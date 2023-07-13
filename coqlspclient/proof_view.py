from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from typing import Dict, Optional, Any, List, Tuple
from pathlib import Path
import uuid
import os
import functools


def silent_exec(fn_name='function', default=None, with_default=False):
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            try:
                return func(*args, **kwargs)
            except Exception:
                if with_default:
                    return default
                
                raise LspResponseParsingError(
                    code=LspPesponseErrorCodes.AstParsingError,
                    message=f"Exception in {fn_name}"
                )
        return wrapper
    return decorator


class ProofView(object): 
    def __init__(self, file_path): 
        path_to_coq_file = Path(file_path)
        parent_dir = path_to_coq_file.parent.absolute()
        parent_dir_uri = f"file://{parent_dir}"
        file_uri = f"file://{file_path}"

        self.coq_lsp_client = CoqLspClient(parent_dir_uri)
        try:
            with open(file_path, 'r') as f:
                self.lines = f.read().split('\n')
                text_doc = TextDocumentItem(file_uri, 'coq', 1, '\n'.join(self.lines))
                self.coq_lsp_client.didOpen(text_doc)
            self.path = file_path
            self.file_uri = file_uri
            self.ast_full = self.coq_lsp_client.getDocument(TextDocumentIdentifier(file_uri))
            self.ast = self.ast_full.spans
            self.inside_proof = False
            self.parsed_thorems = []
        except: 
            self.coq_lsp_client.shutdown()
            self.coq_lsp_client.exit()
            raise Exception("Error initializing proof view")          
            
    @silent_exec(fn_name='get_expr', with_default=True)
    def __get_expr(self, span: Dict[str, Any]) -> Dict[str, Any]:
        return None if span.span is None else span.span['v']['expr']

    @silent_exec(fn_name='get_theorem_name')
    def __get_theorem_name(self, expr: Dict[str, Any]) -> str: 
        return expr[2][0][0][0]['v'][1]
        
    @silent_exec(fn_name='get_vernacexpr', with_default=True)
    def __get_vernacexpr(self, expr: Dict[str, Any]) -> Vernacexpr:
        return Vernacexpr(expr[0])
    
    def __get_text_in_range(
        self, 
        start: Range, 
        end: Range, 
        preserve_line_breaks: bool = False
    ) -> str:
        if start.line == end.line: 
            return self.lines[start.line][start.character:end.character]
        else: 
            text = self.lines[start.line][start.character:]
            for i in range(start.line + 1, end.line):
                if preserve_line_breaks: 
                    text += '\n'
                text += self.lines[i]
            if preserve_line_breaks:
                text += '\n'
            text += self.lines[end.line][:end.character]

            return text

    def __parse_proof(self, span_index: int) -> TheoremProof:
        index = span_index
        proven = False
        proof = []

        while not proven and index < len(self.ast):
            span = self.ast[index]
            vernac_type = self.__get_vernacexpr(self.__get_expr(span))
            if vernac_type == Vernacexpr.VernacEndProof: 
                proof_step =  proof_step = ProofStep(self.__get_text_in_range(span.range.start, span.range.end), None, vernac_type)
                proof.append(proof_step)
                proven = True
            else: 
                goal_ans = self.coq_lsp_client.proofGoals(TextDocumentIdentifier(self.file_uri), span.range.end)
                proof_step_focused_goal = None
                if goal_ans.goals is not None:
                    if len(goal_ans.goals.goals) > 0: 
                        proof_step_focused_goal = goal_ans.goals.goals[0]

                proof_step = ProofStep(
                    self.__get_text_in_range(span.range.start, span.range.end),
                    proof_step_focused_goal,
                    vernac_type
                )

                proof.append(proof_step)
                index += 1

        if not proven: 
            raise ProofViewError("Invalid or incomplete proof.")
        
        proof = TheoremProof(proof)
        
        return proof
    
    def __create_aux_file(self) -> str:
        dir = os.path.dirname(self.path)
        file_name, file_format = os.path.basename(self.path).split('.')
        self.file_name = file_name
        new_file_name_w_ext = file_name + \
            f"new{str(uuid.uuid4()).replace('-', '')}." + file_format
        self.aux_path = os.path.join(dir, new_file_name_w_ext)
        with open(self.aux_path, 'w'):
            pass

    def check_proof(
        self, 
        thr_statement: str, 
        proof: str, 
        preceding_context: str
    ) -> Tuple[bool, Optional[str]]:         
        """
        Checks if the given proof is valid for the given theorem statement.
        Returns a tuple of a boolean and an optional string. The boolean is 
        True if the proof is valid, False otherwise.
        The optional string is None if the proof is valid, otherwise it is a
        string containing the error message.
        """

        def post_proc(): 
            os.remove(self.aux_path)
            self.aux_path = None

        self.__create_aux_file()

        aux_file_text = preceding_context + '\n\n' + thr_statement + '\n' + proof
        with open(self.aux_path, 'w') as f:
            f.write(aux_file_text)

        uri = f"file://{self.aux_path}"
        self.coq_lsp_client.didOpen(TextDocumentItem(uri, 'coq', 1, aux_file_text))

        with open(self.aux_path, 'r') as f:
            self.coq_lsp_client.didOpen(TextDocumentItem(self.aux_path, 'coq', 1, f.read()))
        
        diagnostics = self.coq_lsp_client.lsp_endpoint.diagnostics
        post_proc()

        if uri in diagnostics: 
            new_diags = list(filter(
                lambda diag: diag.range['start']['line'] >= len(preceding_context.split('\n')), 
                diagnostics[uri]
            ))
            error_diags = list(filter(lambda diag: diag.severity == 1, new_diags))
            if len(error_diags) > 0:
                return False, error_diags[0].message
            else: 
                return True, None
            
        raise ProofViewError("Error checking proof. Empty file diagnostics.")
    
    def parse_file(self) -> List[Theorem]:
        """
        Parses the file and returns a list of theorems.
        # Does the same as: 
        # proofs = [pv.get_proof_by_theorem(thm) for thm in pv.all_theorem_names()]
        # but with better performance.
        """
        theorems = []
        for i, span in enumerate(self.ast): 
            try: 
                if self.__get_vernacexpr(self.__get_expr(span)) == Vernacexpr.VernacStartTheoremProof: 
                    thr_statement = self.__get_text_in_range(
                        self.ast[i].range.start, 
                        self.ast[i].range.end, 
                        preserve_line_breaks=True
                    )
                    if i + 1 >= len(self.ast):
                        theorems.append(Theorem(thr_statement, None))
                    elif self.__get_vernacexpr(self.__get_expr(self.ast[i + 1])) != Vernacexpr.VernacProof:
                        theorems.append(Theorem(thr_statement, None))
                    else:
                        proof = self.__parse_proof(i + 1)
                        theorems.append(Theorem(thr_statement, proof))
            except:
                pass

        return theorems

    def get_proof_by_theorem(self, theorem_name: str) -> Optional[Theorem]: 
        """
        Returns the proof of the given theorem name.
        If the theorem is not found, raises an exception.
        If proof is not present, returns None.
        """
        found = False
        span_pos = 0
        for i, span in enumerate(self.ast): 
            try: 
                if self.__get_vernacexpr(self.__get_expr(span)) == Vernacexpr.VernacStartTheoremProof: 
                    if self.__get_theorem_name(self.__get_expr(span)) == theorem_name: 
                        span_pos = i
                        found = True
                        break
            except:
                pass
        
        if not found:
            raise ProofViewError(f"Theorem {theorem_name} not found.")
        
        thr_statement = self.__get_text_in_range(
            self.ast[span_pos].range.start, 
            self.ast[span_pos].range.end, 
            preserve_line_breaks=True
        )

        if span_pos + 1 >= len(self.ast):
            return Theorem(thr_statement, None)
        elif self.__get_vernacexpr(self.__get_expr(self.ast[span_pos + 1])) != Vernacexpr.VernacProof:
            return Theorem(thr_statement, None)

        try: 
            proof = self.__parse_proof(span_pos + 1)
            theorem = Theorem(thr_statement, proof)
            return theorem
        except ProofViewError:
            return None

    def all_theorem_names(self) -> List[str]:
        """
        Returns a list of all theorem names in the file.
        """
        theorem_names = []
        for span in self.ast: 
            try: 
                if self.__get_vernacexpr(self.__get_expr(span)) == Vernacexpr.VernacStartTheoremProof: 
                    theorem_names.append(self.__get_theorem_name(self.__get_expr(span)))
            except:
                pass

        return theorem_names

    def exit(self) -> None:
        self.coq_lsp_client.shutdown()
        self.coq_lsp_client.exit()