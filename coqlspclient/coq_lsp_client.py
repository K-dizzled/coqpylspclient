from pylspclient.lsp_client import LspClient
from pylspclient.json_rpc_endpoint import JsonRpcEndpoint
from pylspclient.lsp_endpoint import LspEndpoint
from pylspclient.lsp_structs import *
from coqlspclient.coq_lsp_structs import *
from typing import List
import time
import subprocess

class CoqLspClient(LspClient):
    def __init__(self, root_uri: str) -> None:
        process = subprocess.Popen(
            ["coq-lsp"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            shell=True, 
        )

        json_rpc_endpoint = JsonRpcEndpoint(process.stdin, process.stdout)
        lsp_endpoint = LspEndpoint(json_rpc_endpoint)

        super().__init__(lsp_endpoint)
        self.initialize(
            processId=process.pid,
            rootPath="",
            rootUri=root_uri,
            initializationOptions={
                "max_errors": 120000000,
                "show_coq_info_messages": True,
                "eager_diagnostics": False 
            },
            capabilities={},
            trace="off",
            workspaceFolders=[{'name': 'coq-lsp', 'uri': root_uri}]
        )
        self.initialized()

    def didOpen(self, textDocument: TextDocumentItem) -> None:
        super().didOpen(textDocument)
        timeout = self.lsp_endpoint.timeout
        while timeout > 0:
            if self.lsp_endpoint.completed_operation:
                return
            elif self.lsp_endpoint.shutdown_flag:
                raise ResponseError(ErrorCodes.ServerQuit, "Server quit")
            else:
                time.sleep(0.1)
                timeout -= 0.1

        self.shutdown()
        self.exit()
        raise ResponseError(ErrorCodes.ServerTimeout, "Timeout server response")
    
    def didChange(
        self, 
        textDocument: VersionedTextDocumentIdentifier, 
        contentChanges: List[TextDocumentContentChangeEvent]
    ) -> None:
        super().didChange(textDocument, contentChanges)
        while self.lsp_endpoint.completed_operation != True:
            time.sleep(0.1)

    def proofGoals(
        self, 
        textDocument: TextDocumentIdentifier,
        position: Position
    ) -> None: 
        server_response = self.lsp_endpoint.call_method(
            method_name="proof/goals", 
            textDocument=textDocument, 
            position=position
        )

        textDocument = VersionedTextDocumentIdentifier(**server_response.get("textDocument"))
        position = Position(server_response.get("position")["line"], server_response.get("position")["character"])
        messages = server_response.get("messages")
        
        # As messages is [str] | [Message] we unify it to [Message]
        if len(messages) == 0:
            messages = []
        elif isinstance(messages[0], str):
            messages = [Message(**{"text": message}) for message in messages]
        else: 
            for i, message in enumerate(messages):
                text = message.get("text")
                range = None if message.get("range") is None else Range(**message.get("range"))
                level = message.get("level")
                messages[i] = Message(text=text, range=range, level=level)

        goal_config = None if server_response.get("goals") is None else goal_config_from_lsp_goal_config(
            server_response.get("goals")
        )

        return GoalAnswer(textDocument=textDocument, position=position, messages=messages, goals=goal_config)
    

    def getDocument(
        self, 
        textDocument: TextDocumentIdentifier
    ) -> FlecheDocument:
        """
        The coq/getDocument request returns a serialized version of Fleche's 
        document. It is modelled after LSP's standard textDocument/documentSymbol, 
        but returns instead the full document contents as understood by Flèche.
        """
        server_response = self.lsp_endpoint.call_method(
            method_name="coq/getDocument", 
            textDocument=textDocument
        )

        return fleche_doc_from_lsp(server_response)