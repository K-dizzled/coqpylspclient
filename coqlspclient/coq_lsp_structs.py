from ..pylspclient.lsp_structs import *
from enum import Enum
from typing import List, Tuple, Any, Dict, Optional


class PpFormat(Enum):
    Pp = 'Pp'
    Str = 'Str'

    def __str__(self) -> str:
        return self.value


class GoalRequest:
    def __init__(
        self, 
        textDocument: VersionedTextDocumentIdentifier, 
        position: Position, 
        pp_format: PpFormat
    ) -> None:
        self.textDocument = textDocument
        self.position = position
        self.pp_format = str(pp_format)


class Hyp:
    def __init__(self, names: List[str], ty: str, definition: str = None) -> None:
        self.names = names
        self.ty = ty
        self.definition = definition

    def __str__(self) -> str:
        return f"{', '.join(self.names)} : {self.ty}"


def hyp_from_lsp_hyp(hyp: Dict[str, Any]) -> Hyp:
    return Hyp(
        names=hyp['names'],
        ty=hyp['ty'],
        definition=hyp['def']
    )


class Goal:
    def __init__(self, hyps: List[Hyp], ty: str) -> None:
        self.hyps = hyps
        self.ty = ty


def goal_from_lsp_goal(goal: Dict[str, Any]) -> Goal:
    return Goal(
        hyps=[hyp_from_lsp_hyp(hyp) for hyp in goal['hyps']],
        ty=goal['ty']
    )


class GoalConfig:
    def __init__(
        self, 
        goals: List[Goal], 
        stack: List[Tuple[List[Goal], List[Goal]]],
        shelf: List[Goal], 
        given_up: List[Goal],
        bullet: str = None, 
    ) -> None:
        self.goals = goals
        self.stack = stack
        self.shelf = shelf
        self.given_up = given_up
        self.bullet = bullet


def goal_config_from_lsp_goal_config(goal_config: Dict[str, Any]) -> GoalConfig:
    goals = [goal_from_lsp_goal(goal) for goal in goal_config['goals']]
    stack = [
        (
            [goal_from_lsp_goal(goal) for goal in goals_tuple[0]],
            [goal_from_lsp_goal(goal) for goal in goals_tuple[1]]
        )
        for goals_tuple in goal_config['stack']
    ]
    bullet = None if 'bullet' not in goal_config else goal_config['bullet']
    shelf = [goal_from_lsp_goal(goal) for goal in goal_config['shelf']]
    given_up = [goal_from_lsp_goal(goal) for goal in goal_config['given_up']]
    return GoalConfig(
        goals=goals, stack=stack, shelf=shelf,
        given_up=given_up, bullet=bullet
    )


class Message:
    def __init__(self, text: str, level: int = None, range: Range = None) -> None:
        self.text = text
        self.level = level
        self.range = range


class GoalAnswer:
    def __init__(
        self, 
        textDocument: VersionedTextDocumentIdentifier, 
        position: Position, 
        messages: Any,
        goals: GoalConfig = None, 
        error: str = None, 
        program: Any = None
    ) -> None:
        self.textDocument = textDocument
        self.position = position
        self.messages = messages
        self.goals = goals
        self.error = error
        self.program = program


class Result(object):
    def __init__(self, range: Range, message: str) -> None:
        self.range = range
        self.message = message


class Query(object): 
    def __init__(self, query: str, results: List[Result]) -> None:
        self.query = query
        self.results = results


class ProofStep(object):
    def __init__(self, text: str, goals: List[GoalAnswer], context: Any) -> None: 
        self.text = text
        self.goals = goals
        self.context = context


class Status(Enum):
    Yes = 'Yes'
    Stopped = 'Stopped'
    Failed = 'Failed'

    def __str__(self) -> str:
        return self.value


class CompletionStatus:
    def __init__(self, status: Status, range: Range) -> None:
        self.status = str(status)
        self.range = range


class RangedSpan:
    def __init__(self, range: Range, span: Any = None) -> None:
        self.range = range
        self.span = span


class FlecheDocument:
    def __init__(self, spans: List[RangedSpan], completed: CompletionStatus) -> None:
        self.spans = spans
        self.completed = completed


class LspPesponseErrorCodes(Enum):
    FlescheDocumentParsingError = 1
    AstParsingError = 2


class LspResponseParsingError(Exception):
    def __init__(self, code: LspPesponseErrorCodes, message: str, data: Any = None):
        self.code = code
        self.message = message
        if data:
            self.data = data


def position_from_lsp(position: Dict[str, Any]) -> Position:
    return Position(position['line'], position['character'])


def range_from_lsp(range: Dict[str, Any]) -> Range:
    return Range(
        start=position_from_lsp(range['start']),
        end=position_from_lsp(range['end'])
    )


def fleche_doc_from_lsp(ast: Dict[str, Any]) -> FlecheDocument: 
    if len(ast['completed']['status']) != 1:
        raise LspResponseParsingError(
            code=LspPesponseErrorCodes.FlescheDocumentParsingError,
            message="Expected exactly one completion status"
        )
    
    status = ast['completed']['status'][0]

    completion_status = CompletionStatus(
        status=Status(status),
        range=range_from_lsp(ast['completed']['range'])
    )
    spans = [
        RangedSpan(
            range=range_from_lsp(span['range']),
            span=(None if 'span' not in span else span['span'])
        )
        for span in ast['spans']
    ]
    return FlecheDocument(spans=spans, completed=completion_status)


class Vernacexpr(Enum):
    VernacLoad = 'VernacLoad'
    VernacSyntaxExtension = 'VernacSyntaxExtension'
    VernacOpenCloseScope = 'VernacOpenCloseScope'
    VernacDelimiters = 'VernacDelimiters'
    VernacBindScope = 'VernacBindScope'
    VernacInfix = 'VernacInfix'
    VernacNotation = 'VernacNotation'
    VernacNotationAddFormat = 'VernacNotationAddFormat'
    VernacDefinition = 'VernacDefinition'
    VernacStartTheoremProof = 'VernacStartTheoremProof'
    VernacEndProof = 'VernacEndProof'
    VernacExactProof = 'VernacExactProof'
    VernacAssumption = 'VernacAssumption'
    VernacInductive = 'VernacInductive'
    VernacFixpoint = 'VernacFixpoint'
    VernacCoFixpoint = 'VernacCoFixpoint'
    VernacScheme = 'VernacScheme'
    VernacCombinedScheme = 'VernacCombinedScheme'
    VernacUniverse = 'VernacUniverse'
    VernacConstraint = 'VernacConstraint'
    VernacBeginSection = 'VernacBeginSection'
    VernacEndSegment = 'VernacEndSegment'
    VernacRequire = 'VernacRequire'
    VernacImport = 'VernacImport'
    VernacCanonical = 'VernacCanonical'
    VernacCoercion = 'VernacCoercion'
    VernacIdentityCoercion = 'VernacIdentityCoercion'
    VernacNameSectionHypSet = 'VernacNameSectionHypSet'
    VernacInstance = 'VernacInstance'
    VernacContext = 'VernacContext'
    VernacDeclareInstances = 'VernacDeclareInstances'
    VernacDeclareClass = 'VernacDeclareClass'
    VernacDeclareModule = 'VernacDeclareModule'
    VernacDefineModule = 'VernacDefineModule'
    VernacDeclareModuleType = 'VernacDeclareModuleType'
    VernacInclude = 'VernacInclude'
    VernacSolveExistential = 'VernacSolveExistential'
    VernacAddLoadPath = 'VernacAddLoadPath'
    VernacRemoveLoadPath = 'VernacRemoveLoadPath'
    VernacAddMLPath = 'VernacAddMLPath'
    VernacDeclareMLModule = 'VernacDeclareMLModule'
    VernacChdir = 'VernacChdir'
    VernacWriteState = 'VernacWriteState'
    VernacRestoreState = 'VernacRestoreState'
    VernacResetName = 'VernacResetName'
    VernacResetInitial = 'VernacResetInitial'
    VernacBack = 'VernacBack'
    VernacBackTo = 'VernacBackTo'
    VernacCreateHintDb = 'VernacCreateHintDb'
    VernacRemoveHints = 'VernacRemoveHints'
    VernacHints = 'VernacHints'
    VernacSyntacticDefinition = 'VernacSyntacticDefinition'
    VernacDeclareImplicits = 'VernacDeclareImplicits'
    VernacArguments = 'VernacArguments'
    VernacArgumentsScope = 'VernacArgumentsScope'
    VernacReserve = 'VernacReserve'
    VernacGeneralizable = 'VernacGeneralizable'
    VernacSetOpacity = 'VernacSetOpacity'
    VernacSetStrategy = 'VernacSetStrategy'
    VernacUnsetOption = 'VernacUnsetOption'
    VernacSetOption = 'VernacSetOption'
    VernacAddOption = 'VernacAddOption'
    VernacRemoveOption = 'VernacRemoveOption'
    VernacMemOption = 'VernacMemOption'
    VernacPrintOption = 'VernacPrintOption'
    VernacCheckMayEval = 'VernacCheckMayEval'
    VernacGlobalCheck = 'VernacGlobalCheck'
    VernacDeclareReduction = 'VernacDeclareReduction'
    VernacPrint = 'VernacPrint'
    VernacSearch = 'VernacSearch'
    VernacLocate = 'VernacLocate'
    VernacRegister = 'VernacRegister'
    VernacComments = 'VernacComments'
    VernacAbort = 'VernacAbort'
    VernacAbortAll = 'VernacAbortAll'
    VernacRestart = 'VernacRestart'
    VernacUndo = 'VernacUndo'
    VernacUndoTo = 'VernacUndoTo'
    VernacBacktrack = 'VernacBacktrack'
    VernacFocus = 'VernacFocus'
    VernacUnfocus = 'VernacUnfocus'
    VernacUnfocused = 'VernacUnfocused'
    VernacBullet = 'VernacBullet'
    VernacSubproof = 'VernacSubproof'
    VernacEndSubproof = 'VernacEndSubproof'
    VernacShow = 'VernacShow'
    VernacCheckGuard = 'VernacCheckGuard'
    VernacProof = 'VernacProof'
    VernacProofMode = 'VernacProofMode'
    VernacToplevelControl = 'VernacToplevelControl'
    VernacExtend = 'VernacExtend'

    def __str__(self) -> str:
        return self.value
    

class ProofViewError(Exception):
    def __init__(self, message: str, data: Any = None):
        self.message = message
        if data:
            self.data = data


class ProofStep: 
    def __init__(
        self, 
        text: str, 
        focused_goal: Optional[Goal], 
        vernac_type: Vernacexpr
    ) -> None:
        self.text = text
        self.focused_goal = focused_goal
        self.vernac_type = vernac_type

    def __str__(self) -> str:
        text = self.text
        if self.vernac_type == Vernacexpr.VernacBullet or self.vernac_type == Vernacexpr.VernacEndProof: 
            return text
        
        if self.focused_goal != None: 
            hyps = self.focused_goal.hyps
            if len(hyps) > 0:
                text += '\n(*\n[CONTEXT]\n'
                text += '\n'.join([str(hyp) for hyp in hyps]) + '\n*)'
            else: 
                text += '\n(* [CONTEXT] ' + "{EMPTY CONTEXT} " + '*)'
            text += '\n(* [GOAL] ' + str(self.focused_goal.ty) + ' *)\n'
        else: 
            text += '\n(* [CONTEXT] ' + "{NO CONTEXT} " + '*)'
            text += '\n(* [GOAL] ' + "{NO GOALS} " + '*)\n'
        
        return text
    

class TheoremProof: 
    def __init__(self, proof_steps: List[ProofStep], end_pos: Range) -> None:
        self.proof_steps = proof_steps
        self.end_pos = end_pos

    def __str__(self) -> str:
        text = ''
        for step in self.proof_steps:
            text += str(step) + ('\n' if step.vernac_type != Vernacexpr.VernacBullet else ' ')
        return text
    
    def only_text(self) -> str: 
        text = ''
        for step in self.proof_steps:
            text += step.text + ('\n' if step.vernac_type != Vernacexpr.VernacBullet else ' ')
        return text

class Theorem: 
    def __init__(
        self, 
        name: str,
        statement_range: Range,
        statement: str,
        proof: Optional[TheoremProof] = None
    ) -> None:
        self.statement = statement
        self.proof = proof
        self.name = name
        self.statement_range = statement_range

    def __str__(self) -> str:
        text = self.statement
        if self.proof != None:
            text += '\n' + str(self.proof)
        return text
    
    def only_text(self) -> str:
        text = self.statement
        if self.proof != None:
            text += '\n' + self.proof.only_text()
        return text