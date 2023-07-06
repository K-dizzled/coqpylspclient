from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from pprint import pprint
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
file_path = os.path.join("imm/src/basic", "Execution.v")
# file_path = os.path.join("tests/resources", "aux.v")

# E_ntid_sb_prcl sb_immediate_adjacent

pv = ProofView(file_path)
# thrs = pv.all_theorem_names()
# print(thrs)
pr = pv.get_proof_by_theorem('sb_immediate_adjacent')
pprint(pr)

pv.exit()