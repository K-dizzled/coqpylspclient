from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
file_path = os.path.join("imm/src/basic", "Execution.v")
coq_proj_root = "imm"
# file_path = os.path.join("tests/resources", "aux.v")
# coq_proj_root = "tests/resources"
# file_path = os.path.join("../../EGG/coqPractice/lf_2/", "Induction.v")

pv = ProofView(file_path, coq_proj_root)

# all_thrs = pv.all_theorem_names()
# print(all_thrs)

pr = pv.get_proof_by_theorem("sb_same_loc_trans")
print(pr.proof)


pv.exit()