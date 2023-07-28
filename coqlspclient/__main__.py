from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
# file_path = os.path.join("imm/src/basic", "Execution.v")
# coq_proj_root = "imm"
file_path = os.path.join("tests/resources", "aux.v")
coq_proj_root = "tests/resources"

pv = ProofView(file_path, coq_proj_root)

# st = "Theorem test_thr1 : forall n:nat, 0 + n + 0 = n. Proof."
# proof = "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed."

# print(pv.check_proofs("", st, [proof]))

# all_thrs = pv.all_theorem_names()
# print(all_thrs)

pr = pv.get_proof_by_theorem("test_thr")
print(pr.proof)


pv.exit()