from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
file_path = os.path.join("tests/resources", "aux.v")

pv = ProofView(file_path)

stt = "Theorem test_thr' : forall n:nat, 0 + n = n."
proof = "Proof. now intros. Qed."

check = pv.check_proof(stt, proof)

print(check)

pv.exit()