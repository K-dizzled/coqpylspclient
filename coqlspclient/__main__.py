from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
file_path = os.path.join("tests/resources", "aux.v")

pv = ProofView(file_path)

pr = pv.get_proof_by_theorem("test_thr")
print(pr.proof)

pv.exit()