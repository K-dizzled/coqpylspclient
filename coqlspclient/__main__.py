from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
file_path = os.path.join("tests/resources", "test_basic_sf.v")

pv = ProofView(file_path)

pr = pv.get_proof_by_theorem("plus_1_neq_0_firsttry")
print(pr.only_text())

pv.exit()