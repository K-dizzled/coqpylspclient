from coqlspclient.coq_lsp_client import CoqLspClient
from coqlspclient.coq_lsp_structs import *
from pylspclient.lsp_structs import *
from coqlspclient.proof_view import ProofView
import os

# Create an instance of a coq-lsp client and initialize it.
file_path = os.path.join("tests/resources", "test_basic_sf.v")

pv = ProofView(file_path)

pv.parse_file()

pv.exit()