from .coq_lsp_client import CoqLspClient
from .coq_lsp_structs import *
from ..pylspclient.lsp_structs import *
from .proof_view import ProofView
from .progress_bar import StdoutProgressBar
import os

# Create an instance of a coq-lsp client and initialize it.
# file_path = os.path.join("coqpylspclient/imm/src/basic", "Execution.v")
# coq_proj_root = "coqpylspclient/imm"
file_path = os.path.join("coqpylspclient/tests/resources", "aux.v")
coq_proj_root = "coqpylspclient/tests/resources"

prog_bar = StdoutProgressBar(
    "pb start",
    "pb end",
    "pb update"
)
pv = ProofView(file_path, coq_proj_root, prog_bar)

# st = "Theorem test_thr1 : forall n:nat, 0 + n + 0 = n. Proof."
# proof = "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed."

# print(pv.check_proofs("", st, [proof]))

all_thrs = pv.all_theorem_names()
# print(all_thrs)

pv.parse_file()

# pr = pv.get_proof_by_theorem("test_thr")
# print([vars(i) for i in pv.ast])


pv.exit()