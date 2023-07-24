# coqpylspclient
[Coq-lsp](https://github.com/ejgallego/coq-lsp) client implementation in Python.

Package provides a partially implemented client for the coq-lsp server, as well as a wrapper around the client, that provides a useful interface for interacting with the server.

## How to use: 
```python
from coqlspclient.proof_view import ProofView

# Create an instance of a coq-lsp client and initialize it.
root_path = "tests/resources" 
file_path = os.path.join("tests/resources", "aux.v")
pv = ProofView(file_path, root_path)

# Get a list of theorems in the file. 
theorems = pv.all_theorem_names()

# Get a theorem by name.
theorem = pv.get_proof_by_theorem("test_thr")

# It returns a `Theorem` object, which contains the theorem's
# statement as present in the file, as well as its proof, 
# augmented with the information about the proof steps. E.g. 
# the hyps and the conclusion of the focused goal at each step.

# Get proofs of all the theorems in the file.
proofs = pv.parse_file()

# Does the same as: 
proofs = [pv.get_proof_by_theorem(thm) for thm in pv.all_theorem_names()]
# but with better performance.

# Try to check the proof for a given theorem.
# preceding_context is a string containing the context preceding
# the proof. If you want to check the proof in top of the file,
# which ProofView was initialized with, then pass 
# preceding_context = '\n'.join(pv.lines)
stt = "Theorem test_thr' : forall n:nat, 0 + n = n."
proof = "Proof. now intros. Qed."
preceding_context = ""

check = pv.check_proof(stt, proof, preceding_context)

# Close the connection to the server.
pv.exit()
```

## To run the tests

```
python setup.py test
```
