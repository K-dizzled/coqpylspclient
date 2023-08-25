import os
import pytest
import time
import sys

sys.path.append(os.path.abspath('../'))

from ..coqlspclient.proof_view import ProofView
from ..coqlspclient.coq_lsp_structs import *
proof_view: ProofView = None

@pytest.fixture(autouse=True)
def pre_post_process():
    yield
    proof_view.exit()

def test_theorem_fetch_small():
    global proof_view
    file_path = os.path.join("tests/resources", "aux.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    thrs = proof_view.all_theorem_names()

    assert thrs == ["test_thr", "test_thr1"]

def test_theorem_fetch_big():
    global proof_view
    file_path = os.path.join("tests/resources", "test_basic_sf.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    thrs = proof_view.all_theorem_names()
    print(thrs)
    assert len(thrs) == 22
    assert thrs == [
        'plus_O_n', "plus_O_n'", "plus_O_n''", 'plus_1_l', 'mult_0_l', 
        'plus_id_example', 'plus_id_exercise', 'mult_n_0_m_0', 
        'mult_n_1', 'plus_1_neq_0_firsttry', 'plus_1_neq_0', 
        'negb_involutive', 'andb_commutative', "andb_commutative'", 
        'andb3_exchange', 'andb_true_elim2', "plus_1_neq_0'", 
        "andb_commutative''", 'zero_nbeq_plus_1', 'identity_fn_applied_twice', 
        'negation_fn_applied_twice', 'andb_eq_orb'
    ]
    
def test_theorem_get_proof_exception(): 
    global proof_view
    file_path = os.path.join("tests/resources", "aux.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    with pytest.raises(Exception):
        _ = proof_view.get_proof_by_theorem("test_thr2")

def test_theorem_get_proof_empty(): 
    global proof_view
    file_path = os.path.join("tests/resources", "aux.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    proof = proof_view.get_proof_by_theorem("test_thr1")

    assert proof.statement == 'Theorem test_thr1 : forall n:nat, 0 + n + 0 = n.'
    assert proof.proof is not None
    
def test_incomplete_proofs():
    global proof_view
    file_path = os.path.join("tests/resources", "test_incomplete_proofs.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    incomplete_indeces = [2, 3, 4, 5, 6]
    complete_indeces = [1, 8]

    for i in incomplete_indeces:
        proof = proof_view.get_proof_by_theorem(f"test_incomplete_proof{i}")
        assert proof.proof.is_incomplete == True
    
    for i in complete_indeces:
        proof = proof_view.get_proof_by_theorem(f"test_incomplete_proof{i}")
        assert proof.proof.is_incomplete == False

def test_theorem_get_proof():
    global proof_view
    file_path = os.path.join("tests/resources", "aux.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    proof = proof_view.get_proof_by_theorem("test_thr")

    assert proof.statement == 'Theorem test_thr : forall n:nat, 0 + n = n.'
    assert len(proof.proof.proof_steps) == 6
    assert proof.proof.proof_steps[3].text == "simpl."
    assert proof.proof.proof_steps[3].focused_goal.ty == "n = n"
    assert len(proof.proof.proof_steps[3].focused_goal.hyps) == 1
    assert proof.proof.proof_steps[3].focused_goal.hyps[0].names[0] == "n"

def test_parse_file_small(): 
    global proof_view
    file_path = os.path.join("tests/resources", "aux.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    theorems = proof_view.parse_file()

    assert len(theorems) == 2
    assert len(list(filter(lambda th: (th.proof is not None), theorems))) == 2

def test_check_proofs_simple(): 
    global proof_view
    file_path = os.path.join("tests/resources", "aux.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    preceding_context = ""
    thr_statement = "Theorem plus_O_n'' : forall n:nat, 0 + n = n."
    proofs = [
        "Proof. intros n. Qed.",
        "Proof. kek. Qed.",
        "Proof. lol. Qed.",
        "Proof. assumption. Qed.",
        "Proof. reflexivity. Qed.",
        "Proof. auto. Qed.",
    ]
    answers = [
        (False, " (in proof plus_O_n''): Attempt to save an incomplete proof"),
        (False, "The reference kek was not found in the current environment."),
        (False, "The reference lol was not found in the current environment."),
        (False, "No such assumption."),
        (True, None)
    ]
    res = proof_view.check_proofs(preceding_context, thr_statement, proofs)
    
    for (r, a) in zip(res, answers): 
        assert r[0] == a[0]
        assert r[1] == a[1]
        
def test_check_proofs_normal(): 
    global proof_view
    file_path = os.path.join("tests/resources", "test_basic_sf.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    preceding_context = ""
    thr_statement = "Theorem test_thr1 : forall n:nat, 0 + n + 0 = n."
    proofs = [
        "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed.",
        "Proof.\nintros n.\nsimpl.\nPrint plus.\nrewrite plus_0_r.\nreflexivity.\nQed.",
        "Proof.\nintros n.\nrewrite plus_0_r.\nrewrite plus_0_l.\nreflexivity.\nQed.",
        "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed.",
        "Proof.\nintros n.\nrewrite <- plus_n_O.\nrewrite <- plus_n_O at 1.\nreflexivity.\nQed.",
        "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed.",
        "Proof.\nintros n.\nPrint plus.\nsimpl.\nrewrite <- plus_n_O.\nreflexivity.\nQed."
    ]
    answers = [
        (False, "The variable plus_0_r was not found in the current environment."),
        (False, "The variable plus_0_r was not found in the current environment."),
        (False, "The variable plus_0_r was not found in the current environment."),
        (False, "The variable plus_0_r was not found in the current environment."),
        (False, 'Found no subterm matching "?n + 0" in the current goal.'),
        (False, "The variable plus_0_r was not found in the current environment."),
        (True, None)
    ]
    # Measure time
    start = time.time()
    res = proof_view.check_proofs(preceding_context, thr_statement, proofs)
    end = time.time()
    time_for_check_proofs_call = end - start

    for (r, a) in zip(res, answers):
        assert r[0] == a[0]
        assert r[1] == a[1]

    # Check that such call is faster than calling chech_proof for each proof separately
    time_for_check_proof_calls = 0
    for i, proof in enumerate(proofs):
        start = time.time()
        res = proof_view.check_proof(thr_statement, proof, preceding_context)
        end = time.time()
        assert res[0] == answers[i][0]
        assert res[1] == answers[i][1]
        time_for_check_proof_calls += end - start
    
    assert time_for_check_proofs_call < time_for_check_proof_calls

def test_parse_file(): 
    global proof_view
    file_path = os.path.join("tests/resources", "test_basic_sf.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    theorems = proof_view.parse_file()

    assert len(theorems) == 22
    assert len(list(filter(lambda th: (th.proof is not None), theorems))) == 22