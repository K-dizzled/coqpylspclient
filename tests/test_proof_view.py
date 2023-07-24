from coqlspclient.proof_view import ProofView
import os
import pytest
from coqlspclient.coq_lsp_structs import *

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

def test_parse_file(): 
    global proof_view
    file_path = os.path.join("tests/resources", "test_basic_sf.v")
    root_path = "tests/resources"
    proof_view = ProofView(file_path, root_path)
    theorems = proof_view.parse_file()

    assert len(theorems) == 22
    assert len(list(filter(lambda th: (th.proof is not None), theorems))) == 22