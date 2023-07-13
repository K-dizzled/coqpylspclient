Theorem test_thr : forall n:nat, 0 + n = n.
Proof.
    intros n. Print plus.
    simpl. reflexivity.
Qed.

Theorem test_thr1 : forall n:nat, 0 + n + 0 = n.
Admitted.