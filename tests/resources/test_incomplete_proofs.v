Theorem test_incomplete_proof1 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
  apply H1.
  apply H3.
Qed.

Theorem test_incomplete_proof2 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
Admitted.

Theorem test_incomplete_proof3 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
  Show Proof.
Abort.

Theorem test_incomplete_proof4 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
Admitted. 

Theorem test_incomplete_proof5 : forall x: bool, x = true \/ x = false. 
Proof. 
    destruct x.
    - admit.
    - now right. 
Admitted. 

Theorem test_incomplete_proof6 : forall x: bool, x = true \/ x = false. 
Proof. 
    destruct x.
    - admit.
    - now right. 
Admitted. 

Theorem test_incomplete_proof8 : forall x: bool, x = true \/ x = false.
Proof. 
    destruct x.
    { now left. }
    { now right. }
Qed.
