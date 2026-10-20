# AlgebraicGeometry.tensor_model_pushout_base_change

## Reason

Retirement item `Sheaf.RingTheory.TensorModelPushoutBaseChange`, listed in
`coord/retire-items.tsv`, follows the human's retirement instruction recorded in
`coord/changes/retire-sheaf-twins-20261020.md`. The Sheaf copy has no importers and
contains zero holes. The upstream twin proves the stronger result that the later
P-algebra structure is induced from the original one.

## Old

`Sheaf.RingTheory.TensorModelPushoutBaseChange` declared:

```lean
theorem tensor_model_pushout_base_change
    (R : Type u) (S : Type v) (T : Type w) (A : Type x) (B : Type y)
    (P Q : Type z)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [CommRing P] [CommRing Q] [Algebra R S] [Algebra R T]
    [Algebra R A] [Algebra R B] [Algebra P Q]
    (t : S →ₐ[R] T) (f : A →ₐ[R] B) (q : Q →+* S ⊗[R] B)
    (h : let D := S ⊗[R] A
      let E := S ⊗[R] B
      let d : D →+* E :=
        (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
      letI : Algebra D E := d.toAlgebra
      letI : Algebra Q E := q.toAlgebra
      ∃ aP : Algebra P D,
        letI := aP
        letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
        letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
        ∃ hPQ : IsScalarTower P Q E,
          letI := hPQ
          Algebra.IsPushout P D Q E) :
    let D := T ⊗[R] A
    let E := T ⊗[R] B
    let d : D →+* E := (Algebra.TensorProduct.map (AlgHom.id T T) f).toRingHom
    letI : Algebra D E := d.toAlgebra
    letI : Algebra Q E :=
      ((Algebra.TensorProduct.map t (AlgHom.id R B)).toRingHom.comp q).toAlgebra
    ∃ aP : Algebra P D,
      letI := aP
      letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
      letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
      ∃ hPQ : IsScalarTower P Q E,
        letI := hPQ
        Algebra.IsPushout P D Q E
```

## New

Withdraw the Sheaf copy using `deleted.txt`; no declarations remain in that module.
The unchanged upstream module
`WeilConjectures.RingTheory.TensorModelPushoutBaseChange` supplies:

```lean
theorem tensor_model_pushout_base_change
    (R : Type u) (S : Type v) (T : Type w) (A : Type x) (B : Type y)
    (P Q : Type z)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [CommRing P] [CommRing Q] [Algebra R S] [Algebra R T]
    [Algebra R A] [Algebra R B] [Algebra P Q]
    (t : S →ₐ[R] T) (f : A →ₐ[R] B) (q : Q →+* S ⊗[R] B) (aP : Algebra P (S ⊗[R] A))
    (h : let D := S ⊗[R] A
      let E := S ⊗[R] B
      let d : D →+* E :=
        (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
      letI : Algebra D E := d.toAlgebra
      letI : Algebra Q E := q.toAlgebra
      letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
      letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
      ∃ hPQ : IsScalarTower P Q E,
        letI := hPQ
        Algebra.IsPushout P D Q E) :
    let D := T ⊗[R] A
    let E := T ⊗[R] B
    let d : D →+* E := (Algebra.TensorProduct.map (AlgHom.id T T) f).toRingHom
    letI : Algebra D E := d.toAlgebra
    letI : Algebra Q E :=
      ((Algebra.TensorProduct.map t (AlgHom.id R B)).toRingHom.comp q).toAlgebra
    letI : Algebra P D :=
      ((Algebra.TensorProduct.map t (AlgHom.id R A)).toRingHom.comp
        (algebraMap P (S ⊗[R] A))).toAlgebra
    letI : Algebra P E := (d.comp (algebraMap P D)).toAlgebra
    letI : IsScalarTower P D E := .of_algebraMap_eq fun _ ↦ rfl
    ∃ hPQ : IsScalarTower P Q E,
      letI := hPQ
      Algebra.IsPushout P D Q E
```

Repoint `lem-pc-tensor-model-pushout-base-change` to this existing declaration,
with its exact upstream signature. The node's mathematical statement and proof
remain unchanged. Unpack the existential original P-algebra structure, apply the
upstream theorem to that structure, and existentially forget the specified later
structure to recover the previous statement. This implication compiled in
`scratch/Verification.lean` through lcompile.py in 1.5 seconds. Both the upstream
theorem and the compatibility theorem have only propext, Classical.choice and
Quot.sound as axioms. No source-library file or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TensorModelPushoutBaseChange | T4 | Withdraw unused duplicate. |

There are zero direct or transitive importers of the Sheaf module. The only other
occurrences of the theorem name in Lean sources belong to its upstream declaration
and the upstream TensorModelAlgebraDescent consumer, which already imports the
upstream twin and stays unchanged. The only DAG attachment to the Sheaf module is
`lem-pc-tensor-model-pushout-base-change`; it now points to the twin. The unit
`sk-thm-picard-semicon` does not realize any unit statement or proof step with this
node, and its route is preserved.

## Status

landed 20261020T132044-L-1407412 2026-10-20 (merge of deliver/T4/Sheaf.RingTheory.TensorModelPushoutBaseChange)
