# SheafOfModules.ExactPullbackSigned.TensorConstraints

## Reason

The original expanded proof-field telescopes repeatedly unfold the coproduct
construction of the cochain total tensor. Profiling found about 27 seconds in
checking the original record and generated recursors. Name its four proof
conditions as transparent predicates, and express the associativity model using
the existing bundled resolving models and their pair representative maps. The
six-field record, its two isomorphism families, and its mathematical conditions
are retained. The `alpha_model` interface now takes three bundled models instead
of separately quantified complexes, six proofs, and four existential proofs.
This is a definition/API repair for compilation, not a proof split.

`TensorSymmetryNatural`, `TensorAssociativityNatural`, and `TensorSymmetryModel`
are verbatim copies of the former field types. The fourth predicate is equivalent
to the former associativity field: a model consists exactly of a complex, its
K-flatness proof, and its degreewise flatness proof. `totalModel` constructs the
actual native tensor complex and supplies its resolving proofs. These proofs
are propositions, so any other witnesses in the old existential give the same
representative maps by proof irrelevance. Unfolding `leftRepresentative` and
`rightRepresentative` gives precisely the old outer representative followed by
the inner tensor of representative maps. The original raw total and the native
tensor object agree definitionally (`total_eq`). `constraintsTensor_map` proves
that the two functor presentations have the same map on a pair. No condition is
added or dropped, and neither tensor nor representative is changed.

A separate Lean check proved both implications, using the body printed below,
in 23.9 seconds in a standalone diagnostic. This validates the repair; it is not a new dependency.
The definitions `tensor`, `tensorMap`, `tensorShift`, `exactDerivedFunctor`,
`exactFactorization`, and `IsNormalizedIdentification`, and the complete theorem
statement, are byte-identical to the original declarations. The statement's
meaning must be independently reviewed because its `TensorConstraints` definition
is repackaged. No declaration of `Challenge.lean` or adopted source module changes.

The three proved public cache lemmas below reuse the existing propositional
`HasTensor`, `HasGoodTensor₁₂`, and `HasGoodTensor₂₃` instances. They carry no new
data and are instances only locally. They are public because public definitions
must not contain private helpers. The new public import of
`DerivedTensorAdditiveConstraints` exposes the existing model and representative
names used by the new predicate; it was initially a proof import.

The existing general sheaf-composition instance is erased only within the proof
section; the small-site instances suffice. A focused context profile improved
from 27.9 seconds to 2.6 seconds. The local `implicit_reducible` attribute on
`Functor.map₂HomologicalComplex` exposes its object formula when checking dependent
tensor types. Both settings are restored when the section ends. Private generic
category calculations avoid repeating concrete tensor computations. All proofs
remain in the original module; no file or proof was split to meet the limit.

## Old

```lean
structure TensorConstraints where
  sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A
  sigma_natural : ∀ {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B'),
    tensorMap R a b ≫ (sigma A' B').hom = (sigma A B).hom ≫ tensorMap R b a
  alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)
  alpha_natural : ∀ {A A' B B' N N' : DerivedCategory (Modules R)}
    (a : A ⟶ A') (b : B ⟶ B') (n : N ⟶ N'),
    tensorMap R (tensorMap R a b) n ≫ (alpha A' B' N').hom =
      (alpha A B N).hom ≫ tensorMap R a (tensorMap R b n)
  sigma_model : ∀ (P Q : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    (representativeIso R P Q hp hq hf hg).hom ≫
        (sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (representativeIso R Q P hq hp hg hf).hom
  alpha_model : ∀ (P Q N : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hn : N.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n))
    (hi : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (N.X n)),
    ∃ (hpq : CochainComplex.IsKFlatIndependentCoefficients (((totalTensor R).obj P).obj Q))
      (hqn : CochainComplex.IsKFlatIndependentCoefficients (((totalTensor R).obj Q).obj N))
      (hfpq : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
        ((((totalTensor R).obj P).obj Q).X n))
      (hfqn : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R)
        ((((totalTensor R).obj Q).obj N).X n)),
      (representativeIso R (((totalTensor R).obj P).obj Q) N hpq hn hfpq hi).hom ≫
          tensorMap R (representativeIso R P Q hp hq hf hg).hom (𝟙 _) ≫
          (alpha (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
            (DerivedCategory.Q.obj N)).hom =
        DerivedCategory.Q.map (HomologicalComplex.associator P Q N).hom ≫
          (representativeIso R P (((totalTensor R).obj Q).obj N) hp hqn hf hfqn).hom ≫
          tensorMap R (𝟙 _) (representativeIso R Q N hq hn hg hi).hom
```

## New

```lean
omit [HasDerivedCategory (Modules R)] in
/-- The existing total-tensor existence proof, cached before the public model predicates.
Use the canonical coproduct-totalization instance; the class is a proposition.
Source: Stacks 06YM and 07A2
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
theorem cochainHasTensor (P Q : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasTensor P Q := by infer_instance

omit [HasDerivedCategory (Modules R)] in
/-- The existing first-parenthesization totalization proof, cached for the model predicates.
Use the canonical coproduct-totalization instance; the class is a proposition.
Source: Stacks 06YM and 07A2
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
theorem cochainGood12 (P Q N : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasGoodTensor₁₂ P Q N := by infer_instance

omit [HasDerivedCategory (Modules R)] in
/-- The existing second-parenthesization totalization proof, cached for the model predicates.
Use the canonical coproduct-totalization instance; the class is a proposition.
Source: Stacks 06YM and 07A2
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
theorem cochainGood23 (P Q N : CochainComplex (Modules R) ℤ) :
    HomologicalComplex.HasGoodTensor₂₃ P Q N := by infer_instance

attribute [local instance 2000] cochainHasTensor cochainGood12 cochainGood23


/-- Naturality of the symmetry of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorSymmetryNatural
    (sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A) : Prop :=
  ∀ {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B'),
    tensorMap R a b ≫ (sigma A' B').hom = (sigma A B).hom ≫ tensorMap R b a

/-- Naturality of reassociation of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorAssociativityNatural (alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)) : Prop :=
  ∀ {A A' B B' N N' : DerivedCategory (Modules R)}
    (a : A ⟶ A') (b : B ⟶ B') (n : N ⟶ N'),
    tensorMap R (tensorMap R a b) n ≫ (alpha A' B' N').hom =
      (alpha A B N).hom ≫ tensorMap R a (tensorMap R b n)

/-- The resolving-model equation for symmetry of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorSymmetryModel
    (sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A) : Prop :=
  ∀ (P Q : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    (representativeIso R P Q hp hq hf hg).hom ≫
        (sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (representativeIso R Q P hq hp hg hf).hom

/-- The resolving-model equation for reassociation of `TensorConstraints`.
Source: Stacks 07A4 and 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
def TensorAssociativityModel (alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)) : Prop :=
  ∀ p q n : DerivedTensorConstraints.Model R,
    (DerivedTensorConstraints.representative R
      (DerivedTensorConstraints.totalModel R p q) n).hom ≫
        tensorMap R (DerivedTensorConstraints.representative R p q).hom (𝟙 _) ≫
        (alpha (DerivedCategory.Q.obj p.obj) (DerivedCategory.Q.obj q.obj)
          (DerivedCategory.Q.obj n.obj)).hom =
      DerivedCategory.Q.map (HomologicalComplex.associator p.obj q.obj n.obj).hom ≫
        (DerivedTensorConstraints.representative R p
          (DerivedTensorConstraints.totalModel R q n)).hom ≫
        tensorMap R (𝟙 _) (DerivedTensorConstraints.representative R q n).hom

set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
/-- Natural derived reassociation and symmetry, fixed by their total-complex models.
The equations use the actual unsigned cochain associator and Koszul braiding.
Thus these are the prescribed constraints of the existing tensor, not arbitrary maps.
Source: Stacks 07A4 and more-algebra.tex, 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
structure TensorConstraints where
  sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A
  sigma_natural : TensorSymmetryNatural R sigma
  alpha : ∀ A B N : DerivedCategory (Modules R),
    tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)
  alpha_natural : TensorAssociativityNatural R alpha
  sigma_model : TensorSymmetryModel R sigma
  alpha_model : TensorAssociativityModel R alpha
```

The checked equivalence proof (with `OldAlpha` the old associativity field and
`TensorAssociativityModel` the new definition, in the module's site context) is:

```lean
private theorem alpha_equivalence
    (alpha : ∀ A B N : DerivedCategory (Modules R),
      tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)) :
    OldAlpha R alpha ↔ TensorAssociativityModel R alpha := by
  constructor
  · intro h p q n
    obtain ⟨hpq, hqn, hfpq, hfqn, h⟩ := h p.obj q.obj n.obj
      p.property.1 q.property.1 n.property.1 p.property.2 q.property.2 n.property.2
    unfold DerivedTensorConstraints.representative
    convert h using 1 <;> rfl
  · intro h P Q N hp hq hn hf hg hi
    let p : DerivedTensorConstraints.Model R := ⟨P, hp, hf⟩
    let q : DerivedTensorConstraints.Model R := ⟨Q, hq, hg⟩
    let n : DerivedTensorConstraints.Model R := ⟨N, hn, hi⟩
    have hpq := (DerivedTensorConstraints.totalModel R p q).property
    have hqn := (DerivedTensorConstraints.totalModel R q n).property
    refine ⟨hpq.1, hqn.1, hpq.2, hqn.2, ?_⟩
    have hh := h p q n
    unfold DerivedTensorConstraints.representative at hh
    convert hh using 1 <;> rfl
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ExactPullbackSignedComparison | X8 | Constructs the same normalized constraints through the bundled associativity interface; all private consumers are adapted. |

`tools/downstream.py Sheaf.Algebra.Homology.ExactPullbackSignedComparison --uses
TensorConstraints TensorAssociativityModel` reports zero downstream modules.
No other Lean file requires adaptation. DAG parents and the blueprint unit are
retained; this is no withdrawal or change to their mathematical assertions.

## Status

landed 20261022T020124-L-42603 2026-10-22 (merge of deliver/X8/Sheaf.Algebra.Homology.ExactPullbackSignedComparison)
