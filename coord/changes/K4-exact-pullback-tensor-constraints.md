# SheafOfModules.ExactPullbackSigned.TensorConstraints

## Reason

K4 proves the module's main theorem. In the complete original file, the generated
eliminators repeatedly typecheck its large model equations and the file exceeds
the 60-second compile limit. Naming those two unchanged predicates keeps the
structure's generated declarations compact. Their bodies are the original field
types verbatim. No hypothesis, normalization, witness, data or mathematical
meaning changes; field applications retain definitionally equal types.

Source and target sheaf-composition instances are cached locally at high priority, with no new
hypotheses. The native cochain tensor dictionaries are selected locally to reconcile the
published total tensor with the monoidal model API. Public imports and the
main theorem's written statement are unchanged. No adopted source file changes.

`tensorMap` also becomes a definition with the same body and an explicit result
type, allowing it to stay folded locally. Its carrier and action are unchanged.
No external module mentions this namespace; no consumer adaptation is required.

## Old

In the original section-variable context:

```lean
abbrev tensorMap {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B') :=
  (Functor.uncurry.obj (derivedTensor R)).map (Prod.mkHom a b)


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

In the same section-variable context:

```lean
def tensorMap {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B') :
    tensor R A B ⟶ tensor R A' B' :=
  (Functor.uncurry.obj (derivedTensor R)).map (Prod.mkHom a b)


def IsSymmetryModel
    (sigma : ∀ A B : DerivedCategory (Modules R), tensor R A B ≅ tensor R B A) : Prop :=
  ∀ (P Q : CochainComplex (Modules R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hg : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
    (representativeIso R P Q hp hq hf hg).hom ≫
        (sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (representativeIso R Q P hq hp hg hf).hom

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- The prescribed reassociation equation on resolving total-complex representatives.
Source: Stacks 07A4 (blueprint: lem-pur-exact-pullback-signed-comparison). -/
def IsAssociativityModel
    (alpha : ∀ A B N : DerivedCategory (Modules R),
      tensor R (tensor R A B) N ≅ tensor R A (tensor R B N)) : Prop :=
  ∀ (P Q N : CochainComplex (Modules R) ℤ)
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

set_option genSizeOf false in
set_option genCtorIdx false in
set_option genInjectivity false in
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Natural derived reassociation and symmetry, fixed by their total-complex models.
The equations use the actual unsigned cochain associator and Koszul braiding.
Thus these are the prescribed constraints of the existing tensor, not arbitrary maps.
Source: Stacks 07A4 and more-algebra.tex, 0FNG
(blueprint: lem-pur-exact-pullback-signed-comparison). -/
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
  sigma_model : IsSymmetryModel R sigma
  alpha_model : IsAssociativityModel R alpha
```

## Users

`tools/downstream.py ... --uses` for both
`SheafOfModules.ExactPullbackSigned.TensorConstraints` and
`SheafOfModules.ExactPullbackSigned.tensorMap` finds only this module using the
declarations. The downstream modules import
it transitively but do not mention this structure or any declaration in its
namespace. No consumer requires adaptation. All old fields remain present.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ExactPullbackSignedComparison | K4 | Own item; fields have definitionally identical named predicates; complete proof added. |

## Status

landed 20261024T204627-L-3809502 2026-10-24 (merge of deliver/K4/Sheaf.Algebra.Homology.ExactPullbackSignedComparison)
