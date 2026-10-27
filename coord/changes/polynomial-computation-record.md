# Algebra.PolynomialHomology.ComputationData

## Reason

The concrete record generated costly recursors, no-confusion declarations and projections:
profiling the original file with its original theorem hole took 29.2 seconds, with individual
kernel checks up to 5.6 seconds. Adding the required proof exceeded the 60-second limit.
Keep the six field types and dependencies identical, but generate the record implementation
once over abstract field types. `ComputationData` specializes that implementation to the
original coordinate, trivial-fibration, resolution, comparison and normalization requirements.
No mathematical condition changes, and no data is selected from an unproved theorem.
The dropped `Sheaf.AlgebraicTopology.TrivialKanFibration` import is replaced with its
Mathlib source, and its reducible alias `SSet.Enhanced.trivialKanFibration` is expanded
verbatim to `SSet.modelCategoryQuillen.I.rlp`. This preserves the meaning and elaborated
requirements of all six fields.
The generic record together with the polynomial-resolution helpers compiled in 13.2 seconds.

## Old

```lean
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Generator coordinates and the canonically normalized derived-colimit computation.
The `Computation` parameter is the already specified general bar comparison; normalization
fixes these comparisons to its projective-resolution roof, with first-vertex bar signs.
Source: Stacks 08PS, 08QI and 08Q9
(blueprint: lem-trf-polynomial-presentation-homology). -/
structure ComputationData {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v}) (C : Computation bar) where
  coordinates : ∀ (Q : SimplicialObject (Category.{u, v} f))
    (T : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T),
    (CommRingCat.ofHom MvPolynomial.C ≫ e.hom = ((diagram f).obj T).left.hom) →
    ∃ i : homSet Q T ≅ fibreProduct Q T E e,
      ∀ x : E, i.hom ≫ coordinateProjection Q T E e x =
        elementEvaluation Q T (e.hom (MvPolynomial.X x))
  trivial : ∀ (Q : SimplicialObject (Category.{u, v} f)),
    SSet.Enhanced.trivialKanFibration (augmentation Q) →
    ∀ T : Category.{u, v} f,
      SSet.Enhanced.trivialKanFibration (toSingleton (homSet Q T))
  resolution : ∀ (Q : SimplicialObject (Category.{u, v} f)),
    SSet.Enhanced.trivialKanFibration (augmentation Q) → IsResolution (Q ⋙ opOp _)
  comparison : ∀ (Q : SimplicialObject (Category.{u, v} f))
    (_hQ : SSet.Enhanced.trivialKanFibration (augmentation Q))
    (R : Type (max (u + 1) v)) [CommRing R],
    evaluationDerived Q R ≅ colimitDerived f bar R
  normalization : ∀ (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.Enhanced.trivialKanFibration (augmentation Q))
    (R : Type (max (u + 1) v)) [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R),
    (comparison Q hQ R).app F = C.comparison F (Q ⋙ opOp _) (resolution Q hQ)
  naturalityResolution : ∀ (Q Q' : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.Enhanced.trivialKanFibration (augmentation Q))
    (hQ' : SSet.Enhanced.trivialKanFibration (augmentation Q')) (h : Q ⟶ Q')
    (R : Type (max (u + 1) v)) [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R),
    resolutionDerivedMap h F ≫ (comparison Q' hQ' R).hom.app F =
      (comparison Q hQ R).hom.app F


```

## New

```lean
set_option genSizeOf false in
set_option genInjectivity false in
/-- Data and their dependent normalization laws, kept abstract for efficient checking.
Source: Stacks 08PS and 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
structure ComputationPackage (Coordinates Trivial Resolution : Prop) (Comparison : Type*)
    (Normalization Naturality : Resolution → Comparison → Prop) where
  coordinates : Coordinates
  trivial : Trivial
  resolution : Resolution
  comparison : Comparison
  normalization : Normalization resolution comparison
  naturalityResolution : Naturality resolution comparison

/-- Generator coordinates and the canonically normalized derived-colimit computation.
The `Computation` parameter is the already specified general bar comparison; normalization
fixes these comparisons to its projective-resolution roof, with first-vertex bar signs.
Source: Stacks 08PS, 08QI and 08Q9
(blueprint: lem-trf-polynomial-presentation-homology). -/
abbrev ComputationData {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v}) (C : Computation bar) :=
  ComputationPackage
    (∀ (Q : SimplicialObject (Category.{u, v} f))
    (T : Category.{u, v} f) (E : Type u)
    (e : CommRingCat.of (MvPolynomial E A) ≅ (rings f).obj T),
    (CommRingCat.ofHom MvPolynomial.C ≫ e.hom = ((diagram f).obj T).left.hom) →
    ∃ i : homSet Q T ≅ fibreProduct Q T E e,
      ∀ x : E, i.hom ≫ coordinateProjection Q T E e x =
        elementEvaluation Q T (e.hom (MvPolynomial.X x)))
    (∀ (Q : SimplicialObject (Category.{u, v} f)),
    SSet.modelCategoryQuillen.I.rlp (augmentation Q) →
    ∀ T : Category.{u, v} f,
      SSet.modelCategoryQuillen.I.rlp (toSingleton (homSet Q T)))
    (∀ (Q : SimplicialObject (Category.{u, v} f)),
    SSet.modelCategoryQuillen.I.rlp (augmentation Q) → IsResolution (Q ⋙ opOp _))
    (∀ (Q : SimplicialObject (Category.{u, v} f))
    (_hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q))
    (R : Type (max (u + 1) v)) [CommRing R],
    evaluationDerived Q R ≅ colimitDerived f bar R)
    (fun resolution comparison ↦ ∀ (Q : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q))
    (R : Type (max (u + 1) v)) [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R),
    (comparison Q hQ R).app F = C.comparison F (Q ⋙ opOp _) (resolution Q hQ))
    (fun _resolution comparison ↦ ∀ (Q Q' : SimplicialObject (Category.{u, v} f))
    (hQ : SSet.modelCategoryQuillen.I.rlp (augmentation Q))
    (hQ' : SSet.modelCategoryQuillen.I.rlp (augmentation Q')) (h : Q ⟶ Q')
    (R : Type (max (u + 1) v)) [CommRing R]
    (F : (Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R),
    resolutionDerivedMap h F ≫ (comparison Q' hQ' R).hom.app F =
      (comparison Q hQ R).hom.app F)

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PolynomialPresentationHomology | V2 | Identical field requirements; proof constructs the specialized generic record. |
| Sheaf.RingTheory.PolynomialSquareBarNaturality | unclaimed | Uses ComputationData with unchanged field requirements; direct Mathlib import and three exact alias expansions preserve the trivial-Kan requirements. |
| Sheaf.RingTheory.CotangentBarTermIdentifications | unclaimed | Downstream with a private import of PolynomialPresentationHomology; no direct use of ComputationData and no change required. |

`tools/downstream.py Sheaf.RingTheory.PolynomialPresentationHomology --uses ComputationData`
now reports two downstream modules (listed above), including the newly added
PolynomialSquareBarNaturality consumer. The earlier zero-user result is superseded. Unfinished DAG parents remain required; none is withdrawn.
This is an implementation repair, so the node statement, unit route and theorem signature stay
unchanged. The public alias-module import is relocated to its consumer as requested by the return. The definitionally equal colimit-functor repair is
documented separately in `polynomial-colimit-functor.md`.

## Status

landed 20261025T005424-L-3486128 2026-10-25 (merge of deliver/V2/Sheaf.RingTheory.PolynomialPresentationHomology)
