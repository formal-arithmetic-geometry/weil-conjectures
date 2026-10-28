# Native finite-cocone descent helpers

## Reason

Separate the coefficient comparison and finite-field tensor cocone from actual descent
on common-stage arrows. The assigned theorem is now proved by constructing the descended
functor, its shift structure, its triangulated structure and its normalized transition
map. In addition, exactness and additivity of the existing native sections functor are
proved from the already proved scalar-forgetting and section-module equivalences.

The added records contain ordinary explicit fields. No data definition uses `sorry`.
The large finite-stage normalization equation is a named irreducible proposition, so
its expanded expression is not replicated in every generated structure projection.
This reduced its module's measured compile time from 68 seconds to 20 seconds.
All reducibility attributes added here concern new definitions or are local to proofs.
Every existing public signature, definition body, instance and public import is unchanged.

## Old

There were no declarations with the new names in the three modules below.
`normalizedFunctor_exists` had its existing signature and a whole-proof `sorry`.

## New

`Sheaf.Paper.LocallyFiniteAdicCoefficientPresentations`:

```lean
theorem coefficientPresentations_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsCommMonObj (abRing l X)] :
    ∃ coefficient : ∀ E : Index l (PadicAlgCl l),
      CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E),
      ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
        completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
          (coefficient L).integralMap l X = (coefficient E).integralMap l X
```

`Sheaf.Paper.LocallyFiniteAdicCoefficientSystem`:

```lean
structure CoefficientSystem where
  [commutative : IsCommMonObj (abRing l X)]
  [sectionsAdditive : (sections l X).Additive]
  [sectionsLimits : PreservesFiniteLimits (sections l X)]
  [sectionsColimits : PreservesFiniteColimits (sections l X)]
  coefficient : ∀ E : Index l (PadicAlgCl l),
    CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)
  coefficient_scalar : ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
    completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
      (coefficient L).integralMap l X = (coefficient E).integralMap l X


theorem coefficientSystem_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (CoefficientSystem l X)
```

`Sheaf.Paper.LocallyFiniteAdicFiniteCocone`:

```lean
structure FiniteCoconeData where
  Φ : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E ⥤
      DerivedCategory (ProEtale.AdicSheaf l X)
  [additive : ∀ E, (Φ E).Additive]
  [shift : ∀ E, (Φ E).CommShift ℤ]
  triangulated : ∀ E, (Φ E).IsTriangulated
  ι : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙ Φ L ≅ Φ E
  coherence : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (h' : L ≤ M)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l (PadicAlgCl l) X E),
    (Φ M).map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).assoc
          h h').hom.app K) ≫ (ι (h.trans h')).hom.app K =
      (ι h').hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj K) ≫
          (ι h).hom.app K
  [transitionShift : ∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
    NatTrans.CommShift (ι h).hom ℤ]
  integral : ∀ E : Index l (PadicAlgCl l),
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      Φ E ⋙ (sections l X).mapDerivedCategory ≅
      ObjectProperty.ι (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X) ⋙
        pbcDerivedExtend.{u} ((C.coefficient E).integralMap l X)

/-- The finite-stage completion-map equation, before pair-category descent.
Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
@[irreducible] def FiniteCoconeData.normalized (A : FiniteCoconeData l X C) : Prop :=
  ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    HEq
      ((sections l X).mapDerivedCategory.map
        ((A.ι h).inv.app ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)))
      ((A.integral E).hom.app K ≫
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((C.coefficient L).integralMap l X) ((C.coefficient E).integralMap l X)
          (C.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h)).app K.obj) ≫
        (A.integral L).inv.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
            E L h).obj K))


/-- The finite realization data with its completion-map equation.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-locally-finite-adic-finite-cocone). -/
structure FiniteCocone extends FiniteCoconeData l X C where
  normalization : toFiniteCoconeData.normalized l X C


theorem finiteCocone_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (C : CoefficientSystem l X) :
    letI := C.commutative
    letI := C.sectionsAdditive
    letI := C.sectionsLimits
    letI := C.sectionsColimits
    Nonempty (FiniteCocone l X C)
```

The signature of `normalizedFunctor_exists` is unchanged. Its proof-only imports now
use the finite cocone and the existing common-stage calculus. The section-functor
commutativity, additivity, finite-limit and finite-colimit instances are local values
in the proved `coefficientSystem_exists` theorem; no global instances are installed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocallyFiniteAdicNormalizedFunctor | E7 | Constructs the global functor from the new finite cocone; unchanged public signature. |
| Sheaf.Paper.LocallyFiniteAdicFiniteCocone | E7 (new) | Uses the new coefficient-system record. |
| Sheaf.Paper.LocallyFiniteAdicCoefficientSystem | E7 (new) | Uses the new normalized coefficient-presentation statement. |

These names did not exist on the delivery base; no other existing module mentions or
imports the new modules. No existing consumer adaptation is necessary.

## Status

landed 20261028T020331-L-2496446 2026-10-28 (merge of deliver/E7/Sheaf.Paper.LocallyFiniteAdicNormalizedFunctor)
