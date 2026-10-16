# IntegralResiduePullComparisons and residueExchange interfaces

## Reason

The remaining projection-normalization theorem must use the actual comparison interface,
while the main existence theorem uses that normalization. Extract the existing interface
into `Sheaf.Paper.IntegralResidueComparisonInterface` to keep these proof dependencies acyclic.
The main module publicly imports it, preserving every existing declaration, signature,
visibility, body, and global attribute. No target statement or definition meaning changes.
The added `residueExchangeCoefficient` is only an abbreviation for the existing explicitly
constructed restricted regular residue module in degree zero; it chooses no data.
Two proved constructions also expose the
actual derived reduction/restriction adjunction and its comparison of composite right
adjoints, `IntegralResiduePullComparisons.restrictPushIso`. They are used explicitly in
the new normalization statement and the main proof's target isomorphism. These helpers
construct the actual adjunctions and conjugate the given pull isomorphism; they introduce
no axiom or chosen witness of an unproved existence statement.

## Old

In `Sheaf.Paper.IntegralResidueComparisons`, the following block precedes
`integralResidue_comparisons` verbatim:

```lean
/-- Ambient derived category used by the coefficient-comparison interface. -/
abbrev residueExchangeDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))

/-- Derived pullback with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeUpperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ Y ⥤ residueExchangeDerived Λ X :=
  L((f)^*⟦Λ⟧)

/-- Derived direct image with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeLowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ X ⥤ residueExchangeDerived Λ Y :=
  R((f)_*⟦Λ⟧)

/-- The actual derived adjunction, expressed through the typed functor interface. -/
@[irreducible] noncomputable def residueExchangeAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar Λ f ⊣ residueExchangeLowerStar Λ f :=
  by
    unfold residueExchangeUpperStar residueExchangeLowerStar
    exact derivedUpperStarLowerStarAdjunction Λ f

/-- The actual derived coefficient reduction with its two categories exposed. -/
@[irreducible] noncomputable def residueExchangeReduction (X : Scheme.{u}) :
    residueExchangeDerived (integralCoeff ℓ E) X ⥤
      residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X :=
  integralReduction ℓ E X

/-- The library's canonical composition comparison, with typed pull functors. -/
@[irreducible] noncomputable def residueExchangeUpperStarComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    residueExchangeUpperStar Λ (f ≫ g) ≅
      residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f :=
  by
    unfold residueExchangeUpperStar
    exact leftDerivedUpperStarComp Λ f g

/-- Pullback comparisons for actual derived reduction, compatible with composition.
The data concern arbitrary schemes and morphisms, without constructibility or base change.
Source: Bhatt--Scholze, Remark 6.8.15, and associativity of derived tensor.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
structure IntegralResiduePullComparisons where
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ≅
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f
  comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Z))),
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app K) ≫
        (pull f).hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
        (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((pull g).hom.app K) =
      (pull (f ≫ g)).hom.app K ≫
        (residueExchangeUpperStarComp
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app
            ((residueExchangeReduction ℓ E Z).obj K)

namespace IntegralResiduePullComparisons

variable {ℓ E} (c : IntegralResiduePullComparisons.{u} ℓ E)

/-- The direct-image comparison is the adjunction mate of the inverse pull comparison.
This is an actual construction; no direct-image isomorphism is chosen.
Source: Bhatt--Scholze, Lemma 6.5.9(3), projection comparison by adjunction.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
noncomputable def push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeLowerStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E Y ⟶
      residueExchangeReduction ℓ E X ⋙
        residueExchangeLowerStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  (mateEquiv (residueExchangeAdjunction (integralCoeff ℓ E) f)
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
      (TwoSquare.mk _ _ _ _ (c.pull f).inv)).natTrans

/-- The defining counit equation for the actual direct-image comparison.
Source: Mathlib, mateEquiv_counit.
(blueprint: lem-weil-pbc-integral-residue-push-counit)
Proof. Apply the counit identity of the mates equivalence to the inverse pull comparison.
-/
theorem push_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((c.push f).app K) ≫
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).counit.app
        ((residueExchangeReduction ℓ E X).obj K) =
    (c.pull f).inv.app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeReduction ℓ E X).map
        ((residueExchangeAdjunction (integralCoeff ℓ E) f).counit.app K) := by
  exact mateEquiv_counit (residueExchangeAdjunction (integralCoeff ℓ E) f)
    (residueExchangeAdjunction
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (TwoSquare.mk _ _ _ _ (c.pull f).inv) K

end IntegralResiduePullComparisons

```

## New

The same block, with its namespace and variables preserved, is now in
`Sheaf.Paper.IntegralResidueComparisonInterface`. Its complete declaration block is:

```lean
/-- Ambient derived category used by the coefficient-comparison interface. -/
abbrev residueExchangeDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))

/-- Derived pullback with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeUpperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ Y ⥤ residueExchangeDerived Λ X :=
  L((f)^*⟦Λ⟧)

/-- Derived direct image with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeLowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ X ⥤ residueExchangeDerived Λ Y :=
  R((f)_*⟦Λ⟧)

/-- The actual derived adjunction, expressed through the typed functor interface. -/
@[irreducible] noncomputable def residueExchangeAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar Λ f ⊣ residueExchangeLowerStar Λ f :=
  by
    unfold residueExchangeUpperStar residueExchangeLowerStar
    exact derivedUpperStarLowerStarAdjunction Λ f

/-- The actual derived coefficient reduction with its two categories exposed. -/
@[irreducible] noncomputable def residueExchangeReduction (X : Scheme.{u}) :
    residueExchangeDerived (integralCoeff ℓ E) X ⥤
      residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X :=
  integralReduction ℓ E X

/-- The library's canonical composition comparison, with typed pull functors. -/
@[irreducible] noncomputable def residueExchangeUpperStarComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    residueExchangeUpperStar Λ (f ≫ g) ≅
      residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f :=
  by
    unfold residueExchangeUpperStar
    exact leftDerivedUpperStarComp Λ f g

/-- Pullback comparisons for actual derived reduction, compatible with composition.
The data concern arbitrary schemes and morphisms, without constructibility or base change.
Source: Bhatt--Scholze, Remark 6.8.15, and associativity of derived tensor.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
structure IntegralResiduePullComparisons where
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ≅
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f
  comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Z))),
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app K) ≫
        (pull f).hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
        (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((pull g).hom.app K) =
      (pull (f ≫ g)).hom.app K ≫
        (residueExchangeUpperStarComp
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app
            ((residueExchangeReduction ℓ E Z).obj K)

namespace IntegralResiduePullComparisons

variable {ℓ E} (c : IntegralResiduePullComparisons.{u} ℓ E)

/-- The direct-image comparison is the adjunction mate of the inverse pull comparison.
This is an actual construction; no direct-image isomorphism is chosen.
Source: Bhatt--Scholze, Lemma 6.5.9(3), projection comparison by adjunction.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
noncomputable def push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeLowerStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E Y ⟶
      residueExchangeReduction ℓ E X ⋙
        residueExchangeLowerStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  (mateEquiv (residueExchangeAdjunction (integralCoeff ℓ E) f)
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
      (TwoSquare.mk _ _ _ _ (c.pull f).inv)).natTrans

/-- The defining counit equation for the actual direct-image comparison.
Source: Mathlib, mateEquiv_counit.
(blueprint: lem-weil-pbc-integral-residue-push-counit)
Proof. Apply the counit identity of the mates equivalence to the inverse pull comparison.
-/
theorem push_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((c.push f).app K) ≫
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).counit.app
        ((residueExchangeReduction ℓ E X).obj K) =
    (c.pull f).inv.app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeReduction ℓ E X).map
        ((residueExchangeAdjunction (integralCoeff ℓ E) f).counit.app K) := by
  exact mateEquiv_counit (residueExchangeAdjunction (integralCoeff ℓ E) f)
    (residueExchangeAdjunction
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (TwoSquare.mk _ _ _ _ (c.pull f).inv) K

end IntegralResiduePullComparisons

/-- The actual derived extension/restriction adjunction, with typed reduction. -/
@[irreducible] noncomputable def residueExchangeReductionAdjunction (T : Scheme.{u}) :
    residueExchangeReduction ℓ E T ⊣
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory := by
  unfold residueExchangeReduction integralReduction
  exact Mod.derivedExtendMapDerivedCategoryAdjunction _

namespace IntegralResiduePullComparisons

variable {ℓ E}

/-- Conjugating the pull comparison between composite left adjoints compares the
composite right adjoints. No exactness of extension of scalars is used. -/
@[irreducible] noncomputable def restrictPushIso (c : IntegralResiduePullComparisons.{u} ℓ E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeLowerStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f ⋙
        (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory ⋙
        residueExchangeLowerStar (integralCoeff ℓ E) f :=
  ((residueExchangeReductionAdjunction ℓ E Y).comp
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)).rightAdjointUniq
    (((residueExchangeAdjunction (integralCoeff ℓ E) f).comp
      (residueExchangeReductionAdjunction ℓ E X)).ofNatIsoLeft (c.pull f))

end IntegralResiduePullComparisons

/-- The restricted residue coefficient, viewed in degree zero. -/
noncomputable abbrev residueExchangeCoefficient (T : Scheme.{u}) :
    residueExchangeDerived (integralCoeff ℓ E) T :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
      (Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))
```

The main module publicly imports the interface:

```lean
public import Sheaf.Paper.IntegralResidueComparisonInterface
```

Its proof privately imports the normalization theorem. The braiding API is already
exposed by the original public dependencies, so its redundant direct import was removed.
The original theorem signature is byte-for-byte unchanged. The interface keeps the original public imports of `ContinuousIntegralCoefficients` and
`Adjunction.Mates`; the original public import of `Monoidal.Rigid.Basic` moves to the main
module, where the theorem signature uses `IsDualizable`. All original exports remain
visible through the main module. The normalization statement publicly imports only
`ProjectionMap`; `ProjectionMapDualizable` is a private proof import of the main module.
This is an extraction to share signatures, not a split to evade the compiler time limit.

## Users

`tools/downstream.py Sheaf.Paper.IntegralResidueComparisons --uses residueExchangeDerived`
lists the nine transitive downstream modules. Textual inspection of all moved names
also finds `IntegralResidueExchange` and `IntegralResidueExchangeAlgebra`, included below.
The sole direct importer `BoundedExchangeAmbient` compiles unchanged against the delivered
interface, normalization, and main module. No other module is adapted in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueComparisons | B4 | Identical exports through the main module; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Identical exports through the main module; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Identical exports through the main module; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Identical exports through the main module; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Identical exports through the main module; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Identical exports through the main module; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Identical exports through the main module; no adaptation. |
| TargetsCheck | unclaimed | Identical exports through the main module; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Identical exports through the main module; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Identical exports through the main module; no adaptation. |

## Status

landed 20261016T070240-L-770386 2026-10-16 (merge of deliver/B4/Sheaf.Paper.IntegralResidueComparisons)
