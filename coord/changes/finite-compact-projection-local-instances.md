# AlgebraicGeometry.Etale.isIso_finiteCompactProjection

## Reason

The static preflight classifies new attribute commands conservatively as an interface
change and requires this record. Every attribute added here is explicitly local to this
module. No public attribute is added. Public declaration signatures, definitions,
notation and public imports are unchanged; proof imports are pruned separately.
No target statement or definition used by a target changes.

The concrete coefficient quotient has two definitionally equal Ring instances: the
direct quotient instance and the projection of its CommRing instance. Matching the
specialized generic helper against the direct quotient instance otherwise unfolds the
derived tensor construction and exceeds the 60-second file limit. Prioritizing the
CommRing projection locally makes those types syntactically identical. Prioritizing
finite noetherianity locally avoids searching through the quotient presentation. Local
irreducibility keeps projection maps abstract during proof elaboration. The completed
file compiles in 8.6 seconds, without warnings.

## Old

The attributes below were absent. The declaration signature was:

```lean
theorem isIso_finiteCompactProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hK : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) X K)
    (_hL : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) Y L)
    (_hTor : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).app K).app L) ∧
    ∀ (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X (Padic.coefficientExtensionRing l E n))
      (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y (Padic.coefficientExtensionRing l E n))
      (wx : Scheme.EtaleOriginWitness X (Padic.coefficientExtensionRing l E n) Kp)
      (wy : Scheme.EtaleOriginWitness Y (Padic.coefficientExtensionRing l E n) Lp)
      (_hx : wx.L.obj ≅ K) (_hy : wy.L.obj ≅ L),
      IsIso (((ProEtale.projectionMapOfCompactification
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).app
        (((ProEtale.finiteCoefficientRealization X
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.asEquivalence.inverse).obj
            Kp.obj)).app
        (((ProEtale.finiteCoefficientRealization Y
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.asEquivalence.inverse).obj
            Lp.obj))
```

## New

The same signature is elaborated with these local commands:

```lean
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 2000] CommRing.toRing
attribute [local irreducible] projectionMapOfCompactification
  ProEtale.projectionMapOfCompactification

theorem isIso_finiteCompactProjection
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hK : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) X K)
    (_hL : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) Y L)
    (_hTor : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).app K).app L) ∧
    ∀ (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X (Padic.coefficientExtensionRing l E n))
      (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y (Padic.coefficientExtensionRing l E n))
      (wx : Scheme.EtaleOriginWitness X (Padic.coefficientExtensionRing l E n) Kp)
      (wy : Scheme.EtaleOriginWitness Y (Padic.coefficientExtensionRing l E n) Lp)
      (_hx : wx.L.obj ≅ K) (_hy : wy.L.obj ≅ L),
      IsIso (((ProEtale.projectionMapOfCompactification
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).app
        (((ProEtale.finiteCoefficientRealization X
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.asEquivalence.inverse).obj
            Kp.obj)).app
        (((ProEtale.finiteCoefficientRealization Y
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.asEquivalence.inverse).obj
            Lp.obj))
```

The Ring presentations are definitionally equal; the text of the signature is unchanged.
The commands are not exported to importers. The public import list is identical.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula | H1 | Local elaboration settings; original public signature retained; proof completed. |

No other module mentions the declaration. Direct importers require no adaptation:
local attributes do not alter their instance priorities or transparency settings.
The source-only declaration-use search finds only the item itself. The requested
downstream.py scan was also started, but it waited in the shared delivery cache for
several minutes and was interrupted; it returned no consumer results. The seven direct
importers found by source search mention no declaration being changed.
No module held by another group is edited.

## Status

landed 20261019T034259-L-416937 2026-10-19 (merge of deliver/H1/Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula)
