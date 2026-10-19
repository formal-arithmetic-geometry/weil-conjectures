# IsLisseCoefficientModule, coefficientHeartRingObj, CoefficientHeartStratificationAssertions

## Reason

Move the three unchanged definitions from CoefficientHeartCommonStratification to CoefficientHeartStratificationDefs so the independent clause theorems can use them without importing their assembly theorem. The old module publicly imports the new one. Names, universes, signatures, bodies, and visibility are unchanged. No mathematical definition or target statement changes, so no target meaning changes.

## Old

In `lean/Sheaf/Paper/CoefficientHeartCommonStratification.lean`:

```lean
/-- Lisse means pro-etale locally free of finite rank, with ranks allowed to vary on the
cover. Source: blueprint sk-lem-coefficient-heart, introductory paragraph
(blueprint: det-lem-coefficient-heart-common-stratification). -/
def IsLisseCoefficientModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
    Mod.IsFree (condensedRingObj Λ (U.X i)) ((CondensedRing.upperStar Λ (U.f i)).obj M)

/-- The underlying ring object of a condensed ring, with its canonical multiplication.
Source: blueprint sk-def-sfb-condensed-ring, first paragraph
(blueprint: det-lem-coefficient-heart-common-stratification). -/
abbrev coefficientHeartRingObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ

/-- All three assertions, with exactness of a pair of arbitrary arrows expressed as equality
of its image and kernel subobjects. This also forces their composite to vanish. Longer
sequences are exact precisely when this condition holds at each term.
Source: blueprint sk-lem-coefficient-heart-common-stratification, clauses (1)--(3)
(blueprint: det-lem-coefficient-heart-common-stratification). -/
def CoefficientHeartStratificationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∀ (n : ℕ) (P : Fin n → X.FiniteLocallyClosedStratification),
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (P j).n,
        R.stratum a ⊆ (P j).stratum b) ∧
      (∀ a : Fin R.n, ConnectedSpace (R.domain a)) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)) ∧
  ((∀ (S T : Scheme.{u}) (i : S ⟶ X), IsImmersion i →
      ∀ j : T ⟶ S, IsImmersion j →
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
        IsLisseCoefficientModule Λ M →
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ j).obj M)) ∧
    (∀ (P R : X.FiniteLocallyClosedStratification)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (∀ a : Fin P.n,
        HasFiniteConstantLocalModel Λ (P.domain a)
          ((CondensedRing.upperStar Λ (P.immersion a)).obj M)) →
      (∀ a : Fin R.n, ∃ b : Fin P.n, R.stratum a ⊆ P.stratum b) →
        ∀ a : Fin R.n,
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (R.immersion a)).obj M))) ∧
  (∀ R : X.FiniteLocallyClosedStratification,
    (∀ a : Fin R.n,
      PreservesFiniteLimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      Nonempty (CondensedRing.upperStar Λ (R.immersion a) ⋙
          Mod.forget (condensedRingObj Λ (R.domain a)) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} (R.immersion a))) ∧
    (∀ (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B),
      (Mono f ↔ ∀ a : Fin R.n, Mono ((CondensedRing.upperStar Λ (R.immersion a)).map f)) ∧
      (Epi f ↔ ∀ a : Fin R.n, Epi ((CondensedRing.upperStar Λ (R.immersion a)).map f))) ∧
    ∀ (A B C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B) (g : B ⟶ C),
      imageSubobject f = kernelSubobject g ↔
        ∀ a : Fin R.n,
          imageSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map f) =
            kernelSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map g))
```

## New

The identical declarations, verbatim, in `lean/Sheaf/Paper/CoefficientHeartStratificationDefs.lean`:

```lean
/-- Lisse means pro-etale locally free of finite rank, with ranks allowed to vary on the
cover. Source: blueprint sk-lem-coefficient-heart, introductory paragraph
(blueprint: det-lem-coefficient-heart-common-stratification). -/
def IsLisseCoefficientModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀,
    Mod.IsFree (condensedRingObj Λ (U.X i)) ((CondensedRing.upperStar Λ (U.f i)).obj M)

/-- The underlying ring object of a condensed ring, with its canonical multiplication.
Source: blueprint sk-def-sfb-condensed-ring, first paragraph
(blueprint: det-lem-coefficient-heart-common-stratification). -/
abbrev coefficientHeartRingObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ

/-- All three assertions, with exactness of a pair of arbitrary arrows expressed as equality
of its image and kernel subobjects. This also forces their composite to vanish. Longer
sequences are exact precisely when this condition holds at each term.
Source: blueprint sk-lem-coefficient-heart-common-stratification, clauses (1)--(3)
(blueprint: det-lem-coefficient-heart-common-stratification). -/
def CoefficientHeartStratificationAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∀ (n : ℕ) (P : Fin n → X.FiniteLocallyClosedStratification),
    ∃ R : X.FiniteLocallyClosedStratification,
      (∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (P j).n,
        R.stratum a ⊆ (P j).stratum b) ∧
      (∀ a : Fin R.n, ConnectedSpace (R.domain a)) ∧
      ∀ k : Fin (R.n + 1),
        IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a)) ∧
  ((∀ (S T : Scheme.{u}) (i : S ⟶ X), IsImmersion i →
      ∀ j : T ⟶ S, IsImmersion j →
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
        IsLisseCoefficientModule Λ M →
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ j).obj M)) ∧
    (∀ (P R : X.FiniteLocallyClosedStratification)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (∀ a : Fin P.n,
        HasFiniteConstantLocalModel Λ (P.domain a)
          ((CondensedRing.upperStar Λ (P.immersion a)).obj M)) →
      (∀ a : Fin R.n, ∃ b : Fin P.n, R.stratum a ⊆ P.stratum b) →
        ∀ a : Fin R.n,
          IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (R.immersion a)).obj M))) ∧
  (∀ R : X.FiniteLocallyClosedStratification,
    (∀ a : Fin R.n,
      PreservesFiniteLimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      PreservesFiniteColimits (CondensedRing.upperStar Λ (R.immersion a)) ∧
      Nonempty (CondensedRing.upperStar Λ (R.immersion a) ⋙
          Mod.forget (condensedRingObj Λ (R.domain a)) ≅
        Mod.forget (condensedRingObj Λ X) ⋙ upperStar Ab.{u + 1} (R.immersion a))) ∧
    (∀ (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B),
      (Mono f ↔ ∀ a : Fin R.n, Mono ((CondensedRing.upperStar Λ (R.immersion a)).map f)) ∧
      (Epi f ↔ ∀ a : Fin R.n, Epi ((CondensedRing.upperStar Λ (R.immersion a)).map f))) ∧
    ∀ (A B C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (f : A ⟶ B) (g : B ⟶ C),
      imageSubobject f = kernelSubobject g ↔
        ∀ a : Fin R.n,
          imageSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map f) =
            kernelSubobject ((CondensedRing.upperStar Λ (R.immersion a)).map g))
```

The original module adds `public import Sheaf.Paper.CoefficientHeartStratificationDefs`. There is no consumer adaptation.

## Users

Refreshed against the shared source on 2026-10-19: this lists all 23 direct importers
and every module mentioning a relocated declaration, including users through transitive imports.
The holder column marks unchanged consumers without taking or changing their claims.
No consumer is modified, so no forced adaptation of another group's module is proposed.
For every consumer, the original module publicly re-exports the same declarations from the
new definitions module. Their names, universes, binders, bodies and visibility are unchanged;
the declarations moved verbatim. Every existing consumer statement therefore has the same
meaning and elaborated type. The assigned theorem also keeps its original signature.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.CoefficientHeart | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.CoefficientHeartCommonStratification | F2 | Assigned module: definitions relocated and re-exported. |
| Sheaf.Paper.CoefficientHeartFiltration | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.LisseFiniteCoefficientModel | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.LisseFiniteHomLift | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | Unchanged consumer; not adapted | Identical definitions publicly re-exported; no adaptation. |

## Status

landed 20261019T093352-L-2301987 2026-10-19 (merge of deliver/F2/Sheaf.Paper.CoefficientHeartCommonStratification)
