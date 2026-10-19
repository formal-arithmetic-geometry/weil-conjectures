# Integral coefficient comparison data: declaration relocation

## Reason

The ring-existence step and its assembly theorem need the same definitions. Relocating the existing definitions prevents an import cycle; no definition body, declaration name, universe or signature changes.

## Old

In Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit:

```lean
/-- The constant set sheaves with finite labels, regarded as presheaves.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbFiniteConstantSets (X : Scheme.{u}) :
    FintypeCat.{u} ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1) :=
  forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1} ⋙
    constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
      sheafToPresheaf _ _

/-- The presheaves represented by the relative finite test schemes, namely the coproducts
of copies of X by `profinite_test_object_functor`.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbFiniteRepresentables (X : Scheme.{u}) :
    FintypeCat.{u} ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1) :=
  FintypeCat.toProfinite ⋙ profiniteToProEtOf X ⋙ uliftYoneda.{u + 1}

/-- The finite quotient at exponent n+1, bundled using its recorded finiteness theorem.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralFiniteLevel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) : FintypeCat.{u} :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  FintypeCat.of (Padic.coefficientExtensionRing l E (n + 1))

/-- The finite quotient tower with exactly the specified reduction maps.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralFiniteTower (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ℕᵒᵖ ⥤ FintypeCat.{u} :=
  Functor.ofOpSequence (fun n ↦
    FintypeCat.homMk (X := sfbIntegralFiniteLevel l E (n + 1))
      (Y := sfbIntegralFiniteLevel l E n) (Padic.coefficientExtensionTransition l E (n + 1)))

/-- The integers with their extending absolute-value topology, bundled as a profinite set.
Source: blueprint main-20261015, integral-limit clause 1; integers-profinite-tower
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralProfinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Profinite.{u} :=
  letI := Padic.coefficientExtensionIntegersTopology l E
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).the project server
  Profinite.of (Padic.coefficientExtensionIntegers l E)

/-- The condensed integer ring, using its actual continuous-function sections.
Source: blueprint main-20261015, integral-limit clauses 2--3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbCondensedIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers l E)) :=
    Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionIntegers l E))
  Mon.mk (Profinite.continuousMapRingObjOfUniverse (Padic.coefficientExtensionIntegers l E))

/-- The existing completed ring sheaf, as an abelian sheaf with its ring-object structure.
Source: blueprint main-20261015, integral-limit clause 3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable abbrev sfbCompletedIntegersAb (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (completedIntegralCoefficientSheafUnrestricted l E X)

/-- The canonical adjunction whose unit specifies sections pulled back from the point.
Source: blueprint main-20261015, integral-limit proof Step 3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralPointAdjunction (X : Scheme.{u}) :
    sfbPullbackFromPoint X ⊣ sfbPullbackFromPointRightAdjoint X :=
  pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The finite-level set representation, including the canonical comparison between
constant ring sheaves and constant set sheaves.
Source: blueprint main-20261015, integral-limit proof Steps 1 and 4
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralFiniteRepresentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) (n : ℕ) :
    (integralCoefficientSheaf l E X n).obj ⋙ forget RingCat.{u + 1} ≅
      uliftYoneda.{u + 1}.obj
        ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (sfbIntegralFiniteLevel l E n))) :=
  (sheafToPresheaf _ _).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    a.app (sfbIntegralFiniteLevel l E n)

```

## New

The identical declarations and bodies above now occur in Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientData. The original module publicly imports it; its five original public imports are public imports of the data module. All consumers retain exactly the same declarations and definitions.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.CartesianCoefficientTwists | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.FiniteConstantModelResolution | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralCriterionReductions | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralProperBaseChange | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralProperDirectSums | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralStratumHomFormula | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.IntegralTensorPullback | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.InternalHomDualConstructibleModels | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.ProEtaleTateTwists | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.SmoothPurityCoefficientTowers | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.Paper.TateTwistLocallyFree | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.SixFunctors.IntegralLisseReductionEquivalence | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | Not adapted | Declaration names, types, bodies and public reachability unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not adapted | Declaration names, types, bodies and public reachability unchanged. |

The retained source-only import inventory was rechecked with tools/downstream.py on this resumption: 669 modules are downstream; sfbFiniteConstantSets is used by the original module and ProEtaleCoefficientComparisonsPullback. The nine definition texts are byte-identical to the current source, and their original public reachability is preserved. The table lists direct importers and modules that use the moved declarations; none is edited. No consumer adaptation is necessary. The target meanings are unchanged because all definition bodies are identical; this relocation alone changes none of their mathematics.

## Status

landed 20261019T231114-L-548537 2026-10-19 (merge of deliver/D9/Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit)
