# AlgebraicGeometry.ProEtale.proper_unbounded_window_iso

## Reason

The item omitted the standing scheme setting inherited from the blueprint unit and its
amplitude theorem. `ProperIndConstructibleUnbounded` and the parent `ProperUnboundedWindow`
already require separated finite-type schemes over a field k of positive characteristic
different from ℓ, and a morphism over k. The source is
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/_section.md`.
This repair restores those hypotheses in both coefficient cases. It does not assert or prove
the previous arbitrary-scheme statement. The full conclusions and dimension bound stay the same.

The downstream DAG-only detail repair preserves the argument and matches the field
setting already explicit in its owning unit sk-lem-proper-unbounded-window-ii.

No target declaration or target-used definition changes. The current main branch has one
external textual consumer, `Sheaf.Paper.ProperUnboundedWindow`; this delivery adapts its two
proof calls to pass the standing field and scheme hypotheses already present there. Its
statements, visibility, definitions and imports are unchanged.
The main parent DAG citer already has the standing setting. The expanded detail citer
`det-proper-unbounded-window-ii-general` omitted it too; its node is repaired in this delivery to match its already-corrected owning
unit. It has no Lean attachment, so there is no Lean adaptation.

## Old

The affected downstream detail node had this statement:

Let $\ell$ be a prime, let $\Qlb$ be a fixed algebraic closure of $\mathbf Q_\ell$, and let $E\subseteq\Qlb$ be a finite extension of $\mathbf Q_\ell$. Let $\Lambda=E$ or $\Qlb$, let $d\in\mathbf Z$, let $X,Y$ be schemes, and let $p\colon X\to Y$ be proper with geometric fibres of dimension $\leq d$. For $(K_\alpha)$ any family in $\Dic(X,\Lambda)$, the map $\bigoplus_\alpha Rp_*K_\alpha\to Rp_*(\bigoplus_\alpha K_\alpha)$
is an isomorphism.

Here coefficients mean the condensed rings [sk-def-sfb-condensed-ring; sk-def-sfb-qlbar-condensed], pulled back to $\Lambda_X$ and $\Lambda_Y$ [sk-def-sfb-pulled-back-coefficients]. The ambient categories are the ordinary unbounded derived categories of module sheaves [sk-def-sfb-derived-categories], and $Rp_*$ is the total derived pushforward of module objects [sk-def-sfb-module-derived-pushpull]. Write $\Cons(X,\Lambda)$ for the constructible module sheaves [sk-def-sfb-constructible], $\IndCons(X,\Lambda)$ for their small filtered colimits in the ambient module-sheaf category, and $\Dic(X,\Lambda)$ for the full subcategory of complexes all of whose cohomology sheaves lie in $\IndCons(X,\Lambda)$. The family is indexed by any small set in the chosen universe [def-weil-size-convention]. Properness, geometric fibres and dimension have the meanings of [def-weil-proper-morphism; def-weil-geometric-fibre; def-kun-topological-krull-dimension]. The comparison is the unique map whose restriction to the $\alpha$-th summand is $Rp_*(\iota_\alpha)$, where $\iota_\alpha:K_\alpha\to\bigoplus_\beta K_\beta$ is the coprojection.

```lean
theorem proper_unbounded_window_iso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K))))

theorem proper_unbounded_window_iso_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K))))
```

## New

The affected downstream detail node now has this statement:

Work in the standing scheme setting of [sk-def-sfb-dc-setting], inherited through [sk-lem-proper-unbounded-window]: $X,Y$ are separated finite-type schemes over a field $k$ of characteristic $p_0>0$ different from $\ell$, and $p$ is a $k$-morphism. Let $\ell$ be a prime, let $\Qlb$ be a fixed algebraic closure of $\mathbf Q_\ell$, and let $E\subseteq\Qlb$ be a finite extension of $\mathbf Q_\ell$. Let $\Lambda=E$ or $\Qlb$, let $d\in\mathbf Z$, let $X,Y$ be schemes, and let $p\colon X\to Y$ be proper with geometric fibres of dimension $\leq d$. For $(K_\alpha)$ any family in $\Dic(X,\Lambda)$, the map $\bigoplus_\alpha Rp_*K_\alpha\to Rp_*(\bigoplus_\alpha K_\alpha)$
is an isomorphism.

Here coefficients mean the condensed rings [sk-def-sfb-condensed-ring; sk-def-sfb-qlbar-condensed], pulled back to $\Lambda_X$ and $\Lambda_Y$ [sk-def-sfb-pulled-back-coefficients]. The ambient categories are the ordinary unbounded derived categories of module sheaves [sk-def-sfb-derived-categories], and $Rp_*$ is the total derived pushforward of module objects [sk-def-sfb-module-derived-pushpull]. Write $\Cons(X,\Lambda)$ for the constructible module sheaves [sk-def-sfb-constructible], $\IndCons(X,\Lambda)$ for their small filtered colimits in the ambient module-sheaf category, and $\Dic(X,\Lambda)$ for the full subcategory of complexes all of whose cohomology sheaves lie in $\IndCons(X,\Lambda)$. The family is indexed by any small set in the chosen universe [def-weil-size-convention]. Properness, geometric fibres and dimension have the meanings of [def-weil-proper-morphism; def-weil-geometric-fibre; def-kun-topological-krull-dimension]. The comparison is the unique map whose restriction to the $\alpha$-th summand is $Rp_*(\iota_\alpha)$, where $\iota_\alpha:K_\alpha\to\bigoplus_\beta K_\beta$ is the coprojection.

```lean
theorem proper_unbounded_window_iso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K))))

theorem proper_unbounded_window_iso_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Both theorem statements repaired and proved. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Pass existing field and scheme arguments in both calls; signatures unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| TargetsCheck | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.Statement | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive importer; parent interface unchanged, no use of repaired declarations or adaptation. |

The current `tools/downstream.py` scan reports 220 downstream modules, all listed
above. Only `Sheaf.Paper.ProperUnboundedWindow` mentions either changed declaration.
The adapted parent preserves its interface, so all other transitive consumers require
no adaptation. The earlier two-module downstream inventory was stale.

A fresh full-library search for both theorem names finds the item itself and
`Sheaf.Paper.ProperUnboundedWindow`, at the calls in `properUnboundedWindow` and
`properUnboundedWindow_padicAlgCl`. These are the only external textual uses. The consumer
was unclaimed when checked. The original consumer fails against the repaired item at
lines 142 and 183: the argument `p : X ⟶ Y` is supplied where the new field parameter
`k : Type u` is expected. Both calls now pass `k p₀ hp₀ hpℓ X Y` before `p`; the arguments
are already hypotheses of the consumer theorems. This preserves their full statements.

The source imports expose the standard truncation API instead of the unrelated
homotopy-colimit bundle; the field hypotheses use public finite-type and separatedness
imports. The consumer is compiled in the same delivered set against this interface.

Repair verification on 2026-10-19: the external user above mentions both
`AlgebraicGeometry.ProEtale.proper_unbounded_window_iso` and
`AlgebraicGeometry.ProEtale.proper_unbounded_window_iso_padicAlgCl`, and is explicitly
covered by this Users table for both interface changes. Its sandbox diff from current
main consists of precisely those two argument-list adaptations. The item and this user
compiled together cleanly on the project server.

## Status

landed 20261019T002605-L-2157050 2026-10-19 (merge of deliver/F8/Sheaf.Paper.ProperUnboundedWindowIso)
