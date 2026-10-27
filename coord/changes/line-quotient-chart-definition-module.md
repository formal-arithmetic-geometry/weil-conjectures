# Normalized line-quotient chart definitions

## Reason

The original module contains seven shared definitions and its inverse theorem. Separate
chart lemmas need these definitions, while the inverse theorem imports those chart lemmas.
Moving the definitions to a publicly re-exported module avoids an import cycle.
No declaration signature or definition body changes. These definitions remain in the
targets' dependency closure, but their mathematical data and predicates are byte-for-byte
unchanged (apart from their blueprint docstring references). The targets therefore have
identical meaning; the independent reader can verify the relocation without reopening a
mathematical statement correction. No adopted-source module is changed.

## Old

The following declarations are in
`Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback`:

```lean
/-- Pull back the quotient using the section-normalized composite-pullback comparison.
Source: Stacks, Constructions, Tag 01OA
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
noncomputable def lineQuotientPullback {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L) :
    (tensorPullback (u ≫ h)).obj E ⟶ (tensorPullback u).obj L :=
  (tensorPullbackSectionComp u h).hom.app E ≫ (tensorPullback u).map q

/-- The normalized tautological section associated with a degree-one generator.
The datum's chart equation identifies this section with iota(m)/1 in the twist.
Source: Stacks, Constructions, Tags 01OA and 01O4
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
noncomputable def tautologicalGenerator {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (U : S.affineOpens)
    (m : Γ(E, U.1)) :
    Γ(D.line, (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1) :=
  ((tensorPullbackSectionAdjunction
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E D.line
      D.quotient).app U.1 m

/-- The actual pullback of the normalized degree-one tautological section, restricted
onto an arbitrary open. This is the pulled frame e on a generator chart.
Source: Stacks, Constructions, Tag 01OA
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
noncomputable def pulledTautologicalGenerator {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (U : S.affineOpens) (V : T.Opens)
    (hVF : V ≤ F ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1)) : Γ((tensorPullback F).obj D.line, V) :=
  ((tensorPullback F).obj D.line).val.map (homOfLE hVF).op
    (tensorPullbackSection F D.line
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
      (tautologicalGenerator D U m))

/-- Sectionwise chart normalization of the inverse line isomorphism. In particular, on
D(b_m) the pulled frame e goes to b_m*l. Taking any v in place of m gives b_v*l;
the fraction-chart equation identifies its pulled quotient coefficient with b_v/b_m.
The equation on every smaller open expresses compatibility on all overlaps and refinements.
Source: Stacks, Constructions, Tag 01OA
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
def InverseLineChartNormalization {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (θ : (tensorPullback F).obj D.line ≅ L) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)), IsFreeGenerator l →
    ∀ (m : Γ(E, U.1)) (V : T.Opens) (hVW : V ≤ W.1)
      (hVF : V ≤ F ⁻¹ᵁ
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)),
      θ.hom.app V (pulledTautologicalGenerator D F U V hVF m) =
        T.presheaf.map (homOfLE hVW).op
          (quotientGeneratorCoefficient h E L q U W hWU l m) •
            L.val.map (homOfLE hVW).op l ∧
      (IsUnit (T.presheaf.map (homOfLE hVW).op
          (quotientGeneratorCoefficient h E L q U W hWU l m)) →
        IsFreeGenerator (pulledTautologicalGenerator D F U V hVF m) ∧
        ∀ v : Γ(E, U.1),
          θ.hom.app V (pulledTautologicalGenerator D F U V hVF v) =
            (T.presheaf.map (homOfLE hVW).op
                (quotientGeneratorCoefficient h E L q U W hWU l v) *
              Ring.inverse (T.presheaf.map (homOfLE hVW).op
                (quotientGeneratorCoefficient h E L q U W hWU l m))) •
            (T.presheaf.map (homOfLE hVW).op
                (quotientGeneratorCoefficient h E L q U W hWU l m) •
              L.val.map (homOfLE hVW).op l)) ∧
      ∀ n : Γ(E, U.1),
        IsUnit (T.presheaf.map (homOfLE hVW).op
          (quotientGeneratorCoefficient h E L q U W hWU l n)) →
        pulledTautologicalGenerator D F U V hVF m =
          (T.presheaf.map (homOfLE hVW).op
              (quotientGeneratorCoefficient h E L q U W hWU l m) *
            Ring.inverse (T.presheaf.map (homOfLE hVW).op
              (quotientGeneratorCoefficient h E L q U W hWU l n))) •
            pulledTautologicalGenerator D F U V hVF n

/-- On a chart pulled back along a, use the pulled tautological generator itself as frame.
Its own quotient coefficient is one. The all-degree fraction charts then recover the ring
map of a on every c/e^d, including degree zero.
Source: Stacks, Constructions, Tags 01OA and 01O4
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
def RecoveredQuotientFrame {S T : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hWa : W.1 ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1)) (l : Γ((tensorPullback a).obj D.line, W.1)),
    l = ((tensorPullback a).obj D.line).val.map (homOfLE hWa).op
      (tensorPullbackSection a D.line
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
        (tautologicalGenerator D U m)) →
    IsFreeGenerator l →
    quotientGeneratorCoefficient h E ((tensorPullback a).obj D.line)
      (pulledQuotient D h a ha) U W hWU l m = 1

/-- The recovered all-degree chart ring map is exactly pullback by a: the coefficient
of c in the pulled e frame is a^*(c/e^d). The map k is the factorization of a into
Spec (A_e)_0, so appTop and the canonical affine section isomorphisms give its ring map.
Source: Stacks, Constructions, Tags 01OA and 01O4
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
def RecoveredFractionCoefficients {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback a).obj D.line)) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hWa : W.1 ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1))
    (k : W.1.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val))),
    W.1.ι ≫ a = k ≫
      Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
        (by decide : 0 < (1 : ℕ)) ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U →
    ∀ (d : ℕ) (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
      ψ.quotientCoefficient U W hWU
        (pulledTautologicalGenerator D a U W.1 hWa m) d c =
      W.1.topIso.hom (k.appTop ((Scheme.ΓSpecIso _).inv
        (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
          (quotientSymmetricGenerator E U m) d c)))

/-- Arbitrary pullback sends all homogeneous coefficients and all degree-zero fractions
to the fractions of their images. The localization homomorphism is fixed on every scalar,
so it is the canonical localization map rather than an arbitrary comparison.
Source: Stacks, Constructions, Tags 01OA and 01O4
(blueprint: lem-trf-line-quotient-chart-inverse-pullback). -/
def QuotientFractionNaturality {S T T' : Scheme.{u}} (h : T ⟶ S) (u : T' ⟶ T)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (ψ' : RelativeGradedLineMap (u ≫ h) (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback u).obj L)) : Prop :=
  ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)), IsFreeGenerator l →
    ∀ (W' : T'.affineOpens) (hWW' : W'.1 ≤ u ⁻¹ᵁ W.1)
      (hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1),
      (∀ (d : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
        ψ'.quotientCoefficient U W' hW'U
          (((tensorPullback u).obj L).val.map (homOfLE hWW').op
            (tensorPullbackSection u L W.1 l)) d z =
          u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z)) ∧
      ∀ m : Γ(E, U.1),
        quotientGeneratorCoefficient (u ≫ h) E ((tensorPullback u).obj L)
          (lineQuotientPullback h u E L q) U W' hW'U
          (((tensorPullback u).obj L).val.map (homOfLE hWW').op
            (tensorPullbackSection u L W.1 l)) m =
          u.appLE W.1 W'.1 hWW' (quotientGeneratorCoefficient h E L q U W hWU l m) ∧
        ∃ β : Localization.Away (quotientGeneratorCoefficient h E L q U W hWU l m) →+*
            Localization.Away (u.appLE W.1 W'.1 hWW'
              (quotientGeneratorCoefficient h E L q U W hWU l m)),
          (∀ b : Γ(T, W.1),
            β (algebraMap Γ(T, W.1) _ b) =
              algebraMap Γ(T', W'.1) _ (u.appLE W.1 W'.1 hWW' b)) ∧
          ∀ (d : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
            β (Localization.mk (ψ.quotientCoefficient U W hWU l d z)
              (⟨quotientGeneratorCoefficient h E L q U W hWU l m ^ d,
                ⟨d, rfl⟩⟩ : Submonoid.powers
                  (quotientGeneratorCoefficient h E L q U W hWU l m))) =
              Localization.mk
                (u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z))
                (⟨u.appLE W.1 W'.1 hWW'
                    (quotientGeneratorCoefficient h E L q U W hWU l m) ^ d,
                  ⟨d, rfl⟩⟩ : Submonoid.powers (u.appLE W.1 W'.1 hWW'
                    (quotientGeneratorCoefficient h E L q U W hWU l m)))

```

## New

The same signatures and bodies are in
`Sheaf.AlgebraicGeometry.LineQuotientChartInverseData`. The original module has
`public import Sheaf.AlgebraicGeometry.LineQuotientChartInverseData`, preserving every
public name and its meaning. The copied docstrings refer to the new definition node.
The inverse theorem node gains that definition node as a statement dependency and its
Lean attachment lists only the theorem; the data node records the seven relocated names.

## Users

All existing definitions keep identical names, types and bodies. The original module
publicly reexports the data module, so every downstream signature and statement is unchanged.
No consumer needs an adaptation. The list below was refreshed after the X5 data-module
landing; its previously forced import change is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback | G3 | Publicly reexports the moved definitions; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.LineZeroClassEtaleRealization | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.LineZeroGeometry | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.OrgogozoGoodModification | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.PlurinodalProperHypercover | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.TraitNearbyBaseChange | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.TraceFormula.AmpleNeighbourhood | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.TraceFormula.TemkinStableModification | not adapted; claim immaterial | Public interface preserved through the original module; no changes required. |
| Sheaf.AlgebraicGeometry.LineQuotientFractionKernel | G3, new | Kernel comparison; imports the shared definitions. |
| Sheaf.AlgebraicGeometry.LineQuotientRecoveredCharts | G3, new | Recovered coefficients; imports the shared definitions. |
| Sheaf.AlgebraicGeometry.LineQuotientIsoCharts | G3, new | Quotient isomorphism invariance; imports the shared definitions. |
| Sheaf.AlgebraicGeometry.LineQuotientPullbackCharts | G3, new | Arbitrary pullback; imports the shared definitions. |

## Status

landed 20261024T185801-L-3673567 2026-10-24 (merge of deliver/G3/Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback)
