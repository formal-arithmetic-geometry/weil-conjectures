module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.DiagonalDncChartNormalization
import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Sheaf.Paper.NormalModelSectionOrientation
import Sheaf.Paper.DiagonalDncAssemblyGlobal

/-! # Choice independence of the normalized diagonal orientation

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
prop-pur-smooth-purity-naturality-cover.proof.md, second sentence.
(blueprint: lem-pur-diagonal-orientation-choice-independent).

The two traces are arbitrary morphisms with the published frame normalization.
Their adjoint transposes and the two DNC comparisons are retained as actual arrows.
The canonical conormal bundle model supplies only a presentation of the normal cone.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The normalization predicate in the published unique-DNC-comparison statement,
with its existential quantifier opened to permit two realizations of the same map.
It reads the same family trivialization at one and zero on every finite-type base.
Source: naturality-cover proof, second sentence; thm-pur-dnc-invariance normalization
(blueprint: lem-pur-diagonal-orientation-choice-independent). -/
def DiagonalChoiceDncNormalized (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (α : Dnc.sourceSection P d g aB s ≅ Dnc.normalSection P d g aB s hs) : Prop :=
      ∀ (B' : Scheme.{u}) (aB' : B' ⟶ Spec (.of P.field.k))
        [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB']
        (b : B' ⟶ B) (_hb : b ≫ aB = aB')
        (C₀ : _root_.DerivedCategory
          (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (e : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
            (Dnc.familyEtale P d g aB s hs) ≅
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace (ULift.{u} (Fin 1)) B' ↘ B')).leftDerivedFunctor.obj C₀),
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso α =
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
              (Dnc.sourceComparison P d g aB s) ≪≫
            Dnc.pullComparison P b (Dnc.sourceEtale P d g aB s) ≪≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
              (Etale.sectionRestrictionIso _ b _ (AffineSpace.oneSection_comp_map b)
                  (AffineSpace.oneSection_comp_over _ B') (Dnc.fibreOne P d g aB s hs) e ≪≫
                (Etale.sectionRestrictionIso _ b _ (AffineSpace.zeroSection_comp_map b)
                  (AffineSpace.zeroSection_comp_over _ B') (Dnc.fibreZero P d g aB s hs) e).symm) ≪≫
            ((ProEtale.upperStar
                (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
                (Dnc.normalComparison P d g aB s hs) ≪≫
              Dnc.pullComparison P b (Dnc.normalEtale P d g aB s hs)).symm

/-- Zero-section restriction of inverse integration-transposed purity, on the
actual normal cone. The canonical conormal model preserves projection and zero;
its exceptional comparison is the published normalized etale-locality mate.
Source: naturality-cover proof, second sentence, beta_i; diagonal-chart proof,
normal-bundle presentation and zero-section restriction
(blueprint: lem-pur-diagonal-orientation-choice-independent). -/
def diagonalChoiceBeta (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian (f ≫ aY)
  letI := (chartDiagonalNormalBundle d f).1
  let F := ConormalGradedAlgebra.piece (pullback.diagonal f) 1
  let q := VectorBundleZeroSection.π X d F
  let z := VectorBundleZeroSection.zero X d F
  let e := chartNormalModel d f
  letI := (Etale.vectorIntegration_geometry X d F).1
  letI := (Etale.vectorIntegration_geometry X d F).2.1
  letI := Dnc.compactifiable P q (f ≫ aY)
  letI := P.noetherian (q ≫ f ≫ aY)
  let g := pullback.fst f f
  let s := pullback.diagonal f
  let hs := pullback.diagonal_fst f
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d g s hs
  letI := Dnc.normalCompactifiable P d g (f ≫ aY) s hs
  letI := P.noetherian (Scheme.Hom.normalConeProj g s ≫ f ≫ aY)
  fun (γ : P.diagonalTwistEtale (VectorBundleZeroSection.scheme X d F) d ≅
      P.diagonalOrdinaryDualizing q)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (M : Etale.EtaleCompactSupportNormalization P.Coefficient) ↦
      Dnc.normalComparison P d g (f ≫ aY) s hs ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (P.chartSectionEtaleRestriction M e.hom (Scheme.Hom.normalConeProj g s) q
            (chartNormal_model_exists d f).exists.choose_spec.2.1
            s.normalConeZeroSection z
            (chartNormal_model_exists d f).exists.choose_spec.2.2 ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) z).leftDerivedFunctor.mapIso
            (P.chartDualizingUnit q ≪≫ γ.symm) ≪≫
          Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t z
            (P.diagonalExponent_isUnit (q ≫ f ≫ aY)) d)

/-- The literal two-choice assertion. The local instances here are consequences
of the stated finite-type geometry. Each trace is normalized on all frames by
VectorIntegrationNormalization. Each gamma is its actual adjunction transpose,
with the canonical Tate pullback; beta is then diagonalChoiceBeta. The final two
equalities compare actual derived morphisms and identify their common value.
Source: naturality-cover proof, second sentence, Pi_i = beta_i delta_i alpha^-1
(blueprint: lem-pur-diagonal-orientation-choice-independent). -/
def DiagonalOrientationChoiceIndependentConclusion (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI := P.noetherian (f ≫ aY)
  letI := Dnc.compactifiable P f aY
  letI := (chartDiagonalNormalBundle d f).1
  let F := ConormalGradedAlgebra.piece (pullback.diagonal f) 1
  let q := VectorBundleZeroSection.π X d F
  letI := (Etale.vectorIntegration_geometry X d F).1
  letI := (Etale.vectorIntegration_geometry X d F).2.1
  letI := Dnc.compactifiable P q (f ≫ aY)
  ∀ (δ₁ δ₂ :
      Dnc.sourceSection P d (pullback.fst f f) (f ≫ aY) (pullback.diagonal f) ≅
        Dnc.normalSection P d (pullback.fst f f) (f ≫ aY) (pullback.diagonal f)
          (pullback.diagonal_fst f)),
    P.DiagonalChoiceDncNormalized d (pullback.fst f f) (f ≫ aY)
      (pullback.diagonal f) (pullback.diagonal_fst f) δ₁ →
    P.DiagonalChoiceDncNormalized d (pullback.fst f f) (f ≫ aY)
      (pullback.diagonal f) (pullback.diagonal_fst f) δ₂ →
    ∀ (t₁ t₂ : Etale.vectorIntegrationSource P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates X d F ⟶ Etale.ordinaryFiniteUnit P.Coefficient X),
      Etale.VectorIntegrationNormalization P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d F t₁ →
      Etale.VectorIntegrationNormalization P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d F t₂ →
      ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates)
        (M : Etale.EtaleCompactSupportNormalization P.Coefficient)
        (γ₁ γ₂ : P.diagonalTwistEtale (VectorBundleZeroSection.scheme X d F) d ≅
          P.diagonalOrdinaryDualizing q),
        γ₁.hom = (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
          P.diagonalExponent P.diagonalExponent_annihilates t q
          (P.diagonalExponent_isUnit (f ≫ aY)) d).inv ≫
          (Etale.rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} P.Coefficient) q).homEquiv _ _ t₁ →
        γ₂.hom = (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
          P.diagonalExponent P.diagonalExponent_annihilates t q
          (P.diagonalExponent_isUnit (f ≫ aY)) d).inv ≫
          (Etale.rightDerivedUpperShriekAdjunction
            (ModuleCat.{u + 1} P.Coefficient) q).homEquiv _ _ t₂ →
        (P.chartDiagonalAlpha d f aY).inv ≫ δ₁.hom ≫
            (P.diagonalChoiceBeta d f aY γ₁ t M).hom =
          (P.chartDiagonalAlpha d f aY).inv ≫ δ₂.hom ≫
            (P.diagonalChoiceBeta d f aY γ₂ t M).hom ∧
        (P.chartDiagonalAlpha d f aY).inv ≫ δ₁.hom ≫
            (P.diagonalChoiceBeta d f aY γ₁ t M).hom =
          (P.diagonalDualizingObject d f aY).hom

private theorem unique_map_of_unique_normalized_pair
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) [H.Full] {X : D} {L N : C}
    (Q : (X ≅ H.obj L) → Prop) (P : (X ⟶ H.obj N) → Prop)
    (h : ∃! p : (X ≅ H.obj L) × (L ⟶ N),
      Q p.1 ∧ P (p.1.hom ≫ H.map p.2))
    {t₁ t₂ : X ⟶ H.obj N} (h₁ : P t₁) (h₂ : P t₂) : t₁ = t₂ := by
  obtain ⟨p, hp, hu⟩ := h
  obtain ⟨l₁, hl₁⟩ := H.map_surjective (p.1.inv ≫ t₁)
  obtain ⟨l₂, hl₂⟩ := H.map_surjective (p.1.inv ≫ t₂)
  have hf₁ : p.1.hom ≫ H.map l₁ = t₁ := by rw [hl₁, Iso.hom_inv_id_assoc]
  have hf₂ : p.1.hom ≫ H.map l₂ = t₂ := by rw [hl₂, Iso.hom_inv_id_assoc]
  have he₁ : (p.1, l₁) = p := hu _ ⟨hp.1, hf₁.symm ▸ h₁⟩
  have he₂ : (p.1, l₂) = p := hu _ ⟨hp.1, hf₂.symm ▸ h₂⟩
  have hl : l₁ = l₂ := congrArg Prod.snd (he₁.trans he₂.symm)
  exact hf₁.symm.trans ((congrArg (fun l ↦ p.1.hom ≫ H.map l) hl).trans hf₂)

private theorem normalizedIntegration_unique (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (t₁ t₂ : Etale.vectorIntegrationSource A N hA S d F ⟶ Etale.ordinaryFiniteUnit A S)
    (h₁ : Etale.VectorIntegrationNormalization N hN A hA S hS d F t₁)
    (h₂ : Etale.VectorIntegrationNormalization N hN A hA S hS d F t₂) : t₁ = t₂ := by
  exact unique_map_of_unique_normalized_pair
    (_root_.DerivedCategory.singleFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (L := Etale.vectorIntegrationSheaf A N hA S d F)
    (N := Etale.ordinaryFiniteConstant A S)
    (fun e ↦ (_root_.DerivedCategory.homologyFunctor _ 0).map e.hom ≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
        (Etale.vectorIntegrationSheaf A N hA S d F) = 𝟙 _)
    (Etale.VectorIntegrationNormalization N hN A hA S hS d F)
    (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2 h₁ h₂

/-- Normalized diagonal/DNC orientations are independent of coordinate covers,
trivializing covers, and frames, and equal the specified canonical orientation.
Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
prop-pur-smooth-purity-naturality-cover.proof.md, second sentence
(blueprint: lem-pur-diagonal-orientation-choice-independent).

Proof:
1. Normalized uniqueness in thm-pur-dnc-invariance identifies the two DNC arrows.
2. The defining vector-integration gluing theorem uniquely characterizes a pair
   consisting of a degree-zero identification and a sheaf map. Fullness of the
   single-degree embedding expresses any normalized trace using that same
   identification. Pair uniqueness therefore identifies the two actual traces.
3. The exceptional adjunction and canonical Tate pullback preserve this equality;
   hence the gammas, betas and complete two-choice composites agree.
4. The same trace uniqueness identifies the first trace with the specified vector
   integration. Normal-model section orientation identifies its beta with the
   fixed chart beta, and normalized DNC uniqueness identifies its delta.
5. Global diagonal assembly identifies the resulting canonical three-factor
   composite with the specified orientation. The two separate geometric results
   are lem-pur-normal-model-section-orientation and
   lem-pur-diagonal-dnc-assembly-global; they retain the affine normalization,
   restriction and degree-zero gluing parts of the source proof. -/
theorem diagonalOrientationChoiceIndependent (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY] :
    P.DiagonalOrientationChoiceIndependentConclusion d f aY := by
  classical
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  let := Dnc.compactifiable P f aY
  let := (chartDiagonalNormalBundle d f).1
  let F := ConormalGradedAlgebra.piece (pullback.diagonal f) 1
  let q := VectorBundleZeroSection.π X d F
  let := (Etale.vectorIntegration_geometry X d F).1
  let := (Etale.vectorIntegration_geometry X d F).2.1
  let := Dnc.compactifiable P q (f ≫ aY)
  dsimp only [DiagonalOrientationChoiceIndependentConclusion]
  intro δ₁ δ₂ hδ₁ hδ₂ t₁ t₂ ht₁ ht₂ t M γ₁ γ₂ hγ₁ hγ₂
  have hδ : δ₁ = δ₂ := (Dnc.existsUnique_dncInvariance P d
    (pullback.fst f f) (f ≫ aY) (pullback.diagonal f)
      (pullback.diagonal_fst f)).unique hδ₁ hδ₂
  have ht : t₁ = t₂ := normalizedIntegration_unique P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d F
    t₁ t₂ ht₁ ht₂
  have hγ : γ₁ = γ₂ := by
    apply Iso.ext
    exact hγ₁.trans ((congrArg (fun a ↦
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates t q
        (P.diagonalExponent_isUnit (f ≫ aY)) d).inv ≫
        (Etale.rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} P.Coefficient) q).homEquiv _ _ a) ht).trans hγ₂.symm)
  constructor
  · rw [hδ, hγ]
  · have hδcanon : δ₁ = P.chartDiagonalDelta d f aY :=
      (Dnc.existsUnique_dncInvariance P d (pullback.fst f f) (f ≫ aY)
        (pullback.diagonal f) (pullback.diagonal_fst f)).unique hδ₁
          (Dnc.existsUnique_dncInvariance P d (pullback.fst f f) (f ≫ aY)
            (pullback.diagonal f) (pullback.diagonal_fst f)).exists.choose_spec
    have htcanon : t₁ = Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d F :=
      normalizedIntegration_unique P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d F
        _ _ ht₁ (Etale.existsUnique_vectorIntegrationGluing P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (f ≫ aY)) d F
          ).2.exists.choose_spec.2
    have hβ : P.diagonalChoiceBeta d f aY γ₁ t M = P.chartDiagonalBeta d f aY t := by
      let g := pullback.fst f f
      let s := pullback.diagonal f
      let hs := pullback.diagonal_fst f
      let : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
        (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
      let := Dnc.normalQuasiCompact d g s hs
      let := Dnc.normalCompactifiable P d g (f ≫ aY) s hs
      have hn := P.normalModelSectionOrientation d (Scheme.Hom.normalConeProj g s)
        (f ≫ aY) s.normalConeZeroSection F (chartNormalModel d f)
        (chartNormal_model_exists d f).exists.choose_spec.2.1
        (chartNormal_model_exists d f).exists.choose_spec.2.2 t M γ₁
        (hγ₁.trans (congrArg (fun a ↦
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
            P.diagonalExponent P.diagonalExponent_annihilates t q
            (P.diagonalExponent_isUnit (f ≫ aY)) d).inv ≫
            (Etale.rightDerivedUpperShriekAdjunction
              (ModuleCat.{u + 1} P.Coefficient) q).homEquiv _ _ a) htcanon))
      dsimp only [diagonalChoiceBeta, chartDiagonalBeta]
      rw [hn]
      rfl
    rw [hδcanon, hβ]
    exact congrArg Iso.hom (P.diagonalDncAssemblyGlobal d f aY t).symm

end WeilConjectures.PurityFiniteSetting
