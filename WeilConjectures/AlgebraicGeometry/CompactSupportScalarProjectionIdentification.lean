/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarMate
public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitReduction
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.CompletedProjectionCoherence
public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarCompletionNormalization
public import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionRealization
public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarGammaIdentification
import all WeilConjectures.AlgebraicGeometry.SfProEtaleProjectionFormula
import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionCoefficientChange
import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientModels
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteFree
import all WeilConjectures.AlgebraicGeometry.CompactSupportScalarCompletionNormalization
import all WeilConjectures.AlgebraicGeometry.SfCompleteDirectImageReduction
import all WeilConjectures.SixFunctors.OpenQuotientKoszulCompleteness
import WeilConjectures.SixFunctors.OpenDvrIntrinsicCriterion
import WeilConjectures.SixFunctors.OpenDvrIntrinsicOpenTransport
import WeilConjectures.SixFunctors.OpenDvrRingedIdentification

public import WeilConjectures.AlgebraicGeometry.CompactSupportCompletedScalarArrow
public import WeilConjectures.AlgebraicGeometry.CompactSupportCompletedProjectionData
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData

/-!
# Scalar projection squares through completion

Source: Stacks, Cohomology on Sites, Tags 0E48, 0B56, 07A6, 0941 and 0A07;
Modules on Sites, Tag 0E8I. The auxiliary assembly is the nine-step proof in
(blueprint: lem-pur-compact-support-scalar-projection-identification).

The scalar functor is ordinary derived extension of the completed coefficient
sheaf. The support functor is the specified total limit, identified with the
proper/open functor by its actual finite scalar-adjunction counits. All completion
comparisons below are fixed by the completion unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurScalarProjection
open PurCompactSupport

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  IntegralOnSlice.completion IntegralOnSlice.completionUnit
  completedCoefficientMap PurCompactSupport.scalarTensor PurCompactSupport.scalarPull
  PurCompactSupport.comparison


variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem tensor_domains (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)] (hl : IsUnit (l : Γ(W, ⊤)))
    (a : PurProjectionData.TensorModel l E W) (M N : DerivedCategory (integralTowerModules l E W))
    (hM : sfIntegralConstructible l E W M) (hN : sfIntegralConstructible l E W N) :
    sfIntegralConstructible l E W (a.tensor.obj (M, N)) ∧
      IsIso ((IntegralOnSlice.completionUnit l E W none).app (a.tensor.obj (M, N))) ∧
      sfIntegralConstructible l E W
        ((IntegralOnSlice.completion l E W none).obj (a.tensor.obj (M, N))) := by
  exact SfProEtaleProjection.tensor_domains l E W hl a M N hM hN

private theorem pull_domains {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    (hXd : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hYd : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hXi : IsUnit (l : Γ(X, ⊤))) (hYi : IsUnit (l : Γ(Y, ⊤)))
    (L : DerivedCategory (integralTowerModules l E Y)) (hL : sfIntegralConstructible l E Y L) :
    sfIntegralConstructible l E X
      ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L) := by
  exact SfProEtaleProjection.pull_domains l E f hXd hYd hXi hYi L hL

/-- Canonical scalar balancing for completed tensor. Source: Stacks 07A4, 0941;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Step 8. -/
def scalarTensorCompleted (W : Scheme.{u})
    (a : PurProjectionData.TensorModel l E W)
    (b : PurProjectionData.TensorModel l F W)
    (Q T : DerivedCategory (scalarReductionSource l E W)) :=
  scalarCompletion l E F i W (a.tensor.obj (Q, T)) ≪≫
    (IntegralOnSlice.completion l F W none).mapIso
      ((scalarTensor (completedCoefficientMap l E F i W) a b).app (Q, T))

private theorem scalarTensorCompleted_iso_naturality (W : Scheme.{u})
    (a : PurProjectionData.TensorModel l E W)
    (b : PurProjectionData.TensorModel l F W)
    {M N : DerivedCategory (scalarReductionSource l E W)} (q : M ≅ N)
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i W)).map
        ((IntegralOnSlice.completion l E W none).map
          (a.tensor.map (Prod.mkHom q.hom (𝟙 K)))) ≫
        (scalarTensorCompleted l E F i W a b N K).hom =
      (scalarTensorCompleted l E F i W a b M K).hom ≫
        (IntegralOnSlice.completion l F W none).map
          (b.tensor.map (Prod.mkHom
            ((pbcDerivedExtend (completedCoefficientMap l E F i W)).map q.hom) (𝟙 _))) := by
  have hχ := scalarCompletion_iso_naturality l E F i W
    (a.tensor.mapIso (Iso.prod q (Iso.refl K)))
  have hτ := (scalarTensor (completedCoefficientMap l E F i W) a b).hom.naturality
    (Prod.mkHom q.hom (𝟙 K))
  with_unfolding_all simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom] at hχ
  with_unfolding_all simp only [Functor.comp_map, Functor.prod_map] at hτ
  erw [CategoryTheory.Functor.map_id] at hτ
  with_unfolding_all dsimp only [
    scalarTensorCompleted, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  with_unfolding_all simp only [Category.assoc]
  erw [reassoc_of% hχ, ← Functor.map_comp, hτ, Functor.map_comp]

private theorem scalarTensorCompleted_unit (W : Scheme.{u})
    (a : PurProjectionData.TensorModel l E W)
    (b : PurProjectionData.TensorModel l F W)
    (Q T : DerivedCategory (scalarReductionSource l E W)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i W)).map
        ((IntegralOnSlice.completionUnit l E W none).app (a.tensor.obj (Q, T))) ≫
        (scalarTensorCompleted l E F i W a b Q T).hom =
      (scalarTensor (completedCoefficientMap l E F i W) a b).hom.app (Q, T) ≫
        (IntegralOnSlice.completionUnit l F W none).app
          (b.tensor.obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj Q,
              (pbcDerivedExtend (completedCoefficientMap l E F i W)).obj T)) := by
  have hχ := (scalarCompletion_existsUnique l E F i W (a.tensor.obj (Q, T))).exists.choose_spec
  have hη := (IntegralOnSlice.completionUnit l F W none).naturality
    ((scalarTensor (completedCoefficientMap l E F i W) a b).hom.app (Q, T))
  dsimp only [scalarTensorCompleted, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc]
  erw [hχ]
  exact hη.symm

/-- Ordinary proper projection with its actual tensor-pullback/counit transpose.
Source: Stacks 0B56;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Step 3.
-/
def properProjectionOrdinary {Z W : Scheme.{u}} (g : Z ⟶ W)
    (aZ : PurProjectionData.TensorModel l E Z)
    (aW : PurProjectionData.TensorModel l E W)
    (V : DerivedCategory (scalarReductionSource l E Z))
    (L : DerivedCategory (scalarReductionSource l E W)) :=
  (proEtaleRingDerivedAdjunction g ((completed l E).ring W)
    ((completed l E).ring Z) ((completed l E).pull g)).homEquiv _ _
    ((proEtaleCanonicalTensorComparison g ((completed l E).ring W)
        ((completed l E).ring Z) ((completed l E).pull g) aW aZ).hom.app
        ((push (completed l E) g).obj V, L) ≫
      aZ.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedAdjunction g ((completed l E).ring W)
          ((completed l E).ring Z) ((completed l E).pull g)).counit.app V) (𝟙 _)))

private theorem push_complete {Z W : Scheme.{u}} (g : Z ⟶ W)
    (Q : DerivedCategory (scalarReductionSource l E Z))
    (hQ : IsDerivedCompleteUnrestricted l E Z Q) :
    IsDerivedCompleteUnrestricted l E W ((push (completed l E) g).obj Q) := by
  have hpull : (completed l E).pull g = coefficient_inverse_image_iso l E g := by
    apply Iso.ext
    apply ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).injective
    change (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
        (sfCompletedCoefficientMap l E g)) = _
    rw [Equiv.apply_symm_apply]
    exact (coefficient_direct_image_eq l E g).symm
  have hpush : proEtaleRingModuleDirectImage g
      (completedIntegralCommRingSheafUnrestricted l E W)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      ((completed l E).pull g) = sfCompletedModuleDirectImage l E g := by
    rw [hpull]
    exact completed_direct_image_eq l E g
  let := sfCompletedModuleDirectImage_additive l E g
  let e : push (completed l E) g ≅ sfCompletedDerivedDirectImage l E g :=
    Functor.rightDerivedFunctorNatIso (eqToIso hpush)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨D⟩ := CompletedCoefficientPushforward.comparison l E g p (by omega)
  exact (complete_unrestricted l E W _).mp
    (complete_iso l E W (e.app Q).symm
      (completed_image_complete l E g D Q ((complete_unrestricted l E Z Q).mpr hQ)))

/-- The actual completed proper projection is uniquely fixed by the completion
unit, for all complete inputs, without constructibility or faithfulness assumptions.
Source: Stacks 07A6, 099N, 0B56, 0A07;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Step 5.
Proof: quotient completion has complete output. The normalized coefficient
adjunction identifies the specified ordinary proper image with the completed-ring
direct image. The completed-coefficient pushforward comparison shows that this
image preserves completeness. Thus the right-hand composite has a complete
target. The Hom bijection for the actual quotient-completion unit extends it
uniquely across that unit, proving both existence and the required normalization.
The reflector is the principal Koszul reflector transported by its normalized
quotient comparison. No geometric finiteness or constructibility is used. -/
theorem properProjection_existsUnique {Z W : Scheme.{u}} (g : Z ⟶ W) [IsProper g]
    (aZ : PurProjectionData.TensorModel l E Z)
    (aW : PurProjectionData.TensorModel l E W)
    (V : DerivedCategory (scalarReductionSource l E Z)) (_hV : IsSfDerivedComplete l E Z V)
    (L : DerivedCategory (scalarReductionSource l E W)) (_hL : IsSfDerivedComplete l E W L) :
    ∃! π : (IntegralOnSlice.completion l E W none).obj
          (aW.tensor.obj ((push (completed l E) g).obj V, L)) ⟶
        (push (completed l E) g).obj ((IntegralOnSlice.completion l E Z none).obj
          (aZ.tensor.obj (V, (pull (completed l E) g).obj L))),
      (IntegralOnSlice.completionUnit l E W none).app
          (aW.tensor.obj ((push (completed l E) g).obj V, L)) ≫ π =
        properProjectionOrdinary l E g aZ aW V L ≫
          (push (completed l E) g).map ((IntegralOnSlice.completionUnit l E Z none).app
            (aZ.tensor.obj (V, (pull (completed l E) g).obj L))) := by
  apply completion_extension_unique l E W
    (push_complete l E g _ (completion_complete l E Z _))
    (properProjectionOrdinary l E g aZ aW V L ≫
      (push (completed l E) g).map ((IntegralOnSlice.completionUnit l E Z none).app
        (aZ.tensor.obj (V, (pull (completed l E) g).obj L))))

/-- The unit-normalized proper completed-adjunction projection.
Source: Stacks 099N, 0B56;
(blueprint: lem-pur-compact-support-scalar-projection-identification),
Step 5. -/
def properProjection {Z W : Scheme.{u}} (g : Z ⟶ W) [IsProper g]
    (aZ : PurProjectionData.TensorModel l E Z)
    (aW : PurProjectionData.TensorModel l E W)
    (V : DerivedCategory (scalarReductionSource l E Z)) (hV : IsSfDerivedComplete l E Z V)
    (L : DerivedCategory (scalarReductionSource l E W)) (hL : IsSfDerivedComplete l E W L) :=
  (properProjection_existsUnique l E g aZ aW V hV L hL).exists.choose

private theorem open_complete {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] [QuasiCompact j]
    (Q : DerivedCategory (scalarReductionSource l E Z))
    (hQ : IsDerivedCompleteUnrestricted l E Z Q) :
    IsDerivedCompleteUnrestricted l E W
      ((openExtension (completed l E) j).mapDerivedCategory.obj Q) := by
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  have hgen : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal := by
    rw [hd]
    congr 1
    exact Set.range_const
  obtain ⟨CZ⟩ := dvrCoefficientModel_exists l E d hd Z
  obtain ⟨CW⟩ := dvrCoefficientModel_exists l E d hd W
  obtain ⟨O⟩ := dvrOpenModel_exists l E j
  have hI := openDvrIntrinsicOpenTransport l E d hgen j CZ CW O Q
    ((openDvrIntrinsicCriterion l E d hgen Z CZ Q).mp hQ)
  have hc := (openDvrIntrinsicCriterion l E d hgen W CW (O.jShriek.obj Q)).mpr hI
  obtain ⟨e⟩ := IntegralSystemRealization.openDvr_ringed_identification l E j O
  exact (complete_unrestricted l E W _).mp
    (complete_iso l E W (e.app Q) ((complete_unrestricted l E W _).mpr hc))

/-- Open extension has the same completion-unit normalization, including arbitrary
complete inputs. Source: Stacks 0E8I, 0GL1;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Step 6.
Proof: the intrinsic DVR completeness criterion and open transport show that
quasi-compact open extension preserves quotient completeness. The normalized
DVR/ringed identification gives this for the actual open extension. Its target
below is therefore complete. Apply the completion-reflector Hom bijection to
the ordinary open projection followed by open extension of the inner unit. -/
theorem openProjection_existsUnique {Z W : Scheme.{u}} (j : Z ⟶ W)
    [IsOpenImmersion j] [QuasiCompact j]
    (aZ : PurProjectionData.TensorModel l E Z)
    (aW : PurProjectionData.TensorModel l E W)
    (V : DerivedCategory (scalarReductionSource l E Z)) (_hV : IsSfDerivedComplete l E Z V)
    (L : DerivedCategory (scalarReductionSource l E W)) (_hL : IsSfDerivedComplete l E W L) :
    ∃! π : (IntegralOnSlice.completion l E W none).obj
          (aW.tensor.obj ((openExtension (completed l E) j).mapDerivedCategory.obj V, L)) ⟶
        (openExtension (completed l E) j).mapDerivedCategory.obj
          ((IntegralOnSlice.completion l E Z none).obj
            (aZ.tensor.obj (V, (pull (completed l E) j).obj L))),
      (IntegralOnSlice.completionUnit l E W none).app
          (aW.tensor.obj ((openExtension (completed l E) j).mapDerivedCategory.obj V, L)) ≫ π =
        (openProjectionIso (completed l E) j aZ aW V L).hom ≫
          (openExtension (completed l E) j).mapDerivedCategory.map
            ((IntegralOnSlice.completionUnit l E Z none).app
              (aZ.tensor.obj (V, (pull (completed l E) j).obj L))) := by
  apply completion_extension_unique l E W
    (open_complete l E j _ (completion_complete l E Z _))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

include hl in
private theorem scheme_unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    IsUnit (l : Γ(W, ⊤)) := by
  let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop
  simpa only [map_natCast] using (PurCompactSupport.coefficientPrimeUnit l D hl).map ρ.hom

include hl in
private theorem residue_unit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (w : W) :
    IsUnit (l : W.residueField w) := by
  let ρ := W.presheaf.germ ⊤ w trivial
  have hs := (scheme_unit l D hl W).map ρ.hom
  exact (by simpa only [map_natCast] using hs.map (W.residue w).hom)

private theorem finite_dimension (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))] :
    ∃ n : ℕ, topologicalKrullDim W ≤ n := by
  have hd := topologicalKrullDim_lt_top_of_finiteType (W ↘ Spec (.of D.k))
  obtain h | h := eq_or_ne (topologicalKrullDim W) ⊥
  · exact ⟨0, by simp only [h, bot_le]⟩
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h
    rw [← ha] at hd ⊢
    change (a : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) at hd
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (WithBot.coe_lt_coe.mp hd).ne
    exact ⟨n, by rw [← hn]; exact le_rfl⟩

set_option linter.unusedSectionVars false in
private theorem supportCounit_naturality
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (n : ℕ)
    {M N : DerivedCategory (scalarReductionSource l E X)} (q : M ⟶ N) :
    (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map
        ((PurStrictScalar.scalarSupport l E c S).map q) ≫
        PurStrictScalar.scalarSupportCounit l E c S n N =
      PurStrictScalar.scalarSupportCounit l E c S n M ≫
        (image (finite l E (n + 1) (Nat.le_add_left 1 n)) c).map
          ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).map q) := by
  let τ := Functor.whiskerLeft (PurStrictScalar.scalarSupportNative l E c S)
      (coefficientSequenceProjection l E Y n) ≫
    Functor.whiskerRight (PurStrictScalar.scalarSupportEvaluation l E c S n).hom
      (coefficientFiniteDerivedRestriction l E Y n)
  apply (pbcDerivedScalarAdjunction
    (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).homEquiv_naturality_right_square
  exact τ.naturality q

include D hl in
private theorem realization_iso_naturality
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    {M N : DerivedCategory (scalarReductionSource l E X)} (q : M ≅ N)
    (hM : finiteTorConstructibleIntegral l E X M)
    (hN : finiteTorConstructibleIntegral l E X N) :
    (image (completed l E) c).map q.hom ≫
        (realization l E D hl f c S N hN).hom =
      (realization l E D hl f c S M hM).hom ≫
        (PurStrictScalar.scalarSupport l E c S).map q.hom := by
  let P := image (completed l E) c
  let R := PurStrictScalar.scalarSupport l E c S
  let z := P.mapIso q ≪≫ realization l E D hl f c S N hN ≪≫ (R.mapIso q).symm
  have hz : ∀ n : ℕ,
      (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map
          z.hom ≫ PurStrictScalar.scalarSupportCounit l E c S n M =
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M := by
    intro n
    let T := pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)
    have hs := supportCounit_naturality l E f c S n q.inv
    have hρ := (realization_existsUnique l E D hl f c S N hN).exists.choose_spec n
    have hc := (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).naturality
      q.hom
    with_unfolding_all dsimp only [
      z, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
    with_unfolding_all simp only [Functor.map_comp, Category.assoc]
    erw [hs]
    erw [reassoc_of% hρ]
    with_unfolding_all simp only [Functor.comp_map] at hc
    erw [reassoc_of% hc]
    erw [← CategoryTheory.Functor.map_comp]
    change (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M ≫
      (image (finite l E (n + 1) (Nat.le_add_left 1 n)) c).map
        ((pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).map q.hom ≫
          (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X)).map q.inv) = _
    erw [← CategoryTheory.Functor.map_comp, q.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have heq : z = realization l E D hl f c S M hM :=
    (realization_existsUnique l E D hl f c S M hM).unique hz
      (realization_existsUnique l E D hl f c S M hM).exists.choose_spec
  have hh := congrArg (fun a ↦ a.hom ≫ R.map q.hom) heq
  with_unfolding_all simp only [z, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc, ← R.map_comp, q.inv_hom_id,
    R.map_id] at hh
  erw [Category.comp_id] at hh
  exact hh

/-- The whole quotient-diagram support realization is the adjunct of the
normalized total-limit realization, retaining the actual system counit.
Source: Stacks 07A6, 0941;
(blueprint: lem-pur-compact-support-scalar-projection-identification),
Steps 5--7. -/
def nativeRealization
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SY : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :=
  SY.reduction.map (realization l E D hl f c SX M hM).hom ≫
    SY.adjunction.counit.app ((PurStrictScalar.scalarSupportNative l E c SX).obj M)

/-- The first ordinary scalar/projection route, with the canonical tensor and
pullback balancing at its target. Source: Stacks 0E48 and 0B56;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Steps 3--4. -/
def projectionFirst
    (aX : PurProjectionData.TensorModel l E X)
    (aZ : PurProjectionData.TensorModel l E c.Z)
    (aY : PurProjectionData.TensorModel l E Y)
    (bX : PurProjectionData.TensorModel l F X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (K : DerivedCategory (scalarReductionSource l E Y)) :=
  (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
      (((projectionMap (completed l E) c aX aZ aY
        (completedPull_comp l E c.i c.g)).app M).app K) ≫
    (comparison (completedChange l E F i) c).app
      (PurProjectionData.ordinaryInner l E f aX M K) ≫
    (image (completed l F) c).map
      ((scalarTensor (completedCoefficientMap l E F i X) aX bX).hom.app
          (M, (pull (completed l E) f).obj K) ≫
        bX.tensor.map (Prod.mkHom (𝟙 _)
          ((scalarPull (completedChange l E F i) f).hom.app K)))

/-- The other ordinary route is scalar balancing, the actual proper/open scalar
mate, then the F-projection. Source: Stacks 0E48 and 0B56;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Steps 3--4. -/
def scalarFirst
    (aY : PurProjectionData.TensorModel l E Y)
    (bX : PurProjectionData.TensorModel l F X)
    (bZ : PurProjectionData.TensorModel l F c.Z)
    (bY : PurProjectionData.TensorModel l F Y)
    (M : DerivedCategory (scalarReductionSource l E X))
    (K : DerivedCategory (scalarReductionSource l E Y)) :=
  (scalarTensor (completedCoefficientMap l E F i Y) aY bY).hom.app
      ((image (completed l E) c).obj M, K) ≫
    bY.tensor.map (Prod.mkHom ((comparison (completedChange l E F i) c).app M) (𝟙 _)) ≫
    ((projectionMap (completed l F) c bX bZ bY
      (completedPull_comp l F c.i c.g)).app
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)).app
          ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K)

include D hl in
private theorem finiteTor_of_constructible (W : Scheme.{u})
    [W.Over (Spec (.of D.k))]
    (Q : DerivedCategory (scalarReductionSource l E W))
    (hQ : sfIntegralConstructible l E W Q) : finiteTorConstructibleIntegral l E W Q := by
  have hglobal : IsUnit (l : Γ(W, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using (coefficientPrimeUnit l D hl).map ρ.hom
  let (x : W) : Invertible (l : W.residueField x) :=
    (show IsUnit (l : W.residueField x) from by
      simpa only [map_natCast] using
        (hglobal.map (W.presheaf.germ ⊤ x trivial).hom).map (W.residue x).hom).invertible
  rw [← (integral_residue_tor D l hl E W).2]
  exact hQ

set_option linter.unusedSectionVars false in
include D hl in
/-- The inner completed tensor has the uniform finite-Tor domain needed for gamma.
Source: Stacks 07A4, 099N; blueprint proof Step 2
(blueprint: lem-pur-compact-support-scalar-projection-identification).
Proof: reduction commutes with completed pullback and completed tensor by their
normalized simultaneous quotient models. Pullback preserves the interval of K.
Tensor adds its endpoints to the interval of M. Finite tensor preserves bounded
constructibility. Completion supplies derived completeness and retains these
reductions with their uniform sum interval. -/
theorem inner_domain
    (aX : PurProjectionData.TensorModel l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : finiteTorConstructibleIntegral l E Y K) :
    finiteTorConstructibleIntegral l E X
      ((IntegralOnSlice.completion l E X none).obj
        (PurProjectionData.ordinaryInner l E f aX M K)) := by
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  have : IsNoetherian Y := ⟨⟩
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  let (x : X) : Invertible (l : X.residueField x) :=
    (residue_unit l D hl X x).invertible
  let (y : Y) : Invertible (l : Y.residueField y) :=
    (residue_unit l D hl Y y).invertible
  have hp := pull_domains l E f
    (finite_dimension D X) (finite_dimension D Y)
    (scheme_unit l D hl X) (scheme_unit l D hl Y) K _hK.1
  have ht := tensor_domains l E X (scheme_unit l D hl X) aX M _ _hM.1 hp
  exact finiteTor_of_constructible l E D hl X _ ht.2.2


set_option linter.unusedSectionVars false in
include D hl in
/-- Completion-unit normalization of the actual proper/open projection, including
uniqueness of its extension. Source: Stacks 07A6, 0B56, 0E8I, 099N;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Steps 5--6.
Proof: completed proper-adjunction coherence identifies the proper counit mate
by its unit equation. The quasi-compact open comparison preserves the open unit;
paste the equations. The completed target is complete, so precomposition with
the source completion unit is a Hom bijection, proving uniqueness. -/
theorem projection_unit
    (aX : PurProjectionData.TensorModel l E X)
    (aZ : PurProjectionData.TensorModel l E c.Z)
    (aY : PurProjectionData.TensorModel l E Y)
    (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E Y) :
    (IntegralOnSlice.completionUnit l E Y none).app
        (PurProjectionData.ordinarySource l E c aY M.obj K.obj) ≫
        (PurProjectionData.integralMap l E D hl f c aX aZ aY M K).hom =
      ((projectionMap (completed l E) c aX aZ aY
        (completedPull_comp l E c.i c.g)).app M.obj).app K.obj ≫
        (image (completed l E) c).map
          ((IntegralOnSlice.completionUnit l E X none).app
            (PurProjectionData.ordinaryInner l E f aX M.obj K.obj)) ∧
    ∀ π : PurProjectionData.completedSource l E c aY M.obj K.obj ⟶
        PurProjectionData.completedTarget l E c aX M.obj K.obj,
      (IntegralOnSlice.completionUnit l E Y none).app
          (PurProjectionData.ordinarySource l E c aY M.obj K.obj) ≫ π =
        ((projectionMap (completed l E) c aX aZ aY
          (completedPull_comp l E c.i c.g)).app M.obj).app K.obj ≫
          (image (completed l E) c).map
            ((IntegralOnSlice.completionUnit l E X none).app
              (PurProjectionData.ordinaryInner l E f aX M.obj K.obj)) →
      π = (PurProjectionData.integralMap l E D hl f c aX aZ aY M K).hom := by
  have := (PurProjectionData.integralDomains l E D hl f c aX aY M K).1
  have hunit : (IntegralOnSlice.completionUnit l E Y none).app
      (PurProjectionData.ordinarySource l E c aY M.obj K.obj) ≫
      (PurProjectionData.integralMap l E D hl f c aX aZ aY M K).hom =
    ((projectionMap (completed l E) c aX aZ aY
      (completedPull_comp l E c.i c.g)).app M.obj).app K.obj ≫
      (image (completed l E) c).map
        ((IntegralOnSlice.completionUnit l E X none).app
          (PurProjectionData.ordinaryInner l E f aX M.obj K.obj)) := by
    simp only [PurProjectionData.integralMap, SfProEtaleProjection.integralMap,
      ObjectProperty.homMk_hom, IsIso.hom_inv_id_assoc]
  refine ⟨hunit, ?_⟩
  intro π hπ
  apply (cancel_epi ((IntegralOnSlice.completionUnit l E Y none).app
    (PurProjectionData.ordinarySource l E c aY M.obj K.obj))).1
  exact hπ.trans hunit.symm



include D hl in
/-- The two completed projection/scalar composites agree as integral morphisms.
Source: Stacks 0E48, 0B56, 0E8I; the completion-reflector argument
(blueprint: lem-pur-compact-support-scalar-projection-identification), Steps 1--9.

Proof:
1. Use the finite-free coefficient models and exact countable products, retaining
   the full F-uniformizer tower and its ramified arithmetic subsequence.
2. Tensor and pullback add the two uniform Tor intervals, so all inputs below
   lie in the same complete constructible domains, including the inner tensor.
3. Ringed exchange/tensor coherence gives the proper scalar/projection square
   on the whole ringed quotient diagram, and on constant integral coefficients.
4. Open tensor normalization identifies its open factor by pure-tensor balancing;
   paste the proper and open squares in their specified order.
5. CompletedProjectionCoherence gives the proper completion-unit equation,
   uniqueness and the direct-image/total-limit identification, including counits.
6. Quasi-compact open completeness and completed-open-tensor system realization
   supply the same identification for open extension and its actual open unit.
7. The augmented strict transpose identifies the normalized limit scalar map
   with comparison, as recorded in gamma_identification above.
8. Finite-free scalar/completion exchange preserves the completion unit. Insert
   the tensor and pullback completion units using their normalized comparisons.
9. Precompose the displayed routes with the source completion unit. Naturality
   reduces them to the ordinary square of Steps 3--4. Their target is complete;
   injectivity of the reflector Hom bijection proves the integral equality.
No step uses faithfulness of reduction functors. -/
theorem ordinaryCompletedSquare
    (aX : PurProjectionData.TensorModel l E X)
    (aZ : PurProjectionData.TensorModel l E c.Z)
    (aY : PurProjectionData.TensorModel l E Y)
    (bX : PurProjectionData.TensorModel l F X)
    (bZ : PurProjectionData.TensorModel l F c.Z)
    (bY : PurProjectionData.TensorModel l F Y)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (hK : finiteTorConstructibleIntegral l E Y K) :
    ∃ (hCM : sfIntegralConstructible l F X
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
      (hCK : sfIntegralConstructible l F Y
          ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K)),
      (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
          (PurProjectionData.integralMap l E D hl f c aX aZ aY
            ⟨M, hM.1⟩ ⟨K, hK.1⟩).hom ≫
        (comparison (completedChange l E F i) c).app
          ((IntegralOnSlice.completion l E X none).obj
            (PurProjectionData.ordinaryInner l E f aX M K)) ≫
        (image (completed l F) c).map
          ((scalarCompletion l E F i X
              (PurProjectionData.ordinaryInner l E f aX M K)).hom ≫
            (IntegralOnSlice.completion l F X none).map
              ((scalarTensor (completedCoefficientMap l E F i X) aX bX).hom.app
                  (M, (pull (completed l E) f).obj K) ≫
                bX.tensor.map (Prod.mkHom (𝟙 _)
                  ((scalarPull (completedChange l E F i) f).hom.app K)))) =
      (scalarTensorCompleted l E F i Y aY bY
          ((image (completed l E) c).obj M) K).hom ≫
        (IntegralOnSlice.completion l F Y none).map
          (bY.tensor.map (Prod.mkHom
            ((comparison (completedChange l E F i) c).app M) (𝟙 _))) ≫
        (PurProjectionData.integralMap l F D hl f c bX bZ bY
          ⟨(pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M, hCM⟩
          ⟨(pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K, hCK⟩).hom := by
  obtain ⟨a, e, hepos, heq⟩ := integral_ramification l E F i
  have he : Ramification l E F i e := by
    dsimp only [Ramification, Padic.coefficientExtensionIdeal]
    rw [pow_one, Ideal.map_span, Set.image_singleton, heq,
      Ideal.span_singleton_mul_left_unit a.isUnit, Ideal.span_singleton_pow]
  have hCM := (compactSupportCoefficientModels_scalar l E F i D hl e hepos he X M hM).1.1
  have hCK := (compactSupportCoefficientModels_scalar l E F i D hl e hepos he Y K hK).1.1
  refine ⟨hCM, hCK, ?_⟩
  let TY := pbcDerivedExtend (completedCoefficientMap l E F i Y)
  let TX := pbcDerivedExtend (completedCoefficientMap l E F i X)
  let PF := image (completed l F) c
  let NE := PurProjectionData.ordinaryInner l E f aX M K
  let NF := PurProjectionData.ordinaryInner l F f bX (TX.obj M) (TY.obj K)
  let bal := (scalarTensor (completedCoefficientMap l E F i X) aX bX).hom.app
      (M, (pull (completed l E) f).obj K) ≫
    bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull (completedChange l E F i) f).hom.app K))
  have hE := (projection_unit l E D hl f c aX aZ aY ⟨M, hM.1⟩ ⟨K, hK.1⟩).1
  have hF := (projection_unit l F D hl f c bX bZ bY
    ⟨TX.obj M, hCM⟩ ⟨TY.obj K, hCK⟩).1
  have hγ := (comparison (completedChange l E F i) c).naturality
    ((IntegralOnSlice.completionUnit l E X none).app NE)
  with_unfolding_all simp only [Functor.comp_map] at hγ
  have hχ := (scalarCompletion_existsUnique l E F i X NE).exists.choose_spec
  have hη := (IntegralOnSlice.completionUnit l F X none).naturality bal
  have hi : TX.map ((IntegralOnSlice.completionUnit l E X none).app NE) ≫
      (scalarCompletion l E F i X NE).hom ≫
      (IntegralOnSlice.completion l F X none).map bal =
      bal ≫ (IntegralOnSlice.completionUnit l F X none).app NF := by
    rw [← Category.assoc]
    erw [hχ]
    exact hη.symm
  have hi' := congrArg PF.map hi
  simp only [bal, Functor.map_comp, Category.assoc] at hi'
  have ht := scalarTensorCompleted_unit l E F i Y aY bY
    ((image (completed l E) c).obj M) K
  have hηY := (IntegralOnSlice.completionUnit l F Y none).naturality
    (bY.tensor.map (Prod.mkHom ((comparison (completedChange l E F i) c).app M)
      (𝟙 (TY.obj K))))
  have := (PurProjectionData.integralDomains l E D hl f c aX aY
    ⟨M, hM.1⟩ ⟨K, hK.1⟩).1
  apply (cancel_epi (TY.map ((IntegralOnSlice.completionUnit l E Y none).app
    (PurProjectionData.ordinarySource l E c aY M K)))).1
  have hEmap := congrArg TY.map hE
  simp only [Functor.map_comp] at hEmap
  simp only [Functor.map_comp]
  erw [reassoc_of% hEmap]
  erw [reassoc_of% hγ, hi', reassoc_of% ht]
  erw [reassoc_of% hηY.symm, hF]
  have hs := compactSupportProjectionCoefficientChange (completedChange l E F i) c
    aX aZ aY bX bZ bY (completedPull_comp l E c.i c.g)
    (completedPull_comp l F c.i c.g) M K
  have hs' := congrArg (fun q ↦ q ≫ PF.map
    ((IntegralOnSlice.completionUnit l F X none).app NF)) hs
  with_unfolding_all simp only [Functor.map_comp, Category.assoc] at hs'
  exact hs'

/-- The actual proper/open projection on the total-limit support presentation.
Both endpoint comparisons are the normalized realizations above; the middle map
is the published actual completed projection, not a freely chosen transformation.
Source: Stacks 0B56, 0E8I, 0941; blueprint Steps 5--6
(blueprint: lem-pur-compact-support-scalar-projection-identification). -/
def supportProjection
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (aX : PurProjectionData.TensorModel l E X)
    (aZ : PurProjectionData.TensorModel l E c.Z)
    (aY : PurProjectionData.TensorModel l E Y)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (hK : finiteTorConstructibleIntegral l E Y K) :=
  (IntegralOnSlice.completion l E Y none).map
      (aY.tensor.map (Prod.mkHom (realization l E D hl f c S M hM).inv (𝟙 K))) ≫
    (PurProjectionData.integralMap l E D hl f c aX aZ aY
      ⟨M, hM.1⟩ ⟨K, hK.1⟩).hom ≫
    (realization l E D hl f c S
      ((IntegralOnSlice.completion l E X none).obj
        (PurProjectionData.ordinaryInner l E f aX M K))
      (inner_domain l E D hl f aX M hM K hK)).hom

/-- Canonical scalar balancing at the inner completed tensor and pullback.
Source: Stacks 07A4, 099N; blueprint Step 8
(blueprint: lem-pur-compact-support-scalar-projection-identification). -/
def scalarInner
    (aX : PurProjectionData.TensorModel l E X)
    (bX : PurProjectionData.TensorModel l F X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (K : DerivedCategory (scalarReductionSource l E Y)) :=
  (scalarCompletion l E F i X
      (PurProjectionData.ordinaryInner l E f aX M K)).hom ≫
    (IntegralOnSlice.completion l F X none).map
      ((scalarTensor (completedCoefficientMap l E F i X) aX bX).hom.app
          (M, (pull (completed l E) f).obj K) ≫
        bX.tensor.map (Prod.mkHom (𝟙 _)
          ((scalarPull (completedChange l E F i) f).hom.app K)))

include D hl in
/-- The displayed scalar/projection square with gamma equal to the specified
normalized strict scalar limit r_e inverse R(q) tau, on the total-limit support.
Source: Stacks 0E48, 0B56, 0E8I; blueprint Steps 1--9
(blueprint: lem-pur-compact-support-scalar-projection-identification).
Proof: the finite-free coefficient model preserves the uniform constructible
Tor domain, giving hCM and hCK. Apply ordinaryCompletedSquare and conjugate by
the normalized support realizations. The gamma_identification equation replaces
each ordinary scalar comparison by the specified completedArrow, including at
the completed inner tensor, whose domain is inner_domain. Naturality of the
completion, tensor and support realization comparisons cancels the intermediate
isomorphisms. This gives the two composites below. Steps 3--4 of the node give
this equality on ringed quotient diagrams, as diagram_projection records;
Steps 5--8 identify their completed counits, and Step 9 uses the completion Hom
bijection. Thus the equality is integral and assumes no faithfulness of reduction. -/
theorem compactSupportScalarProjectionIdentification
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (aX : PurProjectionData.TensorModel l E X)
    (aZ : PurProjectionData.TensorModel l E c.Z)
    (aY : PurProjectionData.TensorModel l E Y)
    (bX : PurProjectionData.TensorModel l F X)
    (bZ : PurProjectionData.TensorModel l F c.Z)
    (bY : PurProjectionData.TensorModel l F Y)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (hK : finiteTorConstructibleIntegral l E Y K) :
    ∃ (hCM : finiteTorConstructibleIntegral l F X
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
      (hCK : finiteTorConstructibleIntegral l F Y
          ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K)),
      (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
          (supportProjection l E D hl f c SE aX aZ aY M hM K hK) ≫
        PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos
          ((IntegralOnSlice.completion l E X none).obj
            (PurProjectionData.ordinaryInner l E f aX M K))
          (inner_domain l E D hl f aX M hM K hK) ≫
        (PurStrictScalar.scalarSupport l F c SF).map
          (scalarInner l E F i f aX bX M K) =
      (scalarTensorCompleted l E F i Y aY bY
          ((PurStrictScalar.scalarSupport l E c SE).obj M) K).hom ≫
        (IntegralOnSlice.completion l F Y none).map
          (bY.tensor.map (Prod.mkHom
            (PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM)
            (𝟙 _))) ≫
        supportProjection l F D hl f c SF bX bZ bY
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) hCM
          ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K) hCK := by
  obtain ⟨hCM, hγM⟩ := gamma_identification l E F i D hl f c SE SF e he hepos M hM
  let SYE := (coefficientDerivedSystemEvaluationCalculus l E Y).choose
  let SYF := (coefficientDerivedSystemEvaluationCalculus l F Y).choose
  obtain ⟨hCK, _⟩ := gamma_identification l E F i D hl (𝟙 Y)
    (Compactification.ofIsProper (𝟙 Y)) SYE SYF e he hepos K hK
  refine ⟨hCM, hCK, ?_⟩
  let ME := (image (completed l E) c).obj M
  let CE := IntegralOnSlice.completion l E Y none
  let CF := IntegralOnSlice.completion l F Y none
  let TX := pbcDerivedExtend (completedCoefficientMap l E F i X)
  let TY := pbcDerivedExtend (completedCoefficientMap l E F i Y)
  let NE := (IntegralOnSlice.completion l E X none).obj
    (PurProjectionData.ordinaryInner l E f aX M K)
  let NF := (IntegralOnSlice.completion l F X none).obj
    (PurProjectionData.ordinaryInner l F f bX (TX.obj M) (TY.obj K))
  have hNE := inner_domain l E D hl f aX M hM K hK
  have hNF := inner_domain l F D hl f bX (TX.obj M) hCM (TY.obj K) hCK
  obtain ⟨hCN, hγN⟩ := gamma_identification l E F i D hl f c SE SF e he hepos NE hNE
  let q : TX.obj NE ≅ NF :=
    scalarCompletion l E F i X (PurProjectionData.ordinaryInner l E f aX M K) ≪≫
      (IntegralOnSlice.completion l F X none).mapIso
        ((scalarTensor (completedCoefficientMap l E F i X) aX bX).app
          (M, (pull (completed l E) f).obj K) ≪≫
          bX.tensor.mapIso (Iso.prod (Iso.refl _) ((scalarPull (completedChange l E F i) f).app K)))
  have hq : q.hom = scalarInner l E F i f aX bX M K := by
    simp only [q, scalarInner, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      Iso.app_hom, Iso.prod_hom, Iso.refl_hom]
  have hρ := realization_iso_naturality l F D hl f c SF q hCN hNF
  rw [hq] at hρ
  have hs := scalarTensorCompleted_iso_naturality l E F i Y aY bY
    (realization l E D hl f c SE M hM).symm K
  obtain ⟨_, _, ho⟩ := ordinaryCompletedSquare l E F i D hl f c
    aX aZ aY bX bZ bY M hM K hK
  have hγ : TY.map (realization l E D hl f c SE M hM).inv ≫
      (comparison (completedChange l E F i) c).app M =
    PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM ≫
      (realization l F D hl f c SF (TX.obj M) hCM).inv := by
    apply (cancel_mono (realization l F D hl f c SF (TX.obj M) hCM).hom).1
    rw [Category.assoc, ← hγM, ← Category.assoc, ← TY.map_comp,
      Iso.inv_hom_id, TY.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have ht : TY.map (CE.map (aY.tensor.map
        (Prod.mkHom (realization l E D hl f c SE M hM).inv (𝟙 K)))) ≫
      (scalarTensorCompleted l E F i Y aY bY ME K).hom ≫
      CF.map (bY.tensor.map (Prod.mkHom
        ((comparison (completedChange l E F i) c).app M) (𝟙 _))) =
    (scalarTensorCompleted l E F i Y aY bY
      ((PurStrictScalar.scalarSupport l E c SE).obj M) K).hom ≫
      CF.map (bY.tensor.map (Prod.mkHom
        (PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM) (𝟙 _))) ≫
      CF.map (bY.tensor.map
        (Prod.mkHom (realization l F D hl f c SF (TX.obj M) hCM).inv (𝟙 _))) := by
    erw [reassoc_of% hs, ← CF.map_comp, ← bY.tensor.map_comp]
    simp only [prod_comp, Category.id_comp]
    erw [hγ]
    rw [show Prod.mkHom
        (PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM ≫
          (realization l F D hl f c SF (TX.obj M) hCM).inv) (𝟙 (TY.obj K)) =
      Prod.mkHom (PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM)
          (𝟙 (TY.obj K)) ≫
        Prod.mkHom (realization l F D hl f c SF (TX.obj M) hCM).inv (𝟙 (TY.obj K)) by
      ext <;> simp only [prod_comp, Category.id_comp]]
    simp only [bY.tensor.map_comp, CF.map_comp]
    rfl
  dsimp only [supportProjection]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (TY.map _) (PurScalarArrow.completedArrow
    l E F i D hl f c SE SF e he hepos NE hNE), hγN]
  simp only [Category.assoc]
  erw [← hρ]
  have ho' := congrArg (fun k ↦ TY.map (CE.map (aY.tensor.map
      (Prod.mkHom (realization l E D hl f c SE M hM).inv (𝟙 K)))) ≫
      k ≫ (realization l F D hl f c SF NF hNF).hom) ho
  simp only [Category.assoc] at ho'
  erw [ho']
  erw [reassoc_of% ht]


include D hl in
/-- Equality of finite quotient projection routes in the native ringed diagram
category, before level evaluation. The endpoint presentation is reduction of
ordinary tensor; reductionTensor and nativeRealization identify it with tensor
and proper/open image of the finite quotient systems. Thus its arrows are the
actual finite projection arrows, with their representative and counit normalization.
Source: Stacks 0E48, 0B56, 0E8I;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Steps 2--4.
Proof: choose simultaneous flat K-flat representatives on the ringed sequence
sites. The proper projection is the counit transpose, so ringed exchange/tensor
coherence gives its square there. For the open factor, the two maps on pure
tensors multiply the same two B-scalars; extension by zero and sheafification
preserve the equality and every horizontal transition. Paste in the proper/open
order. The normalized reduction tensor and support adjunct comparisons transport
this equality to the displayed presentation. No inference from equality at each
finite evaluation is made. The interval sum gives hT uniformly at all levels. -/
theorem diagram_projection
    (SFX : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SFY : CoefficientDerivedSystemCalculus.{u, u} l F Y)
    (aX : PurProjectionData.TensorModel l E X)
    (aZ : PurProjectionData.TensorModel l E c.Z)
    (aY : PurProjectionData.TensorModel l E Y)
    (bX : PurProjectionData.TensorModel l F X)
    (bZ : PurProjectionData.TensorModel l F c.Z)
    (bY : PurProjectionData.TensorModel l F Y)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (hK : finiteTorConstructibleIntegral l E Y K) :
    ∃ hT : finiteTorConstructibleIntegral l F X
        (PurProjectionData.ordinaryInner l F f bX
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
          ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K)),
      SFY.reduction.map (projectionFirst l E F i f c aX aZ aY bX M K) ≫
          nativeRealization l F D hl f c SFX SFY
            (PurProjectionData.ordinaryInner l F f bX
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
              ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K)) hT =
        SFY.reduction.map (scalarFirst l E F i f c aY bX bZ bY M K) ≫
          nativeRealization l F D hl f c SFX SFY
            (PurProjectionData.ordinaryInner l F f bX
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
              ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K)) hT := by
  obtain ⟨hCM, hCK, _⟩ := ordinaryCompletedSquare l E F i D hl f c
    aX aZ aY bX bZ bY M hM K hK
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  have : IsNoetherian Y := ⟨⟩
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  let (x : X) : Invertible (l : X.residueField x) :=
    (residue_unit l D hl X x).invertible
  have hp := pull_domains l F f
    (finite_dimension D X) (finite_dimension D Y)
    (scheme_unit l D hl X) (scheme_unit l D hl Y) _ hCK
  have ht := tensor_domains l F X (scheme_unit l D hl X) bX _ _ hCM hp
  refine ⟨finiteTor_of_constructible l F D hl X _ ht.1, ?_⟩
  have hs := compactSupportProjectionCoefficientChange (completedChange l E F i) c
    aX aZ aY bX bZ bY (completedPull_comp l E c.i c.g)
    (completedPull_comp l F c.i c.g) M K
  exact congrArg (fun q ↦ SFY.reduction.map q ≫
    nativeRealization l F D hl f c SFX SFY _
      (finiteTor_of_constructible l F D hl X _ ht.1)) hs


end WeilConjectures.PurScalarProjection
