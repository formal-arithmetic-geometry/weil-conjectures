module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.BertiniIncidenceNaturality
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.Modules.TensorPowerSectionNonvanishingPullback
import WeilConjectures.AlgebraicGeometry.SectionClearingDenominatorsQCQS
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import all WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen
import all WeilConjectures.AlgebraicGeometry.NonvanishingLocusRestrict
import all WeilConjectures.AlgebraicGeometry.NonvanishingCommonDegree
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Absolute ampleness after a sufficiently large pullback twist

Source: Stacks Project, Morphisms, Tag 0892, assertion (1)
(blueprint: lem-sfb-relative-ample-absolute-twist).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

/-- Compare the explicit tensor pullback with the usual left adjoint. -/
private noncomputable def pullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ pullback f :=
  (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)

private noncomputable def pullbackPowerIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (n : ℕ) :
    (tensorPullback f).obj (L.tensorPow n) ≅ ((tensorPullback f).obj L).tensorPow n :=
  (pullbackComparison f).app (L.tensorPow n) ≪≫
    (nonempty_pullback_tensorPow_iso f L n).some ≪≫
    (tensorPow_iso ((pullbackComparison f).app L).symm n).some

private theorem nonvanishing_power {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤)) (k : ℕ) (hk : 0 < k) :
    nonvanishingLocus (L.tensorPow k)
      (tensorPowSectionOne (homOfGlobalSection L s) k ⊤) = nonvanishingLocus L s := by
  simpa only [Hom.comp_app, Iso.refl_hom, Hom.id_app, ModuleCat.id_apply, Category.comp_id]
    using nonvanishingLocus_power_transport s k hk (Iso.refl (L.tensorPow k))

private theorem residueValue_restrict {X : Scheme.{u}} (L : X.Modules)
    (s : Γ(L, ⊤)) {U : X.Opens} (x : X) (hx : x ∈ U) :
    residueValue (L.presheaf.map (homOfLE le_top).op s) x hx =
      residueValue s x trivial := by
  unfold residueValue
  rw [TopCat.Presheaf.germ_res_apply]

private theorem residueValue_tensor {X : Scheme.{u}} (L P : X.Modules)
    [L.IsInvertible] [P.IsInvertible] {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(P, U)) (x : X) (hx : x ∈ U) :
    residueValue (tmulSection s t) x hx ≠ 0 ↔
      residueValue s x hx ≠ 0 ∧ residueValue t x hx ≠ 0 := by
  obtain ⟨e, he⟩ := (invertible_pullback_tensor (𝟙 X)).2.2.2.2.2.2.2 L P x
  have hinj : Function.Injective e.hom :=
    (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have hz := map_eq_zero_iff e.hom.hom hinj (x := residueValue (tmulSection s t) x hx)
  refine (not_congr hz).symm.trans ?_
  rw [he U hx s t]
  exact tmul_ne_zero_iff _ _

/-- Tensoring an ample module with an invertible module having nonvanishing
sections through every point preserves ampleness (Stacks, Properties 01PV). -/
private theorem ample_tensor_of_sections {X : Scheme.{u}} (L P : X.Modules)
    [L.IsInvertible] [P.IsInvertible] (hL : IsAmple X L)
    (hP : ∀ x : X, ∃ t : Γ(P, ⊤), x ∈ nonvanishingLocus P t) :
    IsAmple X (L ⊗ P) := by
  refine ⟨hL.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, U, hx, hU, hs⟩ := hL.2 x
  obtain ⟨t, ht⟩ := hP x
  let v := tensorPowSectionOne (homOfGlobalSection P t) n ⊤
  let e := (tensorPowTensorObjIso L P n).symm
  obtain ⟨V, hV, hloc⟩ := (affine_cap_section_open X P t U hU).1
  refine ⟨n, hn, e.hom.app ⊤ (tmulSection s v), V, (hloc x).mpr ⟨hx, ht⟩, hV, ?_⟩
  have hv : nonvanishingLocus (P.tensorPow n) v = nonvanishingLocus P t :=
    nonvanishing_power P t n hn
  have he := nonvanishingLocus_iso e (tmulSection s v)
  rw [nonvanishing_tmul, hv] at he
  intro y
  exact (hloc y).trans ((and_congr_left (fun _ ↦ hs y)).trans
    (Set.ext_iff.mp he y).symm)

private theorem separated_of_relative {Z T : Scheme.{u}} (f : Z ⟶ T)
    (N : Z.Modules) [N.IsInvertible]
    (hN : ∀ V : T.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj N).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj N) h) :
    IsSeparated f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
    (iSup_affineOpens_eq_top T)]
  intro V
  obtain ⟨h, hA⟩ := hN V.1 V.2
  have := isSeparated_of_isAmple _ _ hA
  infer_instance

private theorem residueValue_ne_zero_iff {X : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} (s : Γ(F, U)) (x : X) (hx : x ∈ U) :
    residueValue s x hx ≠ 0 ↔ F.presheaf.germ U x hx s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)) := by
  apply not_congr
  change (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
    F.presheaf.germ U x hx s = 0 ↔ _
  rw [← (TensorProduct.quotTensorEquivQuotSMul
    ↑(F.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).map_eq_zero_iff]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

private theorem local_nonvanishing_restrict {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (s : Γ(F.restrict U.ι, ⊤)) (x : U.toScheme) :
    let t : Γ(F, U) := F.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((F.restrictAppIso U.ι ⊤).hom s)
    residueValue t x.1 x.2 ≠ 0 ↔ x ∈ nonvanishingLocus (F.restrict U.ι) s := by
  dsimp only
  rw [residueValue_ne_zero_iff]
  have h := restrict_stalk_membership U.ι x F
    (TopCat.Presheaf.germ (F.restrict U.ι).val.presheaf ⊤ x trivial s)
  have hg := congrArg (fun t ↦ t s)
    (germ_restrictStalkNatIso_hom_app U.ι x F (U := ⊤) trivial)
  change ((restrictStalkNatIso U.ι x).app F).hom
    (TopCat.Presheaf.germ (F.restrict U.ι).val.presheaf ⊤ x trivial s) =
      F.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι x) ⟨x, trivial, rfl⟩ s at hg
  change _ ∉ _ ↔ _ ∉ _
  apply Iff.symm
  apply not_congr
  refine h.trans ?_
  exact Iff.of_eq (congrArg (fun z ↦ z ∈
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)) •
      (⊤ : Submodule (X.presheaf.stalk x.1) (F.presheaf.stalk x.1)))
        (hg.trans (TopCat.Presheaf.germ_res_apply F.val.presheaf
          (eqToHom U.ι_image_top.symm) x.1 x.2 _).symm))

/-- On an ample restriction, choose an affine nonvanishing neighbourhood whose
section is expressed in the ambient module's sections over the restricting open. -/
private theorem relative_affine_section {X : Scheme.{u}} (N : X.Modules)
    [N.IsInvertible] (U : X.Opens)
    (hA : ∃ h : ((tensorPullback U.ι).obj N).IsInvertible,
      @IsAmple U.toScheme ((tensorPullback U.ι).obj N) h)
    (x : X) (hx : x ∈ U) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(N.tensorPow n, U),
      ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ W ≤ U ∧
        ∀ (y : X) (hy : y ∈ U),
          y ∈ W ↔ residueValue s y hy ≠ 0 := by
  obtain ⟨h, hA⟩ := hA
  obtain ⟨n, hn, s, V, hxV, hV, hs⟩ := hA.2 ⟨x, hx⟩
  let a : ((tensorPullback U.ι).obj N).tensorPow n ≅ (N.tensorPow n).restrict U.ι :=
    (pullbackPowerIso U.ι N n).symm ≪≫
      (pullbackComparison U.ι).app (N.tensorPow n) ≪≫
      ((restrictFunctorIsoPullback U.ι).app (N.tensorPow n)).symm
  let t := a.hom.app ⊤ s
  refine ⟨n, hn,
    (N.tensorPow n).presheaf.map (eqToHom U.ι_image_top.symm).op
      (((N.tensorPow n).restrictAppIso U.ι ⊤).hom t),
    U.ι ''ᵁ V, ?_, hV.image_of_isOpenImmersion U.ι, U.ι_image_le V, ?_⟩
  · exact ⟨⟨x, hx⟩, hxV, rfl⟩
  · intro y hy
    have hh := local_nonvanishing_restrict (N.tensorPow n) U t ⟨y, hy⟩
    dsimp only at hh
    rw [hh]
    change y ∈ U.ι ''ᵁ V ↔ _
    rw [Scheme.Opens.mem_ι_image_iff (x := (⟨y, hy⟩ : U.toScheme))]
    exact (hs ⟨y, hy⟩).trans (Set.ext_iff.mp (nonvanishingLocus_iso a s) ⟨y, hy⟩).symm

/-- Clearing denominators and one further positive power gives the same
nonvanishing locus, now as a section of a globally defined twist. -/
private theorem extend_affine_section {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (L F : X.Modules) [L.IsInvertible] [F.IsInvertible]
    (q : Γ(L, ⊤)) (U W : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus L q) (hW : W ≤ U)
    (s : Γ(F, U))
    (hs : ∀ (x : X) (hx : x ∈ U), x ∈ W ↔ residueValue s x hx ≠ 0) :
    ∃ e : ℕ, ∀ b : ℕ, 0 < b → ∃ t : Γ(F ⊗ L.tensorPow (e + b), ⊤),
      nonvanishingLocus (F ⊗ L.tensorPow (e + b)) t = W := by
  classical
  obtain ⟨e, t, ht⟩ := exists_tensorPowSection_eq_restrict_qcqs L q F U hU s
  refine ⟨e, fun b hb ↦ ?_⟩
  let v := tensorPowSectionOne (homOfGlobalSection L q) b ⊤
  let a := tensorIso (Iso.refl F) (L.tensorPowAddIso e b).symm
  let c := (α_ F (L.tensorPow e) (L.tensorPow b)).hom ≫ a.hom
  refine ⟨c.app ⊤ (tmulSection t v), ?_⟩
  have hc : nonvanishingLocus (F ⊗ L.tensorPow (e + b))
      (c.app ⊤ (tmulSection t v)) =
      nonvanishingLocus (F ⊗ L.tensorPow e) t ∩ nonvanishingLocus L q := by
    change nonvanishingLocus _
      (((α_ F (L.tensorPow e) (L.tensorPow b)) ≪≫ a).hom.app ⊤ (tmulSection t v)) = _
    rw [nonvanishingLocus_iso ((α_ F (L.tensorPow e) (L.tensorPow b)) ≪≫ a),
      nonvanishing_tmul, nonvanishing_power L q b hb]
  rw [hc]
  ext x
  by_cases hx : x ∈ U
  · have hqe : residueValue (tensorPowSectionOne (homOfGlobalSection L q) e U) x hx ≠ 0 := by
      have hgen := isFreeGenerator_generatingLocus q
      have hUle : U ≤ generatingLocus q := by
        intro y hy
        exact (mem_nonvanishingLocus_iff_generatesAt L q y).mp (hU ▸ hy)
      have hgenU : IsFreeGenerator (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op q) := by
        simpa only [presheaf_map_homOfLE_map_homOfLE] using hgen.map hUle
      have hgenU' : IsFreeGenerator ((homOfGlobalSection L q).app U
          (unitSectionsEquiv U 1)) := by
        change IsFreeGenerator ((homOfGlobalSection L q).app U (1 : Γ(X, U)))
        rwa [homOfGlobalSection_app_one]
      have hp := isFreeGenerator_tensorPowSectionOne (homOfGlobalSection L q) hgenU' e
      have htop := (mem_nonvanishingLocus_iff_generatesAt
        (L.tensorPow e) (tensorPowSectionOne (homOfGlobalSection L q) e ⊤) x)
      rw [← presheaf_map_tensorPowSectionOne (homOfGlobalSection L q) e
        (homOfLE (le_top : U ≤ ⊤)), residueValue_restrict]
      apply (nonvanishing_iff_residueValue_ne_zero _ _ x).mp
      apply htop.mpr
      refine ⟨U, hx, ?_⟩
      rw [presheaf_map_tensorPowSectionOne]
      simpa only [homOfGlobalSection_app_one] using hp
    have htt : x ∈ nonvanishingLocus (F ⊗ L.tensorPow e) t ↔ x ∈ W := by
      rw [nonvanishing_iff_residueValue_ne_zero, ← residueValue_restrict _ t x hx,
        ht, residueValue_tensor]
      exact (and_iff_left hqe).trans (hs x hx).symm
    exact (and_iff_left (show x ∈ nonvanishingLocus L q from hU ▸ hx)).trans htt
  · have hq : x ∉ nonvanishingLocus L q := by rwa [← hU]
    simp only [Set.mem_inter_iff, hq, and_false, SetLike.mem_coe]
    exact (iff_false_intro (fun h ↦ hx (hW h))).symm

private theorem relative_local_twist {Z T : Scheme.{u}} [CompactSpace Z]
    [QuasiSeparatedSpace Z] (f : Z ⟶ T) (N : Z.Modules) (M : T.Modules)
    [N.IsInvertible] [M.IsInvertible]
    (hN : ∀ V : T.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj N).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj N) h)
    (hM : IsAmple T M) (x : Z) :
    ∃ m : ℕ, 0 < m ∧ ∃ e : ℕ, ∃ W : Z.Opens, x ∈ W ∧ IsAffineOpen W ∧
      ∀ a : ℕ, m ∣ a → m * (e + 1) ≤ a →
        ∃ n : ℕ, 0 < n ∧
          ∃ s : Γ((N ⊗ (tensorPullback f).obj (M.tensorPow a)).tensorPow n, ⊤),
            nonvanishingLocus ((N ⊗ (tensorPullback f).obj
              (M.tensorPow a)).tensorPow n) s = W := by
  classical
  let B := (tensorPullback f).obj M
  have : B.IsInvertible := bertiniTensorPullback_invertible f M
  obtain ⟨m, hm, t, V, hxV, hV, ht⟩ := hM.2 (f x)
  obtain ⟨q, hq⟩ := exists_tensorPow_section_nonvanishing_pullback f M m hm t
  let U := f ⁻¹ᵁ V
  have hU : (U : Set Z) = nonvanishingLocus (B.tensorPow m) q := by
    rw [hq]
    ext y
    exact ht (f y)
  obtain ⟨n, hn, s, W, hxW, hW, hWU, hs⟩ :=
    relative_affine_section N U (hN V hV) x hxV
  obtain ⟨e, he⟩ := extend_affine_section (B.tensorPow m) (N.tensorPow n)
    q U W hU hWU s hs
  refine ⟨m, hm, e, W, hxW, hW, fun a hma ha ↦ ?_⟩
  let k := a / m
  have hk : e + 1 ≤ k := (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using ha)
  have han : m * (e + (n * k - e)) = a * n := by
    rw [Nat.add_sub_of_le (show e ≤ n * k from
      (show e ≤ k by omega).trans (Nat.le_mul_of_pos_left k hn)),
      ← Nat.mul_assoc, Nat.mul_comm m n, Nat.mul_assoc, Nat.mul_div_cancel' hma]
    exact Nat.mul_comm n a
  obtain ⟨v, hv⟩ := he (n * k - e) (by
    have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    omega)
  have hpa : ((tensorPullback f).obj (M.tensorPow a)).IsInvertible :=
    bertiniTensorPullback_invertible f (M.tensorPow a)
  let j : (B.tensorPow m).tensorPow (e + (n * k - e)) ≅ B.tensorPow (a * n) :=
    (B.tensorPowMulIso m (e + (n * k - e))).symm ≪≫
      eqToIso (congrArg B.tensorPow han)
  let b : B.tensorPow (a * n) ≅ ((tensorPullback f).obj (M.tensorPow a)).tensorPow n :=
    B.tensorPowMulIso a n ≪≫ (tensorPow_iso (pullbackPowerIso f M a).symm n).some
  let c : N.tensorPow n ⊗ (B.tensorPow m).tensorPow (e + (n * k - e)) ≅
      (N ⊗ (tensorPullback f).obj (M.tensorPow a)).tensorPow n :=
    tensorIso (Iso.refl _) (j ≪≫ b) ≪≫ (tensorPowTensorObjIso N _ n).symm
  refine ⟨n, hn, c.hom.app ⊤ v, ?_⟩
  exact (nonvanishingLocus_iso c v).trans hv

private theorem exists_ample_twist {Z T : Scheme.{u}} (f : Z ⟶ T) [QuasiCompact f]
    (N : Z.Modules) (M : T.Modules) [N.IsInvertible] [M.IsInvertible]
    (hN : ∀ V : T.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj N).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj N) h)
    (hM : IsAmple T M) :
    ∃ A : ℕ, ∃ h : (N ⊗ (tensorPullback f).obj (M.tensorPow A)).IsInvertible,
      @IsAmple Z (N ⊗ (tensorPullback f).obj (M.tensorPow A)) h := by
  classical
  have : CompactSpace T := hM.1
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have : T.IsSeparated := isSeparated_of_isAmple T M hM
  have : IsSeparated f := separated_of_relative f N hN
  have : Z.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from f]
    infer_instance⟩
  choose m hm e W hx hW hloc using relative_local_twist f N M hN hM
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set Z))
    (fun x ↦ (W x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let D := ∏ x ∈ s, m x
  let E := ∑ x ∈ s, m x * (e x + 1)
  let A := D * (E + 1)
  have hD : 0 < D := Finset.prod_pos (fun x _ ↦ hm x)
  have hpa : ((tensorPullback f).obj (M.tensorPow A)).IsInvertible :=
    bertiniTensorPullback_invertible f (M.tensorPow A)
  refine ⟨A, inferInstance, ‹CompactSpace Z›, fun z ↦ ?_⟩
  obtain ⟨x, hxs, hzx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
  have hmA : m x ∣ A := dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem m hxs) _
  have hb : m x * (e x + 1) ≤ A := by
    have hE : m x * (e x + 1) ≤ E :=
      Finset.single_le_sum (f := fun x ↦ m x * (e x + 1)) (fun _ _ ↦ Nat.zero_le _) hxs
    have hEA : E + 1 ≤ A := Nat.le_mul_of_pos_left _ hD
    omega
  obtain ⟨n, hn, t, ht⟩ := hloc x A hmA hb
  exact ⟨n, hn, t, W x, hzx, hW x, fun y ↦ (Set.ext_iff.mp ht y).symm⟩

private theorem eventual_pullback_sections {Z T : Scheme.{u}} (f : Z ⟶ T)
    (M : T.Modules) [M.IsInvertible] (hM : IsAmple T M) :
    ∃ K : ℕ, ∀ c : ℕ, K ≤ c → ∀ x : Z,
      ∃ s : Γ((tensorPullback f).obj (M.tensorPow c), ⊤),
        x ∈ nonvanishingLocus ((tensorPullback f).obj (M.tensorPow c)) s := by
  classical
  have : (𝟙_ T.Modules).IsQuasicoherent := inferInstance
  let σ₀ := (SheafOfModules.free.generatingSections
    (R := T.ringCatSheaf) PUnit.{u + 1}).ofEpi (SheafOfModules.freeUniqueIso _).hom
  have : σ₀.IsFiniteType := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
  have hloc : σ₀.localGeneratorsData.IsFiniteType := by
    constructor
    intro i
    change (σ₀.map (SheafOfModules.pushforward (𝟙 (T.ringCatSheaf.over i)))
      (Iso.refl _)).IsFiniteType
    infer_instance
  have : (𝟙_ T.Modules).IsFiniteType := by
    constructor
    exact ⟨σ₀.localGeneratorsData, hloc⟩
  obtain ⟨d, hd⟩ := exists_finite_generatingSections_tensorPow_of_isAmple T M (𝟙_ T.Modules) hM
  refine ⟨d.toNat, fun c hc x ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := hd c (by omega)
  let τ := σ.ofEpi (λ_ (M.tensorPow c)).hom
  have hcover := globalGeneration_nonvanishing_cover T (M.tensorPow c) ⟨τ⟩
  have hx : f x ∈ ⋃ s : Γ(M.tensorPow c, ⊤), nonvanishingLocus (M.tensorPow c) s := by
    exact hcover.symm ▸ Set.mem_univ (f x)
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  refine ⟨((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
    (M.tensorPow c)).val.app (op ⊤) s, ?_⟩
  exact (nonvanishing_tensorPullback f (M.tensorPow c) s x).mpr hs

private noncomputable def twistAddIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    (N : Z.Modules) (M : T.Modules) (a c : ℕ) :
    (N ⊗ (tensorPullback f).obj (M.tensorPow a)) ⊗
      (tensorPullback f).obj (M.tensorPow c) ≅
        N ⊗ (tensorPullback f).obj (M.tensorPow (a + c)) :=
  (α_ _ _ _) ≪≫ tensorIso (Iso.refl N)
    (tensorIso ((pullbackComparison f).app (M.tensorPow a))
        ((pullbackComparison f).app (M.tensorPow c)) ≪≫
      (nonempty_pullback_tensorObj_iso f (M.tensorPow a) (M.tensorPow c)).some.symm ≪≫
      (pullback f).mapIso (M.tensorPowAddIso a c).symm ≪≫
      ((pullbackComparison f).app (M.tensorPow (a + c))).symm)

/-- A relatively ample invertible module becomes absolutely ample after twisting by
all sufficiently large powers of the pullback of an ample invertible module.
The integer exponent is nonnegative under the displayed bound, so `a.toNat` is
exactly that exponent in the existing natural-number tensor-power construction.
Existential invertibility witnesses supply only the proof argument of `IsAmple`.

Source: Stacks Project, Morphisms, Tag 0892, assertion (1)
(blueprint: lem-sfb-relative-ample-absolute-twist).

Proof:
1. Compare tensor pullback with the usual pullback by uniqueness of left adjoints.
   This gives invertibility and the tensor-power and tensor-product comparisons.
   Ampleness of M gives compactness and separatedness of T. Over each affine V,
   ampleness of N on its preimage makes that preimage separated. Separatedness is
   local on the target, so f is separated and Z is separated and quasi-compact.
2. At x choose a section t of M^m, m > 0, whose affine nonvanishing open V contains
   f(x). Pulling t back gives q of (f^*M)^m with locus U = f^-1(V). Relative
   ampleness gives n > 0 and a section s of N^n on U with affine locus W containing x.
   The restriction and tensor-power comparisons identify this with ambient sections.
3. Clear denominators on the qcqs scheme Z: a section t' of N^n tensor ((f^*M)^m)^e
   restricts to s tensor q^e. Multiply t' by q^b for any b > 0. The locus is exactly W:
   outside U the positive power vanishes; on U, q and all its powers generate their
   invertible modules, so the product is nonzero precisely where s is nonzero.
4. For m dividing a and a >= m(e+1), set k = a/m and b = nk-e > 0. Then
   m(e+b) = an. Tensor-power comparisons turn the previous section into a section
   of (N tensor f^*(M^a))^n, retaining the fixed affine locus W. Compactness gives
   finitely many such W. Put D equal to the product of their positive m's, E equal
   to the sum of their bounds m(e+1), and A = D(E+1). Each local construction applies
   to A, proving ampleness of N tensor f^*(M^A). An empty finite cover also works.
5. Apply eventual global generation to O_T tensor M^c. The structure module is
   quasi-coherent and is generated by one section; its finite local generators are
   obtained by restricting this generating family. The left unitor transports the
   resulting generators to M^c. The global-generation nonvanishing cover and the
   pullback fibre formula give sections of f^*(M^c) through every point for c >= K.
6. Tensoring an ample invertible module L with an invertible module P having such
   sections preserves ampleness: through x choose an affine section locus of L^n
   and a section w of P nonvanishing at x. The tensor of the first section with w^n
   has the intersection as its locus. This intersection is affine by 01PV. Apply
   this to L = N tensor f^*(M^A), P = f^*(M^c), and transport along the tensor
   comparison to N tensor f^*(M^(A+c)). The bound A+K gives the required integer
   tail; nonnegativity justifies the natural exponents. -/
theorem isAmple_tensorPullback_tensorPow_of_relative
    {Z T : Scheme.{u}} (f : Z ⟶ T) [QuasiCompact f]
    (N : Z.Modules) (M : T.Modules) [N.IsInvertible] [M.IsInvertible]
    (hN : ∀ V : T.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj N).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj N) h)
    (hM : IsAmple T M) :
    ∃ a₀ : ℤ, 0 ≤ a₀ ∧ ∀ a : ℤ, a₀ ≤ a →
      ∃ h : (tensorObj N ((tensorPullback f).obj (M.tensorPow a.toNat))).IsInvertible,
        @IsAmple Z (tensorObj N ((tensorPullback f).obj (M.tensorPow a.toNat))) h := by
  classical
  obtain ⟨A, hA, hample⟩ := exists_ample_twist f N M hN hM
  obtain ⟨K, hK⟩ := eventual_pullback_sections f M hM
  refine ⟨(A + K : ℕ), by omega, fun a ha ↦ ?_⟩
  have haa : A + K ≤ a.toNat := by omega
  have hsum : A + (a.toNat - A) = a.toNat := by omega
  have hp : ((tensorPullback f).obj (M.tensorPow (a.toNat - A))).IsInvertible :=
    bertiniTensorPullback_invertible f (M.tensorPow (a.toNat - A))
  have htail := ample_tensor_of_sections _ _ hample
    (hK (a.toNat - A) (by omega))
  have hpa : ((tensorPullback f).obj (M.tensorPow a.toNat)).IsInvertible :=
    bertiniTensorPullback_invertible f (M.tensorPow a.toNat)
  refine ⟨inferInstance, ?_⟩
  let e := twistAddIso f N M A (a.toNat - A) ≪≫
    tensorIso (Iso.refl N) ((tensorPullback f).mapIso
      (eqToIso (congrArg M.tensorPow hsum)))
  exact (isAmple_iff_of_iso e).mp htail

end AlgebraicGeometry.Scheme.Modules
