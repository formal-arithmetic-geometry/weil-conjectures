/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.AdicReductionTriangle
import all Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The cohomology sequence for a completed DVR quotient

Source: blueprint integral truncations, hypothesis paragraph, and the quotient-resolution
argument in steps 1 and 3 of lem-weil-pbc-adic-tor-flat-cohomology.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem uniformizer_ne_zero (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let A := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing A := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
    (hm.symm.trans hgen.symm)).ne_zero

private theorem principal_scalar_sequence {A : Type*} [CommRing A] [IsDomain A]
    (a : A) (ha : a ≠ 0) :
    let μ := ModuleCat.ofHom (LinearMap.mulLeft A a)
    let p := ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (Ideal.span {a})).toLinearMap)
    ∃ h : μ ≫ p = 0, (ShortComplex.mk μ p h).ShortExact := by
  dsimp only
  have h : ModuleCat.ofHom (LinearMap.mulLeft A a) ≫
      ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (Ideal.span {a})).toLinearMap) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk (Ideal.span {a}) (a * x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a)))
  refine ⟨h, ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_⟩
  · intro x
    change Ideal.Quotient.mk (Ideal.span {a}) x = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
  · intro x y hxy
    exact mul_left_cancel₀ ha hxy
  · exact Ideal.Quotient.mk_surjective

private abbrev constantPresheaves (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantGenerator (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (M : ModuleCat.{u + 1} A) (U : T.ProEtᵒᵖ) (x : M) :
    ((adicLisseConstantModules T A).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (adicLisseConstantUnit T A)).unit.app ((constantPresheaves T A).obj M)).app U x

private theorem constantGenerator_naturality (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] {M N : ModuleCat.{u + 1} A} (g : M ⟶ N)
    (U : T.ProEtᵒᵖ) (x : M) :
    ((adicLisseConstantModules T A).map g).val.app U (constantGenerator T M U x) =
      constantGenerator T N U (g x) := by
  exact (congrArg (fun k ↦ k.app U x)
    ((PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit T A)).unit.naturality
      ((constantPresheaves T A).map g))).symm

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private theorem constant_unit_inv_one (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (c : adicLisseConstantRing T A ⟶ S) (U : T.ProEtᵒᵖ) :
    (CompletedConstantReduction.constantChange_unit T c).inv.val.app U (1 : S.obj.obj U) =
      completedAdicChangeTensor T c ((adicLisseConstantModules T A).obj (ModuleCat.of A A))
        U 1 (constantGenerator T (ModuleCat.of A A) U 1) := by
  unfold CompletedConstantReduction.constantChange_unit
  simp only [Iso.trans_inv, eqToIso.inv, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (eqToHom ((completedAdicChangeData T c).choose_spec.choose
    ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).symm).val.app U
      ((1 : S.obj.obj U) •
        (show (SheafOfModules.changeOfRings c
          ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).val.obj U from
        ((toSheafify (ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf c
            ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).presheaf).app U
              ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
                (c.hom.app U).hom] (constantGenerator T (ModuleCat.of A A) U 1))))) = _
  exact congrArg ((eqToHom ((completedAdicChangeData T c).choose_spec.choose
    ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).symm).val.app U)
      (one_smul (S.obj.obj U)
        (show (SheafOfModules.changeOfRings c
          ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).val.obj U from
          (toSheafify (ProEt.topology T)
            (SheafOfModules.changeOfRingsPresheaf c
              ((adicLisseConstantModules T A).obj (ModuleCat.of A A))).presheaf).app U
                ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
                  (c.hom.app U).hom] (constantGenerator T (ModuleCat.of A A) U 1))))

set_option backward.isDefEq.respectTransparency false in
private theorem completed_map_tensor_one (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : pbcModules T R} (g : M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedAdicChange T φ).map g).val.app U
        (completedAdicChangeTensor T φ M U 1 x) =
      completedAdicChangeTensor T φ N U 1 (g.val.app U x) := by
  have h := congrArg (fun k ↦ k.val.app U x) ((pbcScalarAdjunction φ).unit.naturality g)
  change ((pbcScalarAdjunction φ).unit.app N).val.app U (g.val.app U x) =
    ((completedAdicChange T φ).map g).val.app U
      (((pbcScalarAdjunction φ).unit.app M).val.app U x) at h
  have hM : ((pbcScalarAdjunction φ).unit.app M).val.app U x =
      completedAdicChangeTensor T φ M U 1 x :=
    (pbcScalarAdjunction_exists φ).exists.choose_spec M U x
  have hN : ((pbcScalarAdjunction φ).unit.app N).val.app U (g.val.app U x) =
      completedAdicChangeTensor T φ N U 1 (g.val.app U x) :=
    (pbcScalarAdjunction_exists φ).exists.choose_spec N U (g.val.app U x)
  exact (congrArg (fun y ↦ ((completedAdicChange T φ).map g).val.app U y) hM.symm).trans
    (h.symm.trans hN)

set_option backward.isDefEq.respectTransparency false in
private theorem coefficient_resolution
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    let d := pbcPadicCoefficientDatum l E
    let c := CompletedConstantReduction.base T d.ideal ≫
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
    let F := adicLisseConstantModules T (Padic.coefficientExtensionIntegers l E) ⋙
      completedAdicChange T c
    let e := CompletedConstantReduction.constantChange_unit T c
    let f := e.inv ≫ F.map (ModuleCat.ofHom
      (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))) ≫ e.hom
    ∃ p : SheafOfModules.unit ((adicLisseForget T).obj (pbcAdicCompletion T d)) ⟶
        (pbcRestrict (pbcAdicProjection T d n)).obj
          (SheafOfModules.unit ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))),
      ∃ h : f ≫ p = 0, (ShortComplex.mk f p h).ShortExact ∧
        ∀ U : T.ProEtᵒᵖ, p.val.app U (1 : (pbcAdicCompletion T d).obj.obj U) =
          (1 : ((pbcAdicRings T d).obj (op n)).obj.obj U) := by
  let A := Padic.coefficientExtensionIntegers l E
  let d := pbcPadicCoefficientDatum l E
  let c := CompletedConstantReduction.base T d.ideal ≫
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let F := adicLisseConstantModules T A ⋙ completedAdicChange T c
  let e := CompletedConstantReduction.constantChange_unit T c
  let : IsNoetherianRing A := d.noetherian
  have hfin := CompletedConstantReduction.finite_coefficient_identification
    T d.ideal d.quotientFinite
  have hc : IsIso (CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite) :=
    hfin.2.1
  have hh := completed_constant_algebra_flat_quotients T d.ideal _
    (asIso (CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite)) c
    (fun n ↦ by
      dsimp only [c]
      simp only [asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
      exact (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 n)
  let := (exactFunctor_iff (completedAdicChange T c)).1 hh.2.1 |>.1
  let := (exactFunctor_iff (completedAdicChange T c)).1 hh.2.1 |>.2
  let := (CompletedConstantReduction.constant_exact T A).1
  let := (CompletedConstantReduction.constant_exact T A).2
  let := CompletedConstantReduction.constant_additive T A
  let a := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  have hI : Ideal.span {a} = d.ideal ^ (n + 1) :=
    (Ideal.span_singleton_pow _ _).symm
  let μ := ModuleCat.ofHom (LinearMap.mulLeft A a)
  let p₀ := ModuleCat.ofHom ((Ideal.Quotient.mkₐ A (d.ideal ^ (n + 1))).toLinearMap)
  obtain ⟨hw, hs⟩ : ∃ h : μ ≫ p₀ = 0, (ShortComplex.mk μ p₀ h).ShortExact := by
    dsimp only [μ, p₀]
    rw [← hI]
    exact principal_scalar_sequence a (pow_ne_zero _ (uniformizer_ne_zero l E))
  let r := CompletedConstantReduction.finiteReduction T d.ideal d.quotientFinite n
  have hr : IsIso r := hfin.2.2.1 n
  let eR := asIso r
  let p := e.inv ≫ F.map p₀ ≫ eR.hom
  have hp : (e.inv ≫ F.map μ ≫ e.hom) ≫ p = 0 := by
    simp only [p, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, hw,
      Functor.map_zero, zero_comp, comp_zero]
  refine ⟨p, hp, ?_, ?_⟩
  · let i : ((ShortComplex.mk μ p₀ hw).map F) ≅
        ShortComplex.mk (e.inv ≫ F.map μ ≫ e.hom) p hp :=
      ShortComplex.isoMk e e eR (by simp) (by simp [p])
    exact ShortComplex.shortExact_of_iso i (hs.map_of_exact F)
  · intro U
    change r.val.app U
      (((completedAdicChange T c).map ((adicLisseConstantModules T A).map p₀)).val.app U
        ((CompletedConstantReduction.constantChange_unit T c).inv.val.app U
          (1 : (pbcAdicCompletion T d).obj.obj U))) =
        (1 : ((pbcAdicRings T d).obj (op n)).obj.obj U)
    rw [constant_unit_inv_one, completed_map_tensor_one, constantGenerator_naturality]
    change r.val.app U (completedAdicChangeTensor T c _ U 1
      (constantGenerator T (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) U 1)) =
        (1 : ((pbcAdicRings T d).obj (op n)).obj.obj U)
    have hraw : constantGenerator T (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1))) U 1 =
        (toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ModuleCat.of A (A ⧸ d.ideal ^ (n + 1)))))).app U
              (1 : A ⧸ d.ideal ^ (n + 1)) := rfl
    rw [hraw]
    exact ((CompletedConstantReduction.finiteReduction_exists T d.ideal
      d.quotientFinite n).choose_spec.1 U 1 1).trans (by
        simp only [id_eq, map_one, one_mul])

private theorem exact_transport
    {C : Type*} [Category C] [Abelian C]
    {X Y Z X' Y' Z' : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (a' : X' ⟶ Y') (b' : Y' ⟶ Z') (h : a ≫ b = 0) (h' : a' ≫ b' = 0)
    (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z')
    (ha : eX.hom ≫ a' = a ≫ eY.hom)
    (hb : eY.hom ≫ b' = b ≫ eZ.hom)
    (hex : (ShortComplex.mk a b h).Exact) :
    (ShortComplex.mk a' b' h').Exact := by
  let g : (ShortComplex.mk a b h) ⟶ (ShortComplex.mk a' b' h') :=
    { τ₁ := eX.hom
      τ₂ := eY.hom
      τ₃ := eZ.hom
      comm₁₂ := ha
      comm₂₃ := hb }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono g).mp hex

private theorem exact_cokernel_kernel
    {C : Type*} [Category C] [Abelian C]
    {X Y Z V : C} (a : X ⟶ X) (u : X ⟶ Y) (b : Y ⟶ Z) (t : Z ⟶ Z)
    (c : V ⟶ Y) (h₁ : a ≫ u = 0) (h₂ : u ≫ b = 0) (h₃ : b ≫ t = 0)
    (hex₁ : (ShortComplex.mk a u h₁).Exact)
    (hex₂ : (ShortComplex.mk u b h₂).Exact)
    (hex₃ : (ShortComplex.mk b t h₃).Exact)
    (e : cokernel a ≅ V) (he : cokernel.π a ≫ e.hom ≫ c = u) :
    ∃ (δ : Y ⟶ kernel t) (h : c ≫ δ = 0),
      (ShortComplex.mk c δ h).ShortExact := by
  let δ := kernel.lift t b h₃
  have hcb : c ≫ b = 0 := by
    apply (cancel_epi (cokernel.π a ≫ e.hom)).mp
    calc
      (cokernel.π a ≫ e.hom) ≫ c ≫ b =
          (cokernel.π a ≫ e.hom ≫ c) ≫ b := by simp only [Category.assoc]
      _ = u ≫ b := by rw [he]
      _ = (cokernel.π a ≫ e.hom) ≫ 0 := by rw [h₂, comp_zero]
  have h : c ≫ δ = 0 := by
    apply (cancel_mono (kernel.ι t)).mp
    simpa only [Category.assoc, δ, kernel.lift_ι, zero_comp] using hcb
  have hc : c = e.inv ≫ cokernel.desc a u h₁ := by
    apply (cancel_epi (cokernel.π a ≫ e.hom)).mp
    simp only [Category.assoc, he, Iso.hom_inv_id_assoc, cokernel.π_desc]
  have : Mono (cokernel.desc a u h₁) := hex₁.mono_cokernelDesc
  have hm : Mono c := by rw [hc]; infer_instance
  have hd : Epi δ := hex₃.epi_kernelLift
  let S := ShortComplex.mk c b hcb
  have hs : S.Exact := by
    let g : (ShortComplex.mk u b h₂) ⟶ S :=
      { τ₁ := cokernel.π a ≫ e.hom
        τ₂ := 𝟙 Y
        τ₃ := 𝟙 Z
        comm₁₂ := by simpa only [S, Category.assoc, Category.comp_id] using he
        comm₂₃ := by simp [S] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono g).mp hex₂
  let g : (ShortComplex.mk c δ h) ⟶ S :=
    { τ₁ := 𝟙 V
      τ₂ := 𝟙 Y
      τ₃ := kernel.ι t
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [δ, S] }
  exact ⟨δ, h, ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono g).mpr hs) hm hd⟩

private theorem reduction_triangle_sequence
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (n : ℕ)
    (f : SheafOfModules.unit ((adicLisseForget T).obj (pbcAdicCompletion T d)) ⟶
      SheafOfModules.unit ((adicLisseForget T).obj (pbcAdicCompletion T d)))
    (K : PbcCompletedDerived T d) (a : K ⟶ K)
    (w : (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
      ((pbcDerivedExtend (pbcAdicProjection T d n)).obj K) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk a
      ((pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app K) w ∈ distTriang _)
    (hcoh : ∀ q : ℤ,
      let H := (DerivedCategory.homologyFunctor _ q).obj K
      (∃ e : H ≅ (SheafOfModules.siteSheafTensorRight
          (J := ProEt.topology T) (A := pbcAdicCompletion T d) H).obj
            (SheafOfModules.unit ((adicLisseForget T).obj (pbcAdicCompletion T d))),
        (DerivedCategory.homologyFunctor _ q).map a ≫ e.hom =
          e.hom ≫ (SheafOfModules.siteSheafTensorRight
            (J := ProEt.topology T) (A := pbcAdicCompletion T d) H).map f) ∧
      ∃ e : cokernel ((DerivedCategory.homologyFunctor _ q).map a) ≅
          (pbcRestrict (pbcAdicProjection T d n)).obj
            ((pbcExtend (pbcAdicProjection T d n)).obj H),
        cokernel.π ((DerivedCategory.homologyFunctor _ q).map a) ≫ e.hom =
          (pbcScalarAdjunction (pbcAdicProjection T d n)).unit.app H)
    (q : ℤ) :
    let φ := pbcAdicProjection T d n
    let H := (DerivedCategory.homologyFunctor _ (q + 1)).obj K
    let c := ((pbcScalarAdjunction φ).homEquiv _ _).symm
      ((DerivedCategory.homologyFunctor _ q).map
          ((pbcDerivedScalarAdjunction φ).unit.app K) ≫
        ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).inv.app
          ((pbcDerivedExtend φ).obj K))
    ∃ δ : (pbcRestrict φ).obj
        ((DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K)) ⟶
        kernel ((SheafOfModules.siteSheafTensorRight
          (J := ProEt.topology T) (A := pbcAdicCompletion T d) H).map f),
      ∃ h : (pbcRestrict φ).map c ≫ δ = 0,
        (ShortComplex.mk ((pbcRestrict φ).map c) δ h).ShortExact := by
  classical
  dsimp only
  let triangle := Pretriangulated.Triangle.mk a
    ((pbcDerivedScalarAdjunction
      (pbcAdicProjection T (d) n)).unit.app K) w
  let φ := pbcAdicProjection T (d) n
  let F := DerivedCategory.homologyFunctor (pbcModules T
    (pbcAdicCompletion T (d))) q
  let F' := DerivedCategory.homologyFunctor (pbcModules T
    (pbcAdicCompletion T (d))) (q + 1)
  let j := ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).app
    ((pbcDerivedExtend φ).obj K)
  obtain ⟨⟨e, he⟩, _⟩ := hcoh (q + 1)
  obtain ⟨_, eC, heC⟩ := hcoh q
  let boundary := DerivedCategory.HomologySequence.δ triangle q (q + 1) rfl
  let b := j.hom ≫ boundary ≫ e.hom
  let u := F.map triangle.mor₂ ≫ j.inv
  let t := (SheafOfModules.siteSheafTensorRight
    (J := ProEt.topology T) (A := pbcAdicCompletion T (d))
    (F'.obj K)).map f
  have h₁ : F.map a ≫ u = 0 := by
    have hz := Pretriangulated.comp_distTriang_mor_zero₁₂ triangle hT
    change a ≫ triangle.mor₂ = 0 at hz
    dsimp only [u]
    rw [← Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, zero_comp]
  have h₂ : u ≫ b = 0 := by
    dsimp [u, b]
    simp only [Category.assoc, j.inv_hom_id_assoc]
    simpa only [F, boundary, zero_comp] using
      DerivedCategory.HomologySequence.comp_δ_assoc triangle hT q (q + 1) rfl e.hom
  have h₃ : b ≫ t = 0 := by
    dsimp [b, t]
    rw [Category.assoc, Category.assoc, ← he, ← Category.assoc boundary]
    have hd := DerivedCategory.HomologySequence.δ_comp triangle hT q (q + 1) rfl
    change boundary ≫ F'.map a = 0 at hd
    change j.hom ≫ (boundary ≫ F'.map a) ≫ e.hom = 0
    rw [hd, zero_comp, comp_zero]
  have hx₁ : (ShortComplex.mk (F.map a) u h₁).Exact := by
    apply exact_transport (F.map triangle.mor₁) (F.map triangle.mor₂) _ _ _ h₁
      (Iso.refl _) (Iso.refl _) j.symm
      (by simp [triangle]) (by simp [u])
    exact DerivedCategory.HomologySequence.exact₂ triangle hT q
  have hx₂ : (ShortComplex.mk u b h₂).Exact := by
    apply exact_transport (F.map triangle.mor₂) boundary _ _ _ h₂ (Iso.refl _) j.symm e
      (by simp [u]) (by simp [b])
    exact DerivedCategory.HomologySequence.exact₃ triangle hT q (q + 1) rfl
  have hx₃ : (ShortComplex.mk b t h₃).Exact := by
    apply exact_transport boundary (F'.map triangle.mor₁) _ _ _ h₃ j.symm e e
      (by simp [b]) (by
        change e.hom ≫ t = F'.map a ≫ e.hom
        exact he.symm)
    exact DerivedCategory.HomologySequence.exact₁ triangle hT q (q + 1) rfl
  apply exact_cokernel_kernel (F.map a) u b t _ h₁ h₂ h₃ hx₁ hx₂ hx₃ eC
  rw [← Category.assoc, heC]
  rw [← (pbcScalarAdjunction φ).homEquiv_unit]
  exact Equiv.apply_symm_apply _ _


/-- The universal-coefficient short exact sequence for the completed DVR coefficient
quotient. No flatness or bounded constructibility of the complex is assumed. The
endomorphism is multiplication by a uniformizer to the power n+1 on the unit module;
the existential formulation avoids choosing a uniformizer in downstream definitions.
Its monicity is independent of the complex. The first arrow is the scalar restriction
of the homology adjunct of the normalized derived unit.

Source: blueprint integral truncations, hypothesis paragraph; steps 1 and 3 of
lem-weil-pbc-adic-tor-flat-cohomology; Stacks Project, Tags 06YY and 03EK.
(blueprint: lem-weil-pbc-adic-reduction-cohomology-sequence).

Proof: choose a uniformizer of the finite extension's integer DVR. Flatness of its
completed constant coefficient sheaf, and the completed finite-quotient comparison,
give the exact two-term resolution B --varpi^(n+1)--> B of R_n. In particular its
first map f is monic. Tensor this resolution with a K-flat representative of K.
Its cone computes restriction of the derived quotient extension. The long exact
cohomology sequence gives a short exact sequence from the cokernel of multiplication
on H^q(K) to reduced H^q(K), followed by its connecting epimorphism onto the kernel
of multiplication on H^(q+1)(K). Right exactness of ordinary scalar extension
identifies that cokernel with restricted ordinary extension of H^q(K). The unit
normalization of both scalar adjunctions identifies this injection with the displayed
adjunct: on cocycles it sends z to z tensor 1. Tensoring the unit endomorphism f
with H^(q+1)(K) is its multiplication map, giving precisely the kernel displayed.
The argument works in every degree and for the zero and empty-site cases. -/
theorem pbc_adic_reduction_cohomology_sequence
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    let d := pbcPadicCoefficientDatum l E
    let B := pbcAdicCompletion T d
    let φ := pbcAdicProjection T d n
    let O := SheafOfModules.unit ((adicLisseForget T).obj B)
    ∃ f : O ⟶ O, Mono f ∧
      ∀ (K : PbcCompletedDerived T d) (q : ℤ),
        let H := (DerivedCategory.homologyFunctor _ (q + 1)).obj K
        let c := ((pbcScalarAdjunction φ).homEquiv _ _).symm
          ((DerivedCategory.homologyFunctor _ q).map
              ((pbcDerivedScalarAdjunction φ).unit.app K) ≫
            ((pbcRestrict φ).mapDerivedCategoryHomologyFunctorIso q).inv.app
              ((pbcDerivedExtend φ).obj K))
        ∃ δ : (pbcRestrict φ).obj
            ((DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K)) ⟶
            kernel ((SheafOfModules.siteSheafTensorRight
              (J := ProEt.topology T) (A := B) H).map f),
          ∃ h : (pbcRestrict φ).map c ≫ δ = 0,
            (ShortComplex.mk ((pbcRestrict φ).map c) δ h).ShortExact := by
  classical
  dsimp
  let d := pbcPadicCoefficientDatum l E
  let c := CompletedConstantReduction.base T d.ideal ≫
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let F₀ := adicLisseConstantModules T (Padic.coefficientExtensionIntegers l E) ⋙
    completedAdicChange T c
  let e₀ := CompletedConstantReduction.constantChange_unit T c
  let f := e₀.inv ≫ F₀.map (ModuleCat.ofHom
    (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))) ≫ e₀.hom
  obtain ⟨p, hp, hs, hpone⟩ := coefficient_resolution T l E n
  have hf : Mono f := hs.mono_f
  have hcore := pbc_adic_reduction_triangle T
    (pbcAdicProjection T d n) f p hpone hp hs
  refine ⟨f, hf, ?_⟩
  intro K q
  obtain ⟨a, w, hT, hcoh⟩ := hcore K
  clear hcore hs hp hpone p hf
  exact reduction_triangle_sequence T d n f K a w hT hcoh q

end AlgebraicGeometry.Scheme
