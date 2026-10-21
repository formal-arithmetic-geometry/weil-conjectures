/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Normalized finite free scalar models

Source: Stacks Project, sites-modules.tex, Tags 03CY, 03EK and 0GMW.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v s
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{s} C]
  (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{s}] [HasSheafify J AddCommGrpCat.{s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  (R : Type s) [CommRing R]

private def constantUnitRaw :
    (scalarPerfectConstantPresheaf (C := C) R).obj (ModuleCat.of R R) ⟶
      (PresheafOfModules.restrictScalars (scalarPerfectRingUnit J R)).obj
        (unit (scalarPerfectRingUnderlying J (scalarPerfectRing J R))).val where
  app W := ModuleCat.ofHom (X := ModuleCat.of R R)
    (Y := ((PresheafOfModules.restrictScalars (scalarPerfectRingUnit J R)).obj
      (unit (scalarPerfectRingUnderlying J (scalarPerfectRing J R))).val).obj W)
    { toFun := (scalarPerfectRingUnit J R).app W
      map_add' := map_add _
      map_smul' := by
        intro a b
        change (scalarPerfectRingUnit J R).app W (a * b) =
          (scalarPerfectRingUnit J R).app W a * (scalarPerfectRingUnit J R).app W b
        exact map_mul _ a b }
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (ConcreteCategory.congr_hom ((scalarPerfectRingUnit J R).naturality f) x)

private def constantUnitHom :
    (scalarPerfectConstantFunctor J R).obj (ModuleCat.of R R) ⟶
      unit (scalarPerfectRingUnderlying J (scalarPerfectRing J R)) :=
  letI := (scalarPerfectRingUnit_locallyBijective J R).1
  letI := (scalarPerfectRingUnit_locallyBijective J R).2
  (PresheafOfModules.sheafificationHomEquiv (scalarPerfectRingUnit J R)).symm
    (constantUnitRaw J R)

private theorem constantUnitHom_section (W : Cᵒᵖ) (x : R) :
    (constantUnitHom J R).val.app W (scalarPerfectConstantSection J R
      (ModuleCat.of R R) W x) = (scalarPerfectRingUnit J R).app W x := by
  have := (scalarPerfectRingUnit_locallyBijective J R).1
  have := (scalarPerfectRingUnit_locallyBijective J R).2
  have h := (PresheafOfModules.sheafificationHomEquiv (scalarPerfectRingUnit J R)
    (P := (scalarPerfectConstantPresheaf (C := C) R).obj (ModuleCat.of R R))
    (F := unit (scalarPerfectRingUnderlying J (scalarPerfectRing J R)))).apply_symm_apply
    (constantUnitRaw J R)
  exact congrArg (fun f ↦ f.app W x) h

private theorem constantUnitHom_isIso : IsIso (constantUnitHom J R) := by
  let A := scalarPerfectRingUnderlying J (scalarPerfectRing J R)
  let u := CategoryTheory.toSheafify J
    (((scalarPerfectConstantPresheaf (C := C) R).obj (ModuleCat.of R R)).presheaf)
  let f := (toSheaf A).map (constantUnitHom J R)
  have h : u ≫ f.hom =
      Functor.whiskerRight (scalarPerfectRingUnit J R) (forget₂ RingCat AddCommGrpCat) := by
    ext W x
    exact constantUnitHom_section J R W x
  have hli : Presheaf.IsLocallyInjective J (u ≫ f.hom) := by
    rw [h]
    exact ⟨fun x y hxy ↦
      (scalarPerfectRingUnit_locallyBijective J R).1.equalizerSieve_mem x y hxy⟩
  have hls : Presheaf.IsLocallySurjective J (u ≫ f.hom) := by
    rw [h]
    exact ⟨fun x ↦
      (scalarPerfectRingUnit_locallyBijective J R).2.imageSieve_mem x⟩
  have : Presheaf.IsLocallyInjective J f.hom :=
    (Presheaf.comp_isLocallyInjective_iff J u f.hom).mp hli
  have : Presheaf.IsLocallySurjective J f.hom :=
    (Presheaf.comp_isLocallySurjective_iff J u f.hom).mp hls
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso (constantUnitHom J R) (toSheaf A)



variable [∀ U : C, EssentiallySmall.{s} (Over U)]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{s}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{s}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{s}]
  {B : Sheaf J CommRingCat.{s}} (φ : scalarPerfectRing J R ⟶ B)

private def chartUnitIso (U : C) :
    (scalarPerfectChartFunctor J R φ U).obj (ModuleCat.of R R) ≅
      unit ((scalarPerfectRingUnderlying J B).over U) := by
  have := constantUnitHom_isIso J R
  exact (scalarPerfectExtensionFunctor.{max c v, v, s} (J.over U)
      ((J.overPullback CommRingCat.{s} U).map φ)).mapIso
      ((overFunctor (scalarPerfectRingUnderlying J (scalarPerfectRing J R)) U).mapIso
        (asIso (constantUnitHom J R))) ≪≫
    scalarExtensionUnitIso.{max c v, v, s} ((J.overPullback CommRingCat.{s} U).map φ)

omit [∀ U : C, HasSheafify (J.over U) CommRingCat.{s}] in
private theorem chartUnitIso_section (U : C) (W : (Over U)ᵒᵖ)
    (b : B.obj.obj (Opposite.op W.unop.left)) (x : R) :
    (chartUnitIso J R φ U).hom.val.app W
      (scalarPerfectChartSection J R φ U (ModuleCat.of R R) W b x) =
      b * φ.hom.app (Opposite.op W.unop.left)
        ((scalarPerfectRingUnit J R).app (Opposite.op W.unop.left) x) := by
  change (scalarExtensionUnitIso.{max c v, v, s}
    ((J.overPullback CommRingCat.{s} U).map φ)).hom.val.app W
    ((changeOfRingsHomOfUniverses.{v, max c v, s, s}
      ((J.overPullback CommRingCat.{s} U).map φ)
      (((scalarPerfectConstantFunctor J R).obj (ModuleCat.of R R)).over U)
      ((constantUnitHom J R).over U)).val.app W
      (scalarExtensionSection.{max c v, v, s, s} _ _ W b
        (scalarPerfectConstantSection J R (ModuleCat.of R R)
          (Opposite.op W.unop.left) x))) = _
  rw [scalarExtension_map_tmul.{max c v, v, s, s}]
  have h := scalarExtensionUnitIso_tmul.{max c v, v, s}
    ((J.overPullback CommRingCat.{s} U).map φ) W b
    ((constantUnitHom J R).val.app (Opposite.op W.unop.left)
      (scalarPerfectConstantSection J R (ModuleCat.of R R)
        (Opposite.op W.unop.left) x))
  exact h.trans (congrArg (fun y ↦ b * φ.hom.app (Opposite.op W.unop.left) y)
    (constantUnitHom_section J R (Opposite.op W.unop.left) x))

omit [∀ U : C, HasSheafify (J.over U) CommRingCat.{s}] in
private theorem chart_map_section (U : C) {M N : ModuleCat.{s} R} (f : M ⟶ N)
    (W : (Over U)ᵒᵖ) (b : B.obj.obj (Opposite.op W.unop.left)) (x : M) :
    ((scalarPerfectChartFunctor J R φ U).map f).val.app W
      (scalarPerfectChartSection J R φ U M W b x) =
      scalarPerfectChartSection J R φ U N W b (f x) := by
  change (changeOfRingsHomOfUniverses.{v, max c v, s, s}
    ((J.overPullback CommRingCat.{s} U).map φ)
    (((scalarPerfectConstantFunctor J R).obj M).over U)
    (((scalarPerfectConstantFunctor J R).map f).over U)).val.app W
    (scalarExtensionSection.{max c v, v, s, s} _ _ W b _) = _
  rw [scalarExtension_map_tmul.{max c v, v, s, s}]
  congr 1
  have := (scalarPerfectRingUnit_locallyBijective J R).1
  have := (scalarPerfectRingUnit_locallyBijective J R).2
  exact (congrArg (fun g ↦ g.app (Opposite.op W.unop.left) x)
    ((PresheafOfModules.sheafificationAdjunction (scalarPerfectRingUnit J R)).unit.naturality
      ((scalarPerfectConstantPresheaf (C := C) R).map f))).symm

/-- Constant sheafification and arbitrary scalar extension send a finite free module
onto the finite tuple sheaf, with coordinates given by multiplication on pure sections.
Source: Stacks Project, sites-modules.tex, Tag 0GMW. The constant rank-one module
sheafifies to the constant ring by local bijectivity of its unit. Slice restriction
preserves that unit. Scalar extension identifies it with the target unit by
multiplication. Apply finite-product preservation of additive functors and the
concrete product cone of modules; naturality of the two sheafification units gives
the displayed formula. This includes rank zero.
(blueprint: lem-sfb-scalar-perfect-chart-finite-free). -/
theorem exists_scalarPerfectChartFiniteFreeIso (U : C) (n : ℕ) :
    ∃ e : (scalarPerfectChartFunctor J R φ U).obj (ModuleCat.of R (Fin n → R)) ≅
        ∏ᶜ fun _ : Fin n ↦ unit ((scalarPerfectRingUnderlying J B).over U),
      ∀ (W : (Over U)ᵒᵖ) (b : B.obj.obj (Opposite.op W.unop.left))
        (x : Fin n → R) (k : Fin n),
        (e.hom ≫ Pi.π _ k).val.app W
          (scalarPerfectChartSection J R φ U (ModuleCat.of R (Fin n → R)) W b x) =
          b * φ.hom.app (Opposite.op W.unop.left)
            ((scalarPerfectRingUnit J R).app (Opposite.op W.unop.left) (x k)) := by
  let G := scalarPerfectChartFunctor J R φ U
  have : (overFunctor.{s} (scalarPerfectRingUnderlying J (scalarPerfectRing J R)) U).Additive :=
    ⟨fun {_ _} f g ↦ by ext W x; rfl⟩
  have hC := scalarPerfectConstantFunctor_additive J R
  have hE := scalarPerfectExtensionFunctor_additive (J.over U)
    ((J.overPullback CommRingCat.{s} U).map φ)
  have : G.Additive := inferInstanceAs
    ((scalarPerfectConstantFunctor J R ⋙
      overFunctor (scalarPerfectRingUnderlying J (scalarPerfectRing J R)) U ⋙
      scalarPerfectExtensionFunctor.{max c v, v, s} (J.over U)
        ((J.overPullback CommRingCat.{s} U).map φ)).Additive)
  let e := G.mapIso (ModuleCat.piIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)).symm ≪≫
    PreservesProduct.iso G (fun _ : Fin n ↦ ModuleCat.of R R) ≪≫
      Pi.mapIso (fun _ : Fin n ↦ chartUnitIso J R φ U)
  refine ⟨e, ?_⟩
  intro W b x k
  have he : e.hom ≫ Pi.π _ k =
      G.map (ModuleCat.ofHom (LinearMap.proj k)) ≫ (chartUnitIso J R φ U).hom := by
    simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      Pi.mapIso_hom_π, PreservesProduct.iso_hom, piComparison_comp_π_assoc]
    rw [← G.map_comp_assoc, ModuleCat.piIsoPi_inv_kernel_ι]
  rw [he]
  change (chartUnitIso J R φ U).hom.val.app W
    ((G.map _).val.app W (scalarPerfectChartSection J R φ U (ModuleCat.of R (Fin n → R)) W b x)) = _
  rw [chart_map_section, chartUnitIso_section]
  rfl

end SheafOfModules
