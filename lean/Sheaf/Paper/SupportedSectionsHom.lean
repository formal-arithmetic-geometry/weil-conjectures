/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Underived supported sections as Hom

Source: Milne, Lectures on Etale Cohomology, Section 9, proof of Theorem 9.4,
p. 67; the constant-coefficient argument of lem-pur-supported-hom, steps 1--4
(blueprint: lem-pur-supported-sections-hom).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private noncomputable def openConstantMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    (constantSheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj (ModuleCat.of _ (ULift.{u + 1} A)) ⟶
      (openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
        ((constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
            (ModuleCat.of _ (ULift.{u + 1} A))) :=
  Scheme.proEtaleFixedOpenConstantMap j A

private noncomputable def openConstantArrow {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
      (Scheme.proEtaleFixedConstantModule U A) ⟶ Scheme.proEtaleFixedConstantModule X A :=
  ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv _ _).symm (openConstantMap j A)

private theorem fixedConstantPresentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : openConstantArrow i.openComplement.ι A ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (ModuleCat.of _ (ULift.{u + 1} A)) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (ModuleCat.of _ (ULift.{u + 1} A))) h)) := by
  classical
  let E := Scheme.sfIntrinsicModuleEquivalence X A
  let EU := Scheme.sfIntrinsicModuleEquivalence i.openComplement.toScheme A
  let AZ := Scheme.proEtaleFixedConstantModule Z A
  let AX := Scheme.proEtaleFixedConstantModule X A
  let AU := Scheme.proEtaleFixedConstantModule i.openComplement.toScheme A
  let L := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A))
    i.openComplement.ι
  let ρ := Scheme.proEtaleConstantDirectImageMap i
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (ModuleCat.of _ (ULift.{u + 1} A))
  let k : E.functor.obj (L.obj AU) ≅
      (Scheme.sfIntrinsicExtensionByZero i.openComplement.ι A).obj
        (Scheme.proEtaleConstantModule i.openComplement.toScheme A) :=
    E.functor.mapIso (L.mapIso (EU.unitIso.app AU ≪≫
      EU.inverse.mapIso (Scheme.proEtaleConstantModuleUnit i.openComplement.toScheme A)))
  let q : E.functor.obj ((lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj AZ) ≅
        (Scheme.proEtaleConstantModuleDirectImage i A).obj
          (Scheme.proEtaleConstantModule Z A) :=
    (Scheme.sfIntrinsicDirectImageComparison i A).symm.app AZ ≪≫
      (Scheme.proEtaleConstantModuleDirectImage i A).mapIso
        (Scheme.proEtaleConstantModuleUnit Z A)
  have he : E.functor.map (openConstantArrow i.openComplement.ι A) ≫
      (Scheme.proEtaleConstantModuleUnit X A).hom =
        k.hom ≫ Scheme.proEtaleOpenConstantCounit i.openComplement.ι A := by
    dsimp [k, Scheme.proEtaleOpenConstantCounit, Scheme.sfIntrinsicExtensionByZero]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    simp [E, EU, AU, L, openConstantArrow, openConstantMap]
  have hr : E.functor.map ρ ≫ q.hom =
      (Scheme.proEtaleConstantModuleUnit X A).hom ≫
        Scheme.proEtaleClosedConstantRestriction i A := by
    dsimp [q, Scheme.proEtaleClosedConstantRestriction]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  obtain ⟨h, ⟨hc⟩⟩ := Scheme.proEtale_supported_constant_presentation A i
  have hz : openConstantArrow i.openComplement.ι A ≫ ρ = 0 := by
    apply E.functor.map_injective
    apply (cancel_mono q.hom).mp
    rw [Functor.map_comp, Functor.map_zero, zero_comp, Category.assoc, hr,
      ← Category.assoc, he, Category.assoc, h, comp_zero]
  refine ⟨hz, ⟨?_⟩⟩
  apply isColimitOfReflects E.functor
  refine (isColimitMapCoconeCoforkEquiv' E.functor hz).symm ?_
  exact IsCokernel.ofIso _ hc _ k.symm (Scheme.proEtaleConstantModuleUnit X A).symm
    q.symm (by
      apply (cancel_epi k.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← he]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]) (by
      apply (cancel_epi (Scheme.proEtaleConstantModuleUnit X A).hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc, Cofork.π_ofπ]
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])

private noncomputable def constantHomEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} R)) :
    ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶ M) ≃+
      M.obj.obj (op T) :=
  ((constantSheafAdj J (ModuleCat.{u + 1} R) hT).homAddEquiv _ M).trans
    (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toAddEquiv)

private theorem constantHomEquiv_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] [HasSheafify J (ModuleCat.{u + 1} R)]
    {T : C} (hT : IsTerminal T) (M : Sheaf J (ModuleCat.{u + 1} R))
    (f : (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ⟶ M) :
    constantHomEquiv J hT M f = f.hom.app (op T)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))).app (op T) (1 : R)) := by
  rfl

private noncomputable def openHomEquiv {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
      (Scheme.proEtaleFixedConstantModule U A) ⟶ M) ≃+
        ((openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj M).obj.obj
          (op (Scheme.ProEt.mk (𝟙 U))) :=
  ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homAddEquiv _ M).trans
      (constantHomEquiv (Scheme.ProEt.topology U)
        (MorphismProperty.Over.mkIdTerminal _ U) _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openHomEquiv_comp {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (f : Scheme.proEtaleFixedConstantModule X A ⟶ M) :
    openHomEquiv j A M (openConstantArrow j A ≫ f) =
      M.obj.map (MorphismProperty.Over.homMk j
        (by
          change j ≫ 𝟙 X = 𝟙 U ≫ j
          exact (Category.comp_id j).trans (Category.id_comp j).symm) :
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
            (Scheme.ProEt.mk (𝟙 U)) ⟶ Scheme.ProEt.mk (𝟙 X)).op
        (constantHomEquiv (Scheme.ProEt.topology X)
          (MorphismProperty.Over.mkIdTerminal _ X) M f) := by
  dsimp only [openHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right, openConstantArrow,
    Equiv.apply_symm_apply]
  simp only [constantHomEquiv_apply]
  let T := Scheme.ProEt.mk (𝟙 U)
  let V : X.ProEt := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj T
  let η := toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))
  let t := Functor.whiskerLeft
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op η
  have hn := ((sheafificationAdjunction (Scheme.ProEt.topology U)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))).homEquiv
      ((Functor.const U.ProEtᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))
      ((openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
        (Scheme.proEtaleFixedConstantModule X A))).apply_symm_apply t
  have hu : (toSheafify (Scheme.ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))).app (op T) ≫
      (openConstantMap j A).hom.app (op T) = η.app (op V) :=
    congrArg (fun k ↦ k.app (op T)) hn
  change f.hom.app (op V) ((openConstantMap j A).hom.app (op T)
    ((toSheafify (Scheme.ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj
        (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))).app (op T) (1 : ULift A))) = _
  have hu1 := congrArg (fun k ↦ k (1 : ULift A)) hu
  change _ = _ at hu1
  erw [hu1]
  let g : V ⟶ Scheme.ProEt.mk (𝟙 X) := MorphismProperty.Over.homMk j
    (by exact (Category.comp_id j).trans (Category.id_comp j).symm)
  have hf := congrArg (fun k ↦ k (η.app (op (Scheme.ProEt.mk (𝟙 X))) (1 : ULift A)))
    (f.hom.naturality g.op)
  have hη := congrArg (fun k ↦ k (1 : ULift A)) (η.naturality g.op)
  change f.hom.app (op V) (η.app (op V) (1 : ULift A)) = _
  simp only [Functor.const_obj_map, ModuleCat.comp_apply] at hη hf
  change η.app (op V) (1 : ULift A) = _ at hη
  exact (congrArg (fun x ↦ f.hom.app (op V) x) hη).trans hf

private noncomputable def openSiteIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Scheme.ProEt.mk j ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        (Scheme.ProEt.mk (𝟙 U)) :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 U ≫ (𝟙 U ≫ j) = j
    simp only [Category.id_comp])

private noncomputable def openHomEquivAt {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj
      (Scheme.proEtaleFixedConstantModule U A) ⟶ M) ≃+ M.obj.obj (op (Scheme.ProEt.mk j)) :=
  (openHomEquiv j A M).trans (M.obj.mapIso (openSiteIso j).op).toLinearEquiv.toAddEquiv

private theorem openHomEquivAt_comp (A : Type u) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (f : Scheme.proEtaleFixedConstantModule X A ⟶ M) :
    openHomEquivAt i.openComplement.ι A M (openConstantArrow i.openComplement.ι A ≫ f) =
      M.obj.map (supportRestrictionArrow i).op
        (constantHomEquiv (Scheme.ProEt.topology X)
          (MorphismProperty.Over.mkIdTerminal _ X) M f) := by
  dsimp only [openHomEquivAt, AddEquiv.trans_apply]
  rw [openHomEquiv_comp]
  change M.obj.map _ (M.obj.map _ _) = _
  erw [← ModuleCat.comp_apply, ← Functor.map_comp]
  congr 2

private noncomputable def homToSupportKernel (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj
      (Scheme.proEtaleFixedConstantModule Z A)) ⟶ M) →+
        (M.obj.map (supportRestrictionArrow i).op).hom.ker where
  toFun f := ⟨constantHomEquiv (Scheme.ProEt.topology X)
    (MorphismProperty.Over.mkIdTerminal _ X) M
      (Scheme.proEtaleConstantDirectImageMap i _ (ModuleCat.of _ (ULift.{u + 1} A)) ≫ f), by
    rw [LinearMap.mem_ker, ← openHomEquivAt_comp]
    obtain ⟨h, _⟩ := fixedConstantPresentation A i
    rw [← Category.assoc, h, zero_comp]
    exact (openHomEquivAt _ A M).map_zero⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' f g := by
    apply Subtype.ext
    simp only [Preadditive.comp_add, map_add, AddMemClass.mk_add_mk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homToSupportKernel_bijective (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    Function.Bijective (homToSupportKernel A i M) := by
  obtain ⟨h, ⟨hc⟩⟩ := fixedConstantPresentation A i
  constructor
  · intro f g hfg
    apply Cofork.IsColimit.hom_ext hc
    apply (constantHomEquiv (Scheme.ProEt.topology X)
      (MorphismProperty.Over.mkIdTerminal _ X) M).injective
    exact congrArg Subtype.val hfg
  · intro s
    let f := (constantHomEquiv (Scheme.ProEt.topology X)
      (MorphismProperty.Over.mkIdTerminal _ X) M).symm s.val
    have hf : openConstantArrow i.openComplement.ι A ≫ f = 0 := by
      apply (openHomEquivAt _ A M).injective
      rw [openHomEquivAt_comp]
      simp only [f, AddEquiv.apply_symm_apply, map_zero]
      exact s.property
    refine ⟨hc.desc (CokernelCofork.ofπ f hf), ?_⟩
    apply Subtype.ext
    change constantHomEquiv (Scheme.ProEt.topology X)
      (MorphismProperty.Over.mkIdTerminal _ X) M
        (Scheme.proEtaleConstantDirectImageMap i _ (ModuleCat.of _ (ULift.{u + 1} A)) ≫
          hc.desc (CokernelCofork.ofπ f hf)) = s.val
    rw [show Scheme.proEtaleConstantDirectImageMap i _
      (ModuleCat.of _ (ULift.{u + 1} A)) ≫ hc.desc (CokernelCofork.ofπ f hf) = f from
        Cofork.IsColimit.π_desc hc]
    exact AddEquiv.apply_symm_apply _ _

private noncomputable def fixedSupportedHomEquiv (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj
      (Scheme.proEtaleFixedConstantModule Z A)) ⟶ M) ≃+
        (supportSections i (ULift.{u + 1} A)).obj M :=
  (AddEquiv.ofBijective (homToSupportKernel A i M)
    (homToSupportKernel_bijective A i M)).trans
      ((ModuleCat.kernelIsoKer
        (M.obj.map (supportRestrictionArrow i).op)).symm.toLinearEquiv.toAddEquiv)

private theorem fixedSupportedHomEquiv_ι (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (g : ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj
      (Scheme.proEtaleFixedConstantModule Z A)) ⟶ M) :
    kernel.ι (M.obj.map (supportRestrictionArrow i).op) (fixedSupportedHomEquiv A i M g) =
      constantHomEquiv (Scheme.ProEt.topology X)
        (MorphismProperty.Over.mkIdTerminal _ X) M
        (Scheme.proEtaleConstantDirectImageMap i _ (ModuleCat.of _ (ULift.{u + 1} A)) ≫ g) := by
  change ((ModuleCat.kernelIsoKer _).inv ≫ kernel.ι _) (homToSupportKernel A i M g) = _
  rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

private theorem fixedSupportedHomEquiv_naturality (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (f : M ⟶ N)
    (g : ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj
      (Scheme.proEtaleFixedConstantModule Z A)) ⟶ M) :
    (supportSections i (ULift.{u + 1} A)).map f (fixedSupportedHomEquiv A i M g) =
      fixedSupportedHomEquiv A i N (g ≫ f) := by
  apply (ModuleCat.mono_iff_injective (kernel.ι
    (N.obj.map (supportRestrictionArrow i).op))).mp inferInstance
  change (kernel.map _ _ (f.hom.app _) (f.hom.app _)
    (f.hom.naturality (supportRestrictionArrow i).op) ≫ kernel.ι _)
    (fixedSupportedHomEquiv A i M g) = _
  rw [kernel.lift_ι]
  change f.hom.app (op (Scheme.ProEt.mk (𝟙 X)))
    (kernel.ι (M.obj.map (supportRestrictionArrow i).op)
      (fixedSupportedHomEquiv A i M g)) = _
  rw [fixedSupportedHomEquiv_ι, fixedSupportedHomEquiv_ι]
  simp only [constantHomEquiv_apply]
  rfl

/-- The open-closed constant-coefficient presentation represents the support kernel.
Source: Milne, Section 9, proof of Theorem 9.4, p. 67; blueprint
lem-pur-supported-hom, steps 1--4 (blueprint: lem-pur-supported-sections-hom).

Proof: the constant restriction A_X to i_* A_Z is the cokernel of extension
by zero of A on the complement, by proEtale_supported_constant_presentation.
Transport that cokernel through the canonical intrinsic realization equivalence.
Hom into M is therefore the kernel of Hom(A_X,M) to Hom(j_! A_U,M).
The constant-sheaf adjunction followed by evaluation at 1 identifies the first
Hom group with M(X). The open-extension adjunction and the same evaluation
identify the second with M(U). The open counit sends 1 to 1, so their map is
restriction. Taking kernels gives the claimed additive equivalence. All maps
commute with module morphisms, so these equivalences form a natural isomorphism.
This includes empty supports, full supports, and the zero coefficient ring. -/
theorem supported_sections_hom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Nonempty ((supportSections i P.Coefficient ⋙
      forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) ≅
        preadditiveCoyoneda.obj
          (op ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)))) := by
  classical
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let C := ModuleCat.{u + 1} P.Coefficient
  let e : P.constant Z ≅ Scheme.proEtaleFixedConstantModule Z P.Ring :=
    ((Functor.isoWhiskerLeft (constantSheaf Z.smallEtaleTopology C)
      (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.toProEt Z)
        C Z.smallEtaleTopology (Scheme.ProEt.topology Z)).symm ≪≫
      (Scheme.toProEt Z).constantSheafsheafPullbackIso C
        Z.smallEtaleTopology (Scheme.ProEt.topology Z)
        (terminalIsTerminal : IsTerminal (⊤_ Z.Etale))
        (terminalIsTerminal.isTerminalObj (Scheme.toProEt Z))).app
          (ModuleCat.of P.Coefficient P.Coefficient))
  let E : preadditiveCoyoneda.obj
      (op ((lowerStar C i).obj (Scheme.proEtaleFixedConstantModule Z P.Ring))) ≅
        supportSections i P.Coefficient ⋙ forget₂ C AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun M ↦ (fixedSupportedHomEquiv P.Ring i M).toAddCommGrpIso)
      (by
        intro M N f
        ext g
        exact (fixedSupportedHomEquiv_naturality P.Ring i f g).symm)
  exact ⟨E.symm ≪≫ preadditiveCoyoneda.mapIso ((lowerStar C i).mapIso e).op⟩

end AlgebraicGeometry.ProEtale
