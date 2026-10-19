/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections

/-! # Local lifting from a constant finite-projective module

Source: Stacks Project, Cohomology on Sites, Tag 08FN.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Actual covering presieves are cofinal among covering sieves. -/
private theorem covering_presieve_refinement
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {U : C} {S : Sieve U} (hS : S ∈ J.toGrothendieck U) :
    ∃ Q ∈ J U, Q ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of U Q hQ => exact ⟨Q, hQ, Sieve.le_generate Q⟩
  | top U =>
      exact ⟨Presieve.singleton (𝟙 U), J.mem_coverings_of_isIso (𝟙 U), by simp⟩
  | pullback U S hS V f ih =>
      obtain ⟨Q, hQ, hle⟩ := ih
      obtain ⟨I, W, g, rfl⟩ := Q.exists_eq_ofArrows
      obtain ⟨P, p, q, hpq, hP⟩ := hJ.2.2 I U W g hQ V f
      refine ⟨Presieve.ofArrows P p, hP, ?_⟩
      intro T a ha
      obtain ⟨i⟩ := ha
      change S (p i ≫ f)
      rw [(hpq i).w]
      exact S.downward_closed (hle _ _ ⟨i⟩) (q i)
  | transitive U S T hS hT ihS ihT =>
      obtain ⟨Q, hQ, hle⟩ := ihS
      have hlocal (V : C) (f : V ⟶ U) (hf : Q f) :
          ∃ P ∈ J V, P ≤ (T.pullback f).arrows := ihT (hle _ _ hf)
      choose P hP hPT using hlocal
      refine ⟨Q.bind (fun V f hf ↦ P V f hf),
        hJ.2.1 U Q (fun V f hf ↦ P V f hf) hQ hP, ?_⟩
      intro V f hf
      obtain ⟨W, g, a, hg, ha, rfl⟩ := hf
      exact hPT W a hg _ _ ha

section ConstantSlice

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] (M : ModuleCat.{max u v} R) (U : C)

private abbrev sliceRingUnit :
    (Functor.const (Over U)ᵒᵖ).obj (RingCat.of R) ⟶
      (((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)).over U).obj :=
  Functor.whiskerLeft (Over.forget U).op
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))

private def sliceModuleUnit :
    (siteConstantModulePresheafGeneral (C := Over U) R).obj M ⟶
      (PresheafOfModules.restrictScalars (sliceRingUnit J R U)).obj
        (((siteConstantModuleFunctorGeneral J R).obj M).over U).val where
  app W := ((PresheafOfModules.sheafificationAdjunction
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).unit.app
      ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app
        ((Over.forget U).op.obj W)
  naturality {W Z} f := by
    exact ((PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).unit.app
        ((siteConstantModulePresheafGeneral (C := C) R).obj M)).naturality
          ((Over.forget U).op.map f)

private def sliceConstantHomEquiv
    (A : SheafOfModules.{max u v}
      (((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)).over U)) :
    (((siteConstantModuleFunctorGeneral J R).obj M).over U ⟶ A) ≃
      ((siteConstantModulePresheafGeneral (C := Over U) R).obj M ⟶
        (PresheafOfModules.restrictScalars (sliceRingUnit J R U)).obj A.val) := by
  have : Presheaf.IsLocallySurjective (J.over U) (sliceRingUnit J R U) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  have : PresheafOfModules.IsLocallyInjective (J.over U) (sliceModuleUnit J R M U) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf)
  have : PresheafOfModules.IsLocallySurjective (J.over U) (sliceModuleUnit J R M U) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf)
  exact (SheafOfModules.fullyFaithfulForget _).homEquiv.trans
    ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (sliceRingUnit J R U) A.isSheaf).trans
      (PresheafOfModules.homEquivOfIsLocallyBijective
        (f := sliceModuleUnit J R M U) A.isSheaf))

/-- A constant-presheaf map on a slice is determined at its terminal object. -/
private theorem slice_presheaf_hom_ext
    {P : PresheafOfModules.{max u v} ((Functor.const (Over U)ᵒᵖ).obj (RingCat.of R))}
    (a b : (siteConstantModulePresheafGeneral (C := Over U) R).obj M ⟶ P)
    (h : a.app (op (Over.mk (𝟙 U))) = b.app (op (Over.mk (𝟙 U)))) : a = b := by
  ext W x
  have ha := PresheafOfModules.naturality_apply a
    (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op x
  have hb := PresheafOfModules.naturality_apply b
    (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op x
  change a.app W x = P.map _ (a.app (op (Over.mk (𝟙 U))) x) at ha
  change b.app W x = P.map _ (b.app (op (Over.mk (𝟙 U))) x) at hb
  rw [ha, hb, h]

/-- Extend a linear map at the terminal slice object to a constant-presheaf map. -/
private def slice_presheaf_hom
    (P : PresheafOfModules.{max u v} ((Functor.const (Over U)ᵒᵖ).obj (RingCat.of R)))
    (l : M ⟶ P.obj (op (Over.mk (𝟙 U)))) :
    (siteConstantModulePresheafGeneral (C := Over U) R).obj M ⟶ P where
  app W := l ≫ P.map (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op
  naturality {W Z} f := by
    ext x
    change P.map (Over.homMk Z.unop.hom : Z.unop ⟶ Over.mk (𝟙 U)).op (l x) =
      P.map f (P.map (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op (l x))
    rw [← PresheafOfModules.map_comp_apply]
    apply P.congr_map_apply
    congr 1
    apply Over.OverMorphism.ext
    exact (Over.w f.unop).symm

private theorem slice_presheaf_hom_app
    (P : PresheafOfModules.{max u v} ((Functor.const (Over U)ᵒᵖ).obj (RingCat.of R)))
    (l : M ⟶ P.obj (op (Over.mk (𝟙 U)))) :
    (slice_presheaf_hom R M U P l).app (op (Over.mk (𝟙 U))) = l := by
  change l ≫ P.map (Over.homMk (𝟙 U) : Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U)).op = l
  have h : (Over.homMk (𝟙 U) : Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U)) = 𝟙 _ := by
    ext
    rfl
  rw [h, op_id, P.map_id]
  exact Category.comp_id l

/-- Constant sections commute with the localization comparison. -/
private theorem sliceModuleUnit_overMap
    {V : C} (f : V ⟶ U)
    (A : SheafOfModules.{max u v}
      (((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)).over U))
    (a : ((siteConstantModuleFunctorGeneral J R).obj M).over U ⟶ A) :
    (sliceConstantHomEquiv J R M V
      ((SheafOfModules.overMap _ f).obj A)
      ((SheafOfModules.overFunctorMap _ f).inv.app _ ≫
        (SheafOfModules.overMap _ f).map a)).app (op (Over.mk (𝟙 V))) =
      (sliceConstantHomEquiv J R M U A a).app (op (Over.mk (𝟙 V ≫ f))) := by
  ext x
  change a.val.app (op (Over.mk (𝟙 V ≫ f)))
      ((sliceModuleUnit J R M V).app (op (Over.mk (𝟙 V))) x) =
    a.val.app (op (Over.mk (𝟙 V ≫ f)))
      ((sliceModuleUnit J R M U).app (op (Over.mk (𝟙 V ≫ f))) x)
  rfl

end ConstantSlice

set_option maxHeartbeats 600000 in
-- Elaborating scalar restrictions and slice comparisons needs more than the default budget.
/-- A map from a constant finite-projective module on a slice lifts locally through
an epimorphism. Source: Stacks Project, Cohomology on Sites, Tag 08FN
(blueprint: lem-sfb-perfect-constant-local-lift).

Proof: Restrict the constant-ring sheafification unit to each slice. It is locally
surjective, and the corresponding constant-module unit is locally bijective.
Their universal properties identify maps from the restricted constant module
with maps of constant module presheaves into the scalar restriction of the target.
Such a map is determined by its component at the terminal object of the slice;
a linear map at that object extends by restriction along every slice structure map.
Choose finitely many generators of M. Forgetting p to abelian sheaves preserves
its epimorphism, so the images of these generators lift on covering sieves.
Intersect these finitely many sieves. Induction on the saturation defining
J.toGrothendieck, using covering pullbacks and Presieve.bind transitivity,
refines this covering sieve to an actual J-covering presieve. On every member,
transport the lifted sections to the terminal object of the new slice. The
restricted map sends every generator into the sectionwise image of p, and hence
its entire image lies there. Factor through this image and use projectivity of M
to lift through the surjection onto it. Extend the resulting linear map to a
presheaf map, then to a sheaf map by the universal properties. Checking at the
terminal slice object proves the required composite equation. Naturality of the
constant-module unit gives the displayed overFunctorMap comparison. An empty
generating family uses the maximal sieve; empty covers and the zero ring are allowed. -/
theorem exists_perfect_constant_local_lift
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Type (max u v)) [CommRing R]
    (M : ModuleCat.{max u v} R) [Module.Finite R M] [Module.Projective R M]
    (U : C)
    (A B : SheafOfModules.{max u v}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U))
    (p : A ⟶ B) [Epi p]
    (a : ((siteConstantModuleFunctorGeneral J.toGrothendieck R).obj M).over U ⟶ B) :
    ∃ S ∈ J U, ∀ (V : C) (f : V ⟶ U), S f →
      ∃ t : ((siteConstantModuleFunctorGeneral J.toGrothendieck R).obj M).over V ⟶
          (SheafOfModules.overMap
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) f).obj A,
        t ≫ (SheafOfModules.overMap
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) f).map p =
          (SheafOfModules.overFunctorMap
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) f).inv.app
              ((siteConstantModuleFunctorGeneral J.toGrothendieck R).obj M) ≫
          (SheafOfModules.overMap
            ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) f).map a  := by
  classical
  let K := J.toGrothendieck
  let S := (constantSheaf K RingCat.{max u v}).obj (RingCat.of R)
  let aa := sliceConstantHomEquiv K R M U B a
  let φ := (SheafOfModules.toSheaf.{max u v} (S.over U)).map p
  have : Epi φ := inferInstance
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' _ φ).2 inferInstance
  have : Presheaf.IsLocallySurjective (K.over U) φ.hom := inferInstance
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let T (i : s) := Presheaf.imageSieve φ.hom
    (aa.app (op (Over.mk (𝟙 U))) i.1)
  have hT : (⨅ i, T i) ∈ (K.over U) (Over.mk (𝟙 U)) :=
    (K.over U).iInf_mem T (fun i ↦ Presheaf.imageSieve_mem _ _ _)
  obtain ⟨Q, hQ, hQT⟩ := covering_presieve_refinement J hJ
    ((K.mem_over_iff _).mp hT)
  refine ⟨Q, hQ, ?_⟩
  intro V f hf
  have hf' := (Sieve.overEquiv_iff _ _).mp (hQT _ _ hf)
  have hlifts (i : s) := (iInf_le T i) _ hf'
  let β := sliceRingUnit K R V
  let AV := (SheafOfModules.overMap S f).obj A
  let BV := (SheafOfModules.overMap S f).obj B
  let PAV := (PresheafOfModules.restrictScalars β).obj AV.val
  let PBV := (PresheafOfModules.restrictScalars β).obj BV.val
  let pV := (SheafOfModules.overMap S f).map p
  let b := (SheafOfModules.overFunctorMap S f).inv.app
    ((siteConstantModuleFunctorGeneral K R).obj M) ≫
      (SheafOfModules.overMap S f).map a
  let b₀ : M →ₗ[R] PBV.obj (op (Over.mk (𝟙 V))) :=
    ((sliceConstantHomEquiv K R M V BV b).app (op (Over.mk (𝟙 V)))).hom
  let p₀ : PAV.obj (op (Over.mk (𝟙 V))) →ₗ[R] PBV.obj (op (Over.mk (𝟙 V))) :=
    (((PresheafOfModules.restrictScalars β).map pV.val).app
      (op (Over.mk (𝟙 V)))).hom
  have hgen (i : s) : b₀ i.1 ∈ LinearMap.range p₀ := by
    have hli := hlifts i
    change ∃ t : A.val.obj (op (Over.mk (f ≫ 𝟙 U))),
      p.val.app (op (Over.mk (f ≫ 𝟙 U))) t =
        B.val.map (Over.homMk f : Over.mk (f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)).op
          (aa.app (op (Over.mk (𝟙 U))) i.1) at hli
    obtain ⟨t, ht⟩ := hli
    let e : Over.mk (𝟙 V ≫ f) ⟶ Over.mk (f ≫ 𝟙 U) :=
      Over.homMk (𝟙 V) (by simp)
    refine ⟨A.val.map e.op t, ?_⟩
    have hb : b₀ i.1 = aa.app (op (Over.mk (𝟙 V ≫ f))) i.1 :=
      ConcreteCategory.congr_hom (sliceModuleUnit_overMap K R M U f B a) i.1
    have hn := PresheafOfModules.naturality_apply aa
      (Over.homMk (𝟙 V ≫ f) : Over.mk (𝟙 V ≫ f) ⟶ Over.mk (𝟙 U)).op i.1
    change aa.app (op (Over.mk (𝟙 V ≫ f))) i.1 =
      B.val.map (Over.homMk (𝟙 V ≫ f) :
        Over.mk (𝟙 V ≫ f) ⟶ Over.mk (𝟙 U)).op
          (aa.app (op (Over.mk (𝟙 U))) i.1) at hn
    change p.val.app (op (Over.mk (𝟙 V ≫ f))) (A.val.map e.op t) = b₀ i.1
    rw [PresheafOfModules.naturality_apply p.val e.op t, ht,
      ← PresheafOfModules.map_comp_apply]
    have he : (Over.homMk f : Over.mk (f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)).op ≫ e.op =
        (Over.homMk (𝟙 V ≫ f) : Over.mk (𝟙 V ≫ f) ⟶ Over.mk (𝟙 U)).op := by
      rw [← op_comp]
      congr 1
    exact (B.val.congr_map_apply he _).trans (hn.symm.trans hb.symm)
  have hrange : LinearMap.range b₀ ≤ LinearMap.range p₀ := by
    rw [LinearMap.range_eq_map, ← hs, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact hgen ⟨m, hm⟩
  let b' := b₀.codRestrict (LinearMap.range p₀)
    (fun m ↦ hrange (LinearMap.mem_range_self b₀ m))
  obtain ⟨l, hl⟩ := Module.projective_lifting_property p₀.rangeRestrict b'
    (fun x ↦ by obtain ⟨y, hy⟩ := x.2; exact ⟨y, Subtype.ext hy⟩)
  let g := slice_presheaf_hom R M V PAV
    (ModuleCat.ofHom (X := M) (Y := PAV.obj (op (Over.mk (𝟙 V)))) l)
  let t := (sliceConstantHomEquiv K R M V AV).symm g
  refine ⟨t, ?_⟩
  apply (sliceConstantHomEquiv K R M V BV).injective
  apply slice_presheaf_hom_ext R M V
  change (sliceModuleUnit K R M V).app _ ≫
    ((PresheafOfModules.restrictScalars β).map (t ≫ pV).val).app _ =
      ModuleCat.ofHom (X := M) (Y := PBV.obj (op (Over.mk (𝟙 V)))) b₀
  have ht := (sliceConstantHomEquiv K R M V AV).apply_symm_apply g
  have ht₀ := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 V)))) ht
  change (sliceModuleUnit K R M V).app _ ≫
    ((PresheafOfModules.restrictScalars β).map t.val).app _ = _ at ht₀
  rw [slice_presheaf_hom_app] at ht₀
  change ((sliceModuleUnit K R M V).app _ ≫
    ((PresheafOfModules.restrictScalars β).map t.val).app _) ≫
      ModuleCat.ofHom (X := PAV.obj (op (Over.mk (𝟙 V))))
        (Y := PBV.obj (op (Over.mk (𝟙 V)))) p₀ =
      ModuleCat.ofHom (X := M) (Y := PBV.obj (op (Over.mk (𝟙 V)))) b₀
  rw [ht₀]
  ext m
  exact congrArg Subtype.val (LinearMap.congr_fun hl m)

end CategoryTheory
