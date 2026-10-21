/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.PrincipalKoszulRoosPresentationComparison
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.LocallySmall
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Reflection by the principal Koszul Roos complex

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E;
sites-cohomology.tex, Tag 0941.
(blueprint: lem-pur-principal-koszul-roos-reflector).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w ux vx

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})

-- Choose the standard degreewise product directly, avoiding recursive limit search.
local instance (priority := 1100)
    (H : ℕ → CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete ℕ)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).has_limit
        (Discrete.functor H)


@[instance_reducible]
private noncomputable def derivedOfLocallySmall
    (A : Type ux) [Category.{vx} A] [Abelian A] [LocallySmall.{w} A]
    [Abelian.HasKInjectiveResolutions A] : HasDerivedCategory.{w} A := by
  letI := HasDerivedCategory.standard A
  have hsmall (K L : CochainComplex A ℤ) [L.IsKInjective] :
      Small.{w} (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) := by
    have hsurj : Function.Surjective (fun f : K ⟶ L ↦ DerivedCategory.Q.map f) := by
      intro f
      let e := DerivedCategory.quotientCompQhIso A
      obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient A (.up ℤ)).obj K) L).surjective
        (e.hom.app K ≫ f ≫ e.inv.app L)
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
      refine ⟨g, ?_⟩
      calc
        DerivedCategory.Q.map g = e.inv.app K ≫
            DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map g) ≫
              e.hom.app L := by
          rw [show
            DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map g) ≫
              e.hom.app L = e.hom.app K ≫ DerivedCategory.Q.map g from
                e.hom.naturality g]
          simp
        _ = f := by rw [hg]; simp
    exact small_of_surjective hsurj
  have : LocallySmall.{w} (DerivedCategory A) := by
    constructor
    intro K L
    let X := DerivedCategory.Q.objPreimage K
    let Y := DerivedCategory.Q.objPreimage L
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective Y
    let eK := DerivedCategory.Q.objObjPreimageIso K
    let eL := (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
      asIso (DerivedCategory.Q.map j)
    have := hsmall X I
    exact (small_congr (Iso.homCongr eK.symm eL)).2 inferInstance
  exact MorphismProperty.hasLocalizationOfLocallySmall _ DerivedCategory.Q


/-- The principal Koszul Roos complex is the reflection onto locally derived complete
objects. No K-flatness of the representative is required: the finite free Koszul factors
preserve quasi-isomorphisms.

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; sites-cohomology.tex,
Tag 0941 (blueprint: lem-pur-principal-koszul-roos-reflector).

Proof: apply the ringed Koszul completion reflector to the singleton generating list
consisting of a. Multiplication by a represents its ideal and the unit module is generated
by one on every slice. Evaluation at one identifies the dual positive two-term Koszul
complex with the negative cone of a^(n+1); the differential sign and degree-zero inclusion
agree, and the dual transition is (a,1). The tensor symmetry identifies its tensor tower
with the principal cone tensor tower used here. These identifications preserve the strict
augmentations. Exact countable products identify the strict Roos cone with total derived
inverse limit, with its zero-coordinate augmentation, by the normalized strict Roos
comparison. Transport the reflector's output completeness and Hom bijection along this
unit-compatible isomorphism. Slice restriction and derived internal Hom preserve that
isomorphism, so the local vanishing condition is exactly the displayed one. The argument
also applies to zero complexes and to a unit; no boundedness or termwise flatness is used.
-/
theorem principalKoszulRoos_reflector
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (R.over V)))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (_ha : Mono (globalSectionMultiplication R a))
    (P : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    IsLocallyDerivedRingedIdealComplete R
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (globalSectionMultiplication R a)
      (DerivedCategory.Q.{w}.obj
        (roosF.obj (koszulTowerComplex R (koszulTensorTower R P a)))) ∧
    ∀ L, IsLocallyDerivedRingedIdealComplete R
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (globalSectionMultiplication R a) L →
      Function.Bijective (fun f : DerivedCategory.Q.{w}.obj
          (roosF.obj (koszulTowerComplex R (koszulTensorTower R P a))) ⟶ L ↦
        DerivedCategory.Q.{w}.map (principalKoszulRoosUnit R P a) ≫ f) := by
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : LocallySmall.{w} A := locallySmall_of_faithful (DerivedCategory.singleFunctor A 0)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ A) := by
    let G := separator A
    have hG := isSeparator_separator A
    have hS : ObjectProperty.IsSeparating
        (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
      intro F F' f g hfg
      apply NatTrans.ext
      funext j
      apply hG.def
      intro a
      let adj := evaluationAdjunctionRight A j
      apply (adj.homEquiv G F').symm.injective
      have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
      exact (adj.homEquiv_naturality_right_symm a f).trans
        (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
    let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
    let : HasFilteredColimitsOfSize.{u, u} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    let : AB5OfSize.{u, u} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    exact {}
  let : LocallySmall.{w} (ℕᵒᵖ ⥤ A) := by
    constructor
    intro F G
    exact small_of_injective (f := fun t : F ⟶ G ↦ t.app) (by
      intro f g h
      apply NatTrans.ext
      exact h)
  let : HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A) := derivedOfLocallySmall _
  have hgen (V : C) : IsRingedIdealGeneratingList R _
      (globalSectionMultiplication R a) V 1 (fun _ ↦ a.val (op V)) := by
    let M := (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).over V
    let s : ULift.{u} (Fin 1) → M.sections := fun _ ↦ M.unitHomEquiv (𝟙 M)
    let f := M.freeHomEquiv.symm s
    have hf : SheafOfModules.ιFree (R := _) (ULift.up (0 : Fin 1)) ≫ f = 𝟙 M := by
      apply M.unitHomEquiv.injective
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp only [f, Equiv.apply_symm_apply]
      rfl
    let : IsSplitEpi f := IsSplitEpi.mk' ⟨SheafOfModules.ιFree (ULift.up (0 : Fin 1)), hf⟩
    let σ : M.GeneratingSections := { I := ULift.{u} (Fin 1), s := s, epi := inferInstance }
    refine ⟨σ, Equiv.ulift, ?_⟩
    intro i
    change (globalSectionMultiplication R a).val.app (op V)
      (1 : R.obj.obj (op V)) = a.val (op V)
    have h := congrArg (fun z ↦ z.val (op V))
      ((SheafOfModules.unit _).unitHomEquiv.apply_symm_apply a)
    exact h
  let : Mono (globalSectionMultiplication R a) := _ha
  obtain ⟨D, hD, hbij, _, _⟩ := ringedKoszulCompletionReflector R 1
    (fun _ ↦ ⟨a.val, a.property⟩) _ (globalSectionMultiplication R a) hgen
  obtain ⟨e, he⟩ := principalKoszulRoos_presentation_comparison R a P D
  have hcomplete : IsLocallyDerivedRingedIdealComplete R _
      (globalSectionMultiplication R a) (DerivedCategory.Q.{w}.obj
        (roosF.obj (koszulTowerComplex R (koszulTensorTower R P a)))) := by
    intro V f hf
    exact (hD (DerivedCategory.Q.obj P) V f hf).of_iso
      ((derivedInternalHom (J.over V) (R.over V)).mapIso
        ((Iso.refl (op ((DerivedCategory.singleFunctor _ 0).obj
          (ringedSectionLocalization (R.over V) (ringedSliceSection R V f))))).prod
            ((ringedDerivedRestriction R V).mapIso e)))
  refine ⟨hcomplete, ?_⟩
  intro L hL
  have hb := hbij (DerivedCategory.Q.obj P) L hL
  let b : (DerivedCategory.Q.obj
      (roosF.obj (koszulTowerComplex R (koszulTensorTower R P a))) ⟶ L) ≃
      (D.completion.obj (DerivedCategory.Q.obj P) ⟶ L) :=
    (Iso.homCongr e (Iso.refl L))
  convert hb.comp b.bijective using 1
  ext f
  dsimp [b, Iso.homCongr]
  rw [← he]
  simp

end CategoryTheory
