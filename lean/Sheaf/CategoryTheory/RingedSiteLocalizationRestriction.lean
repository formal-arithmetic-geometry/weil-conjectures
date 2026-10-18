/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.RingedSiteLocalization
public import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Whiskering

/-! Restriction comparison for the localization-Hom vanishing criterion. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_sheafification
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U V : C) (a : V ⟶ U) :
    let S := PresheafOfModules.sheafification.{u} (R := R.over U) (𝟙 (R.over U).obj)
    let T := PresheafOfModules.sheafification.{u} (R := R.over V) (𝟙 (R.over V).obj)
    Nonempty (S ⋙ SheafOfModules.overMap.{u} R a ≅
      PresheafOfModules.pushforward₀.{u} (Over.map a) (R.over U).obj ⋙ T) := by
  dsimp only
  let J₀ := J.over U
  let K := J.over V
  let : K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}) := inferInstance
  let S := PresheafOfModules.sheafification.{u} (R := R.over U) (𝟙 (R.over U).obj)
  let T := PresheafOfModules.sheafification.{u} (J := K) (R := R.over V)
    (𝟙 (R.over V).obj)
  let P : PresheafOfModules.{u} (R.over U).obj ⥤ PresheafOfModules.{u} (R.over V).obj :=
    PresheafOfModules.pushforward₀.{u} (Over.map a) (R.over U).obj
  let F := SheafOfModules.overMap.{u} R a
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (R := R.over U) (𝟙 (R.over U).obj)
  let b := PresheafOfModules.sheafificationAdjunction.{u} (J := K) (R := R.over V)
    (𝟙 (R.over V).obj)
  let t : P ⋙ T ⟶ S ⋙ F :=
    { app M := (b.homEquiv _ _).symm (P.map (adj.unit.app M))
      naturality {M N} f := by
        change T.map (P.map f) ≫
          (b.homEquiv (P.obj N) (F.obj (S.obj N))).symm (P.map (adj.unit.app N)) =
            (b.homEquiv (P.obj M) (F.obj (S.obj M))).symm (P.map (adj.unit.app M)) ≫
              F.map (S.map f)
        erw [← b.homEquiv_naturality_left_symm, ← b.homEquiv_naturality_right_symm]
        congr 1
        change P.map f ≫ P.map (adj.unit.app N) =
          P.map (adj.unit.app M) ≫
            P.map ((SheafOfModules.forget (R.over U) ⋙
              PresheafOfModules.restrictScalars (𝟙 (R.over U).obj)).map (S.map f))
        rw [← P.map_comp, ← P.map_comp]
        exact congrArg P.map (adj.unit.naturality f) }
  have ht (M : PresheafOfModules.{u} (R.over U).obj) :
      CategoryTheory.toSheafify K (P.obj M).presheaf ≫
          (PresheafOfModules.toPresheaf (R.over V).obj).map (t.app M).val =
        Functor.whiskerLeft (Over.map a).op
          (CategoryTheory.toSheafify J₀ M.presheaf) := by
    have h := (b.homEquiv (P.obj M) (F.obj (S.obj M))).apply_symm_apply
      (show P.obj M ⟶ (SheafOfModules.forget (R.over V) ⋙ PresheafOfModules.restrictScalars
        (𝟙 (R.over V).obj)).obj (F.obj (S.obj M)) from P.map (adj.unit.app M))
    have h' := congrArg ((PresheafOfModules.toPresheaf (R.over V).obj).map) h
    change CategoryTheory.toSheafify K (P.obj M).presheaf ≫
      (PresheafOfModules.toPresheaf (R.over V).obj).map (t.app M).val = _ at h'
    exact h'
  have hi (M : PresheafOfModules.{u} (R.over U).obj) : IsIso (t.app M) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over V))]
    apply (Sheaf.isLocallyBijective_iff_isIso (J := K)
      ((SheafOfModules.toSheaf (R.over V)).map (t.app M))).mp
    have h₁ : Presheaf.IsLocallyInjective K
        (Functor.whiskerLeft (Over.map a).op
          (CategoryTheory.toSheafify J₀ M.presheaf)) :=
      Presheaf.isLocallyInjective_whisker K J₀ (Over.map a) _
    have h₂ : Presheaf.IsLocallySurjective K
        (Functor.whiskerLeft (Over.map a).op
          (CategoryTheory.toSheafify J₀ M.presheaf)) :=
      Presheaf.isLocallySurjective_whisker K J₀ (Over.map a) _
    have : Presheaf.IsLocallyInjective K
        (CategoryTheory.toSheafify K (P.obj M).presheaf) :=
      (K.W_toSheafify _).isLocallyInjective
    have : Presheaf.IsLocallySurjective K
        (CategoryTheory.toSheafify K (P.obj M).presheaf) :=
      (K.W_toSheafify _).isLocallySurjective
    rw [← ht M] at h₁ h₂
    exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp h₁,
      (Presheaf.comp_isLocallySurjective_iff _ _ _).mp h₂⟩
  let : ∀ M, IsIso (t.app M) := hi
  let : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨(asIso t).symm⟩


private theorem restriction_preserves_colimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U V : C) (a : V ⟶ U) :
    PreservesColimitsOfShape ℕ (SheafOfModules.overMap.{u} R a) := by
  let S := PresheafOfModules.sheafification.{u} (R := R.over U) (𝟙 (R.over U).obj)
  let T := PresheafOfModules.sheafification.{u} (R := R.over V) (𝟙 (R.over V).obj)
  let P := PresheafOfModules.pushforward₀.{u} (Over.map a) (R.over U).obj
  let F := SheafOfModules.overMap.{u} R a
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (R := R.over U) (𝟙 (R.over U).obj)
  let : PreservesColimitsOfShape ℕ P := ⟨fun {D} ↦ by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
    apply PresheafOfModules.evaluationJointlyReflectsColimits
    intro X
    exact isColimitOfPreserves
      (PresheafOfModules.evaluation (R.over U).obj ((Over.map a).op.obj X))
      (colimit.isColimit D)⟩
  obtain ⟨e⟩ := restriction_sheafification R U V a
  let : PreservesColimitsOfShape ℕ (S ⋙ F) :=
    preservesColimitsOfShape_of_natIso e.symm
  constructor
  intro D
  let E := D ⋙ (SheafOfModules.forget (R.over U) ⋙
    PresheafOfModules.restrictScalars (𝟙 (R.over U).obj))
  let : PreservesColimit (E ⋙ S) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves S (colimit.isColimit E))
      (isColimitOfPreserves (S ⋙ F) (colimit.isColimit E))
  exact preservesColimit_of_iso_diagram F
    (Functor.associator D _ S ≪≫
      Functor.isoWhiskerLeft D (asIso adj.counit) ≪≫ Functor.rightUnitor D)

/-- Sequential coefficient localization commutes with restriction between slices.

Source: Stacks Project, algebraization.tex, Tag 0997, and sites-cohomology.tex,
Tag 08JB. (blueprint: lem-weil-pbc-ringed-site-localization-restriction).

Proof: Restriction along Over.map a commutes with module sheafification: both
sheafifications have the same local sections on each object W → V, since the
covering sieves there are exactly the covering sieves on W. Colimits of module
sheaves are sheafifications of sectionwise colimits, so this restriction preserves
colimits. The restriction of the unit module on U is canonically the unit module
on V. Under this identification multiplication by f restricts to multiplication
by R(a)(f), by functoriality of R and the commuting triangle defining an object
over V. Apply the colimit comparison to this isomorphism of sequential diagrams.
All maps are module maps and commute with restrictions. The inverse follows from
the universal property of the colimit; this includes zero and nilpotent f.
-/
theorem ringedSite_localization_restriction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U V : C) (a : V ⟶ U)
    (f : R.obj.obj (op U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    Nonempty ((SheafOfModules.overMap.{u} R₀ a).obj
      (ringedSiteSectionLocalization R₀ U f) ≅
      ringedSiteSectionLocalization R₀ V (R.obj.map a.op f)) := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let F := SheafOfModules.overMap.{u} R₀ a
  let := restriction_preserves_colimits R₀ U V a
  let tU : SheafOfModules.unit (R₀.over U) ⟶ SheafOfModules.unit (R₀.over U) :=
    (SheafOfModules.unit (R₀.over U)).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk (fun W ↦ R₀.obj.map W.unop.hom.op f)
        (fun {W Z} b ↦ ringedSiteSectionLocalization_compatible R₀ U f W Z b))
  let tV : SheafOfModules.unit (R₀.over V) ⟶ SheafOfModules.unit (R₀.over V) :=
    (SheafOfModules.unit (R₀.over V)).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun W ↦ R₀.obj.map W.unop.hom.op (R.obj.map a.op f))
        (fun {W Z} b ↦ ringedSiteSectionLocalization_compatible
          R₀ V (R.obj.map a.op f) W Z b))
  let DU := Functor.ofSequence (fun _ : ℕ ↦ tU)
  let DV := Functor.ofSequence (fun _ : ℕ ↦ tV)
  let e := SheafOfModules.overMapUnitIso (R := R₀) a
  have ht : F.map tU ≫ e.hom = e.hom ≫ tV := by
    apply (SheafOfModules.unit (R₀.over V)).unitHomEquiv.injective
    ext W
    simp only [SheafOfModules.unitHomEquiv_apply_coe]
    change tU.val.app ((Over.map a).op.obj W)
      (1 : R₀.obj.obj (op W.unop.left)) =
        tV.val.app W (1 : R₀.obj.obj (op W.unop.left))
    rw [← SheafOfModules.unitHomEquiv_apply_coe,
      ← SheafOfModules.unitHomEquiv_apply_coe]
    simp only [tU, tV, Equiv.apply_symm_apply]
    change R₀.obj.map (W.unop.hom ≫ a).op f =
      R₀.obj.map W.unop.hom.op (R.obj.map a.op f)
    rw [op_comp, R₀.obj.map_comp]
    rfl
  let t : DU ⋙ F ⟶ DV := NatTrans.ofSequence (fun _ ↦ e.hom) (fun n ↦ by
    simpa only [Functor.comp_map, DU, DV, Functor.ofSequence_map_homOfLE_succ] using ht)
  let : ∀ n, IsIso (t.app n) := fun n ↦ inferInstanceAs (IsIso e.hom)
  let : IsIso t := NatIso.isIso_of_isIso_app t
  change Nonempty (F.obj (colimit DU) ≅ colimit DV)
  exact ⟨preservesColimitIso F DU ≪≫ HasColimit.isoOfNatIso (asIso t)⟩

end CategoryTheory
