/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # The coefficient module colimit above a finite subextension

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sfb-finite-extension-compatibility/lem-sfb-qlbar-flat.proof.md, first sentence.
(blueprint: lem-sfb-qlbar-tail-module-colimit).

The universal property is written on sections using the specified coefficient inclusions.
The existing internal-to-sectionwise equivalence retains the underlying abelian sheaves
identically, so these equations name the actual transition maps and cocone legs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- The regular coefficient module F_X with its E_X-action restricted along E_X → F_X,
viewed as a sectionwise module by the existing equivalence.
Source: blueprint lem-sfb-qlbar-flat.proof.md, first sentence, scalar structures.
(blueprint: lem-sfb-qlbar-tail-module-colimit). -/
noncomputable abbrev qlbarTailStage (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (padicSubfieldRingObj X ℓ E)).functor.obj
      ((Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
        (Mod.regular (padicSubfieldRingObj X ℓ F)))

/-- The regular algebraic-closure coefficient module with its E_X-action induced by q_E,
viewed as a sectionwise module by the existing equivalence.
Source: blueprint lem-sfb-qlbar-flat.proof.md, first sentence, scalar structures.
(blueprint: lem-sfb-qlbar-tail-module-colimit). -/
noncomputable abbrev qlbarTailVertex (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : FiniteIntermediateField ℓ) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (padicSubfieldRingObj X ℓ E)).functor.obj
      ((Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj
        (Mod.regular (padicAlgClRingObj X ℓ)))

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj in
private noncomputable def tailRestrictedMap
    {C : Type*} [Category C] [MonoidalCategory C]
    {R A B : C} [MonObj R] [MonObj A] [MonObj B]
    (s : R ⟶ A) (t : R ⟶ B) (a : A ⟶ B)
    [IsMonHom s] [IsMonHom t] [IsMonHom a] (h : s ≫ a = t) :
    (Mod.comap s).obj (Mod.regular A) ⟶ (Mod.comap t).obj (Mod.regular B) :=
  Mod.homMk a (by
    change (s ▷ A ≫ μ[A]) ≫ a = R ◁ a ≫ t ▷ B ≫ μ[B]
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, h, whisker_exchange_assoc])

/-- The finite fields containing E form a nonempty directed poset, and the original maps
q_F : F_X → Ω_X have the colimit universal property in sectionwise E_X-module sheaves.
Source: blueprint lem-sfb-qlbar-flat.proof.md, first sentence.
(blueprint: lem-sfb-qlbar-tail-module-colimit).

Proof:
1. Use the existing directed order on finite intermediate fields to obtain common upper
   bounds in the tail. The tail contains E, and every finite field has a common upper
   bound with E. Thus its inclusion in all finite intermediate fields is final, by
   Mathlib's Monotone.final_functor_iff.
2. Multiplicativity and compatibility of the coefficient inclusions give linear maps
   between the restricted regular internal modules. Apply sectionModuleEquivalence
   to obtain the module diagram and its cocone with exactly the original section maps.
3. Restrict the already proved abelian coefficient colimit
   isColimitPadicAlgClRingObjCocone along the final inclusion. The result is definitionally
   the underlying abelian cocone of the module cocone. The module forgetful functor
   preserves colimits and reflects isomorphisms, so it reflects this colimit.
4. Package the given compatible family as a module cocone. Its descent map and the
   colimit's factorization and uniqueness equations give the stated sectionwise
   existence and uniqueness. -/
theorem qlbar_tail_module_colimit (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : FiniteIntermediateField ℓ) :
    Nonempty {F : FiniteIntermediateField ℓ // E ≤ F} ∧
    (∀ F G : {F : FiniteIntermediateField ℓ // E ≤ F},
      ∃ H : {F : FiniteIntermediateField ℓ // E ≤ F}, F ≤ H ∧ G ≤ H) ∧
    (∀ (M : ringedSiteModules.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X)
            (padicSubfieldRingObj X ℓ E))))
      (f : ∀ F : {F : FiniteIntermediateField ℓ // E ≤ F},
        qlbarTailStage X ℓ F.2 ⟶ M),
      (∀ (F G : {F : FiniteIntermediateField ℓ // E ≤ F}) (h : F ≤ G)
        (U : X.ProEtᵒᵖ) (x : (padicSubfieldRingObj X ℓ F.1).obj.obj U),
        (f G).val.app U ((padicSubfieldRingObjMap X ℓ h).hom.app U x) =
          (f F).val.app U x) →
      ∃! g : qlbarTailVertex X ℓ E ⟶ M,
        ∀ (F : {F : FiniteIntermediateField ℓ // E ≤ F})
          (U : X.ProEtᵒᵖ) (x : (padicSubfieldRingObj X ℓ F.1).obj.obj U),
          g.val.app U ((padicSubfieldRingObjToPadicAlgCl X ℓ F.1).hom.app U x) =
            (f F).val.app U x) := by
  classical
  let I := {F : FiniteIntermediateField ℓ // E ≤ F}
  have hdir (F G : I) : ∃ H : I, F ≤ H ∧ G ≤ H := by
    obtain ⟨H, hF, hG⟩ := exists_ge_ge F.1 G.1
    exact ⟨⟨H, F.2.trans hF⟩, hF, hG⟩
  have : Nonempty I := ⟨⟨E, le_rfl⟩⟩
  have : IsDirectedOrder I := ⟨hdir⟩
  let inc : I ⥤ FiniteIntermediateField ℓ :=
    (show Monotone (fun F : I ↦ F.1) from fun _ _ h ↦ h).functor
  have : inc.Final := (Monotone.final_functor_iff _).2 (by
    intro F
    obtain ⟨G, hE, hF⟩ := exists_ge_ge E F
    exact ⟨⟨G, hE⟩, hF⟩)
  let K := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (padicSubfieldRingObj X ℓ E)
  let O := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X)
      (padicSubfieldRingObj X ℓ E))
  have hcomp {F G H : FiniteIntermediateField ℓ} (h : F ≤ G) (k : G ≤ H) :
      padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjMap X ℓ k =
        padicSubfieldRingObjMap X ℓ (h.trans k) := by
    exact (upperStarFromPoint X).map_comp _ _ |>.symm
  let D : I ⥤ SheafOfModules.{u + 1} O :=
    { obj := fun F ↦ qlbarTailStage X ℓ F.2
      map := fun {F G} h ↦ K.functor.map (tailRestrictedMap
        (padicSubfieldRingObjMap X ℓ F.2) (padicSubfieldRingObjMap X ℓ G.2)
        (padicSubfieldRingObjMap X ℓ (leOfHom h)) (hcomp _ _))
      map_id := by
        intro F
        ext U x
        change ((upperStarFromPoint X).map (𝟙 _)).hom.app U x = x
        simp
      map_comp := by
        intro F G H h k
        ext U x
        exact congrArg (fun t ↦ t.hom.app U x) (hcomp (leOfHom h) (leOfHom k)).symm }
  let d : Cocone D :=
    { pt := qlbarTailVertex X ℓ E
      ι :=
        { app := fun F ↦ K.functor.map (tailRestrictedMap
            (padicSubfieldRingObjMap X ℓ F.2)
            (padicSubfieldRingObjToPadicAlgCl X ℓ E)
            (padicSubfieldRingObjToPadicAlgCl X ℓ F.1)
            (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.2))
          naturality := by
            intro F G h
            ext U x
            exact congrArg (fun t ↦ t.hom.app U x)
              (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom h)) } }
  have ha := (Functor.Final.isColimitWhiskerEquiv inc
    (padicAlgClRingObjCocone X ℓ)).symm (isColimitPadicAlgClRingObjCocone X ℓ)
  have : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  have : HasColimit D := by
    let e : D ≅ (D ⋙ SheafOfModules.forget O) ⋙
        PresheafOfModules.sheafification (𝟙 O.obj) :=
      Functor.isoWhiskerLeft D
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit).symm
    exact hasColimit_of_iso e
  have : PreservesColimit D (SheafOfModules.toSheaf.{u + 1} O) := inferInstance
  have : ReflectsColimit D (SheafOfModules.toSheaf.{u + 1} O) :=
    reflectsColimit_of_reflectsIsomorphisms D (SheafOfModules.toSheaf.{u + 1} O)
  have hd : IsColimit d := isColimitOfReflects (SheafOfModules.toSheaf.{u + 1} O) ha
  refine ⟨inferInstance, hdir, ?_⟩
  intro M f hf
  let c : Cocone D :=
    { pt := M
      ι :=
        { app := f
          naturality := by
            intro F G h
            ext U x
            exact hf F G (leOfHom h) U x } }
  refine ⟨hd.desc c, ?_, ?_⟩
  · intro F U x
    exact congrArg (fun t ↦ t.val.app U x) (hd.fac c F)
  · intro g hg
    apply hd.uniq c g
    intro F
    ext U x
    exact hg F U x

end AlgebraicGeometry.ProEtale
