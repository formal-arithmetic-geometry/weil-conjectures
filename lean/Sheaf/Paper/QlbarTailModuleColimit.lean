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

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

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

open MonoidalCategory MonObj in
private noncomputable def tailRestrictedMap
    {C : Type*} [Category C] [MonoidalCategory C]
    {R A B : C} [MonObj R] [MonObj A] [MonObj B]
    (sA : R ⟶ A) (sB : R ⟶ B) [IsMonHom sA] [IsMonHom sB]
    (a : A ⟶ B) [IsMonHom a] (h : sA ≫ a = sB) :
    (Mod.comap sA).obj (Mod.regular A) ⟶
      (Mod.comap sB).obj (Mod.regular B) := by
  refine Mod.homMk a ?_
  change (sA ▷ A ≫ μ[A]) ≫ a = R ◁ a ≫ sB ▷ B ≫ μ[B]
  rw [Category.assoc, IsMonHom.mul_hom, tensorHom_def']
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]

set_option backward.isDefEq.respectTransparency false in
/-- The finite fields containing E form a nonempty directed poset, and the original maps
q_F : F_X → Ω_X have the colimit universal property in sectionwise E_X-module sheaves.
Source: blueprint lem-sfb-qlbar-flat.proof.md, first sentence.
(blueprint: lem-sfb-qlbar-tail-module-colimit).

Proof:
1. E itself belongs to the indexing tail. The finite compositum FG contains F and G,
   and EH lies above E for every finite subextension H, so the tail is cofinal.
   Use det-def-sfb-qlbar-condensed-subextensions for finiteness of these composita.
2. Functoriality of the coefficient inclusions and
   lem-sfb-subfield-coefficient-map-comp give a_FG s_F = s_G and q_F s_F = q_E.
   Multiplicativity makes these maps linear for the displayed restricted actions.
   The sectionModuleEquivalence preserves their underlying sheaves identically.
3. By sk-prop-sfb-qlbar-colimit-x the full coefficient ring cocone is a colimit.
   Given a ring cocone t_F on the tail, extend it to all H by t_EH a_H,EH.
   For H ≤ K, EH ≤ EK, so functoriality and the cocone equation give compatibility.
   The full colimit gives a unique factorization; EF = F identifies its tail legs.
   Conversely any tail factorization is fixed on H by q_H = a_H,EH q_EH, hence unique.
4. Apply lem-sfb-directed-ring-sheaf-module-colimit to this tail ring cocone, with
   scalar maps E_X → F_X and q_E. Its module universal property is precisely the
   sectionwise existence and uniqueness below, with the original q_F as legs.
   Thus the comparison from any chosen module colimit is characterized by these legs. -/
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
  have hdir : ∀ F G : I, ∃ H : I, F ≤ H ∧ G ≤ H := by
    intro F G
    obtain ⟨H, hF, hG⟩ := exists_ge_ge F.1 G.1
    exact ⟨⟨H, F.2.trans hF⟩, hF, hG⟩
  have : Nonempty I := ⟨⟨E, le_rfl⟩⟩
  have : IsDirectedOrder I := ⟨hdir⟩
  refine ⟨inferInstance, hdir, ?_⟩
  intro M f hf
  let inc : I → FiniteIntermediateField ℓ := Subtype.val
  have hinc : Monotone inc := fun _ _ h ↦ h
  have : hinc.functor.Final := (hinc.final_functor_iff).2 (by
    intro F
    obtain ⟨G, hE, hF⟩ := exists_ge_ge E F
    exact ⟨⟨G, hE⟩, hF⟩)
  let S := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (padicSubfieldRingObj X ℓ E)
  let D : I ⥤ ringedSiteModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology X)
          (padicSubfieldRingObj X ℓ E))) :=
    { obj := fun F ↦ qlbarTailStage X ℓ F.2
      map := fun {F G} h ↦ S.functor.map
        (tailRestrictedMap _ _ (padicSubfieldRingObjMap X ℓ (leOfHom h)) (by
          change (upperStarFromPoint X).map _ ≫ (upperStarFromPoint X).map _ = _
          rw [← Functor.map_comp]
          rfl))
      map_id := by
        intro F
        ext U x
        change (padicSubfieldRingObjMap X ℓ (le_refl F.1)).hom.app U x = x
        change ((upperStarFromPoint X).map (𝟙 _)).hom.app U x = x
        simp
      map_comp := by
        intro F G H a b
        ext U x
        change (padicSubfieldRingObjMap X ℓ (leOfHom (a ≫ b))).hom.app U x =
          (padicSubfieldRingObjMap X ℓ (leOfHom b)).hom.app U
            ((padicSubfieldRingObjMap X ℓ (leOfHom a)).hom.app U x)
        exact congrArg (fun t ↦ t.hom.app U x)
          ((upperStarFromPoint X).map_comp
            (Profinite.padicSubfieldRingObjMap ℓ (leOfHom a))
            (Profinite.padicSubfieldRingObjMap ℓ (leOfHom b))) }
  let c : Cocone D :=
    { pt := qlbarTailVertex X ℓ E
      ι :=
        { app := fun F ↦ S.functor.map
            (tailRestrictedMap _ _ (padicSubfieldRingObjToPadicAlgCl X ℓ F.1)
              (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ F.2))
          naturality := by
            intro F G h
            ext U x
            exact congrArg (fun t ↦ t.hom.app U x)
              (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ (leOfHom h)) } }
  let R := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (ProEt.topology X)
      (padicSubfieldRingObj X ℓ E))
  have : HasColimit D := by
    let e : D ≅ (D ⋙ SheafOfModules.forget R) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft D
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact hasColimit_of_iso e
  have : ReflectsColimit D (SheafOfModules.toSheaf R) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have hc : IsColimit c := by
    apply isColimitOfReflects (SheafOfModules.toSheaf R)
    exact (Functor.Final.isColimitWhiskerEquiv hinc.functor
      (padicAlgClRingObjCocone X ℓ)).symm (isColimitPadicAlgClRingObjCocone X ℓ)
  let d : Cocone D :=
    { pt := M
      ι :=
        { app := f
          naturality := by
            intro F G h
            ext U x
            exact hf F G (leOfHom h) U x } }
  refine ⟨hc.desc d, ?_, ?_⟩
  · intro F U x
    exact congrArg (fun t ↦ t.val.app U x) (hc.fac d F)
  · intro g hg
    apply hc.uniq d g
    intro F
    ext U x
    exact hg F U x

end AlgebraicGeometry.ProEtale
