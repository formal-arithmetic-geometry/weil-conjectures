/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Homology.ExactSequence
/-! # Transport of localization across equivalent coefficient presentations -/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u v
namespace AlgebraicGeometry.ProEtale
private theorem exact_localization_transport
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D A' D' : C} (f : A ⟶ B) (g : B ⟶ D)
    [Mono f] [Epi g] (h : (ComposableArrows.mk₂ f g).Exact)
    (a : A' ≅ A) (d : D' ≅ D) :
    Mono (a.hom ≫ f) ∧ Epi (g ≫ d.inv) ∧
      (ComposableArrows.mk₂ (a.hom ≫ f) (g ≫ d.inv)).Exact := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  let e : ComposableArrows.mk₂ (a.hom ≫ f) (g ≫ d.inv) ≅
      ComposableArrows.mk₂ f g :=
    ComposableArrows.isoMk₂ a (Iso.refl B) d
      (by change (a.hom ≫ f) ≫ 𝟙 B = a.hom ≫ f; rw [Category.comp_id])
      (by
        change (g ≫ d.inv) ≫ d.hom = 𝟙 B ≫ g
        rw [Category.assoc, d.inv_hom_id, Category.comp_id, Category.id_comp])
  exact ComposableArrows.exact_of_iso e.symm h

private def openAdjunctionTransport
    {C O S : Type u} [Category.{v} C] [Category.{v} O] [Category.{v} S]
    (Q : O ≌ S) (F : C ⥤ O) (A : S ⥤ C) (R : C ⥤ S)
    (a : A ⊣ R) (e : F ⋙ Q.functor ≅ R) : Q.functor ⋙ A ⊣ F := by
  let b := Q.toAdjunction.comp (a.ofNatIsoRight e.symm)
  let d : (F ⋙ Q.functor) ⋙ Q.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F Q.unitIso.symm ≪≫ Functor.rightUnitor F
  exact b.ofNatIsoRight d

private theorem openAdjunctionTransport_counit
    {C O S : Type u} [Category.{v} C] [Category.{v} O] [Category.{v} S]
    (Q : O ≌ S) (F : C ⥤ O) (A : S ⥤ C) (R : C ⥤ S)
    (a : A ⊣ R) (e : F ⋙ Q.functor ≅ R) (L : C) :
    (openAdjunctionTransport Q F A R a e).counit.app L =
      A.map (e.hom.app L) ≫ a.counit.app L := by
  suffices A.map (Q.functor.map (Q.unit.app (F.obj L))) ≫
      A.map (Q.counit.app (Q.functor.obj (F.obj L))) ≫
      A.map (e.hom.app L) ≫ a.counit.app L = A.map (e.hom.app L) ≫ a.counit.app L by
    simpa [openAdjunctionTransport, Category.assoc] using this
  rw [← Category.assoc, ← Category.assoc, ← A.map_comp]
  have hz : Q.functor.map (Q.unit.app (F.obj L)) ≫
      Q.counit.app (Q.functor.obj (F.obj L)) = 𝟙 _ := Q.functor_unit_comp (F.obj L)
  rw [hz, A.map_id, Category.id_comp]

/-- A localization sequence is unchanged by equivalences on its two supported
categories. Source: Stacks Project, Tag 09AH, and elementary adjunction calculus
(blueprint: lem-weil-pbc-localization-equivalence-transport).
Proof: transport the open adjunction through Q and the displayed restriction
comparison. Its counit is A applied to the comparison, followed by the old
counit. Compose the closed adjunction with the scalar adjunction. Its unit is
the old unit followed by D applied to the scalar unit; this last map is an
isomorphism because the scalar right adjoint is an equivalence. The resulting
three-term sequence is isomorphic to the original sequence, with the middle
isomorphism the identity. Monicity, epicity and exactness transport along it. -/
theorem localization_equivalence_transport
    {C O S I Z : Type u} [Category.{v} C] [Category.{v} O] [Category.{v} S]
    [Category.{v} I] [Category.{v} Z] [HasZeroMorphisms C]
    (Q : O ≌ S) (F : C ⥤ O) (A : S ⥤ C) (R : C ⥤ S)
    (aj₀ : A ⊣ R) (e : F ⋙ Q.functor ≅ R)
    (FC : C ⥤ I) (D : I ⥤ C) (ai₀ : FC ⊣ D)
    (E : I ⥤ Z) (RC : Z ⥤ I) (aE : E ⊣ RC) [RC.IsEquivalence]
    (h : ∀ L, Mono (aj₀.counit.app L) ∧ Epi (ai₀.unit.app L) ∧
      (ComposableArrows.mk₂ (aj₀.counit.app L) (ai₀.unit.app L)).Exact) :
    ∃ (aj : Q.functor ⋙ A ⊣ F) (ai : FC ⋙ E ⊣ RC ⋙ D),
      ∀ L, Mono (aj.counit.app L) ∧ Epi (ai.unit.app L) ∧
        (ComposableArrows.mk₂ (aj.counit.app L) (ai.unit.app L)).Exact := by
  let aj := openAdjunctionTransport Q F A R aj₀ e
  let ai := ai₀.comp aE
  refine ⟨aj, ai, ?_⟩
  intro L
  obtain ⟨hf, hg, hex⟩ := h L
  let := hf
  let := hg
  let d := (D.mapIso (asIso (aE.unit.app (FC.obj L)))).symm
  have ht := exact_localization_transport (aj₀.counit.app L) (ai₀.unit.app L)
    hex (A.mapIso (e.app L)) d
  simpa only [aj, ai, openAdjunctionTransport_counit, Adjunction.comp_unit_app,
    Functor.mapIso_hom, d, Iso.symm_inv, asIso_hom, Iso.app_hom] using ht

end AlgebraicGeometry.ProEtale
