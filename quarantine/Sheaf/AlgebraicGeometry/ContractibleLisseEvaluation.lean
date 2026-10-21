/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel

import Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction
import Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect
public import Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Perfect complexes and dualizable objects under contractible evaluation

Source: Hemo--Richarz--Scholbach, Section 3, (3.1)--(3.2), Remark 3.2,
Lemma 4.1 and Proposition 4.3(3)
(blueprint: lem-zl-contractible-lisse-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Duality

variable {V W : Type*} [Category* V] [Category* W]
  [MonoidalCategory V] [MonoidalCategory W]

private noncomputable def dualHomEquiv (X X' Y : V) [ExactPairing X X'] :
    (X ⟶ Y) ≃ (𝟙_ V ⟶ Y ⊗ X') :=
  (Iso.homCongr (λ_ X).symm (Iso.refl Y)).trans
    (tensorRightHomEquiv (𝟙_ V) X X' Y)

private theorem dualHomEquiv_apply (X X' Y : V) [ExactPairing X X'] (f : X ⟶ Y) :
    dualHomEquiv X X' Y f = η_ X X' ≫ f ▷ X' := by
  apply (tensorRightHomEquiv (𝟙_ V) X X' Y).symm.injective
  simp only [dualHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
  exact (tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight f).symm

private theorem dualHomEquiv_map (H : V ⥤ W) [H.Monoidal]
    (X X' Y : V) [ExactPairing X X'] (f : X ⟶ Y) :
    let := ExactPairing.map H X X'
    dualHomEquiv (H.obj X) (H.obj X') (H.obj Y) (H.map f) =
      Functor.LaxMonoidal.ε H ≫ H.map (dualHomEquiv X X' Y f) ≫
        Functor.OplaxMonoidal.δ H Y X' := by
  let := ExactPairing.map H X X'
  dsimp only
  rw [dualHomEquiv_apply, dualHomEquiv_apply]
  change (Functor.LaxMonoidal.ε H ≫ H.map (η_ X X') ≫
    Functor.OplaxMonoidal.δ H X X') ≫ H.map f ▷ H.obj X' = _
  simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight, Category.assoc]
  simp only [Functor.Monoidal.μ_δ, Category.comp_id]

private theorem monoidal_map_bijective (H : V ⥤ W) [H.Monoidal]
    (h : ∀ Y : V, Function.Bijective (H.map : (𝟙_ V ⟶ Y) → _))
    (X Y : V) (hX : IsDualizable X) :
    Function.Bijective (H.map : (X ⟶ Y) → _) := by
  obtain ⟨hX⟩ := hX
  let := hX
  let := ExactPairing.map H X Xᘁ
  let e := dualHomEquiv X Xᘁ Y
  let e' := dualHomEquiv (H.obj X) (H.obj Xᘁ) (H.obj Y)
  let post := Iso.homCongr (Functor.Monoidal.εIso H).symm
    (Functor.Monoidal.μIso H Y Xᘁ).symm
  have hb := post.bijective.comp ((h (Y ⊗ Xᘁ)).comp e.bijective)
  have heq : post ∘ H.map ∘ e = e' ∘ H.map := by
    funext f
    exact (dualHomEquiv_map H X Xᘁ Y f).symm
  rw [heq] at hb
  exact (e'.bijective.of_comp_iff' _).mp hb

omit [MonoidalCategory V] [MonoidalCategory W] in
private theorem right_adjoint_map_bijective {L : W ⥤ V} {H : V ⥤ W}
    (adj : L ⊣ H) [IsIso adj.unit] (X : W) (Y : V) :
    Function.Bijective (H.map : (L.obj X ⟶ Y) → _) := by
  let e := (adj.homEquiv X Y).trans
    (Iso.homCongr (asIso (adj.unit.app X)) (Iso.refl (H.obj Y)))
  have he : (H.map : (L.obj X ⟶ Y) → (H.obj (L.obj X) ⟶ H.obj Y)) = e := by
    funext f
    simp [e, Iso.homCongr_apply, Adjunction.homEquiv_unit]
  rw [he]
  exact e.bijective

omit [MonoidalCategory V] [MonoidalCategory W] in
private theorem map_bijective_of_iso (H : V ⥤ W) {X X' Y : V} (e : X ≅ X')
    (h : Function.Bijective (H.map : (X' ⟶ Y) → _)) :
    Function.Bijective (H.map : (X ⟶ Y) → _) := by
  let a := Iso.homCongr e (Iso.refl Y)
  let b := Iso.homCongr (H.mapIso e).symm (Iso.refl (H.obj Y))
  have hb := b.bijective.comp (h.comp a.bijective)
  convert hb using 1
  funext f
  simp [a, b, Iso.homCongr_apply, Functor.map_comp]

private theorem right_adjoint_dualizable_bijective {L : W ⥤ V} {H : V ⥤ W}
    [L.Monoidal] [H.Monoidal] (adj : L ⊣ H) [IsIso adj.unit]
    (X Y : V) (hX : IsDualizable X) :
    Function.Bijective (H.map : (X ⟶ Y) → _) := by
  apply monoidal_map_bijective H _ X Y hX
  intro Z
  exact map_bijective_of_iso H (Functor.Monoidal.εIso L)
    (right_adjoint_map_bijective adj (𝟙_ W) Z)

omit [MonoidalCategory V] [MonoidalCategory W] in
private theorem restriction_equivalence {L : V ⥤ W} {H : W ⥤ V}
    (adj : L ⊣ H) [IsIso adj.unit] (P : ObjectProperty V) (Q : ObjectProperty W)
    (hL : ∀ X, P X → Q (L.obj X)) (hH : ∀ X, Q X → P (H.obj X))
    (hmap : ∀ X Y, Q X → Q Y → Function.Bijective (H.map : (X ⟶ Y) → _)) :
    ∃ e : P.FullSubcategory ≌ Q.FullSubcategory,
      Nonempty (e.functor ⋙ Q.ι ≅ P.ι ⋙ L) ∧
      Nonempty (e.inverse ⋙ P.ι ≅ Q.ι ⋙ H) := by
  let L' := Q.lift (P.ι ⋙ L) (fun X ↦ hL X.obj X.property)
  let H' := P.lift (Q.ι ⋙ H) (fun X ↦ hH X.obj X.property)
  let adj' : L' ⊣ H' := adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
    (Iso.refl _) (Iso.refl _)
  let := adj.fullyFaithfulLOfIsIsoUnit.full
  let := adj.fullyFaithfulLOfIsIsoUnit.faithful
  let : H'.Full := ⟨fun {X Y} f ↦ by
    obtain ⟨g, hg⟩ := (hmap X.obj Y.obj X.property Y.property).2 f.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩⟩
  let : H'.Faithful := ⟨fun {X Y} {f g} h ↦ by
    apply ObjectProperty.hom_ext
    apply (hmap X.obj Y.obj X.property Y.property).1
    exact congrArg (fun k ↦ k.hom) h⟩
  exact ⟨adj'.toEquivalence, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

end Duality

private theorem perfect_iff_dualizable
    {R : Type (u + 1)} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R)]
    (Q : DerivedCategory (ModuleCat.{u + 1} R)) :
    DerivedCategory.IsPerfectRingComplex Q ↔ IsDualizable Q := by
  rw [← DerivedCategory.dualizable_iff_isPerfectRingComplex Q]
  constructor
  · rintro ⟨D, ev, coev, hQ, hD⟩
    let h : ExactPairing Q D := {
      evaluation' := ev
      coevaluation' := coev
      evaluation_coevaluation' := by
        apply (cancel_epi (λ_ Q).inv).1
        apply (cancel_mono (ρ_ Q).hom).1
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id] using hQ
      coevaluation_evaluation' := by
        apply (cancel_epi (ρ_ D).inv).1
        apply (cancel_mono (λ_ D).hom).1
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id] using hD }
    exact ⟨{ rightDual := D, exact := h }⟩
  · rintro ⟨hQ⟩
    let := hQ
    refine ⟨Qᘁ, ε_ Q Qᘁ, η_ Q Qᘁ, ?_, ?_⟩
    · simp only [ExactPairing.evaluation_coevaluation_assoc, Iso.inv_hom_id, Category.comp_id]
    · simp only [ExactPairing.coevaluation_evaluation_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem realization_triangulated
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U) :
    ∃ (_ : (Evaluation.F J O U hU).CommShift ℤ),
      (Evaluation.F J O U hU).IsTriangulated := by
  obtain ⟨hshift, htri⟩ := (Evaluation.extensionModel J O U hU).triangulated
  let := hshift
  let := htri
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let := Functor.additive_of_preserves_binary_products e.inverse
  dsimp only [Evaluation.F, commutativeSiteDerivedConstantModuleFunctor]
  exact ⟨inferInstance, inferInstance⟩

/-- Contractible derived evaluation identifies perfect complexes with lisse objects.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1)--(2)
(blueprint: lem-zl-contractible-lisse-evaluation).

Proof: the realization adjunction has invertible unit, so realization is fully
faithful. Its constant, derived extension, and coefficient equivalence factors
are triangulated. Both realization and sections preserve duals by their strong
monoidal structures. Ring dualizability is equivalent to perfection. For a
dualizable X, its two duality identities identify maps X to Y with maps from
the unit to Y tensor the dual of X. Sections induce a bijection on the latter
maps by the adjunction at the unit, since realization preserves the unit.
Thus sections are fully faithful on dualizable objects. Restrict the adjunction
to the two full subcategories. Both restricted functors are fully faithful,
so their restricted unit and counit give the required equivalence. -/
theorem contractible_lisse_evaluation
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Evaluation.ringSheaf J O)))]
    (heval : ContractibleDerivedSectionsTensor.{u + 1, u, 0}
      J (Evaluation.ringSheaf J O) (op U)) : Evaluation.Statement J O U hU := by
  obtain ⟨adj, hunit, hF, ⟨hG⟩⟩ :=
    Evaluation.contractible_realization_adjunction J O U hU heval
  let := hunit
  refine ⟨⟨adj.fullyFaithfulLOfIsIsoUnit⟩, realization_triangulated J O U hU, hF, ?_⟩
  let := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} (Evaluation.A J O U))
  let := DerivedCategory.braidedCategory' (Mod (Sheaf J Ab.{u + 1}) O)
  obtain ⟨hF⟩ := hF
  let := hF
  let := hG
  apply restriction_equivalence adj (Evaluation.perfect J O U) (Evaluation.lisse J O)
  · intro X hX
    exact ((perfect_iff_dualizable X).mp hX).map (Evaluation.F J O U hU)
  · intro X hX
    exact (perfect_iff_dualizable _).mpr (hX.map (Evaluation.G J O U))
  · intro X Y hX _
    exact right_adjoint_dualizable_bijective adj X Y hX

end AlgebraicGeometry.ProEtale.CondensedRing
