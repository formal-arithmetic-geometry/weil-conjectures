/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
import Sheaf.CategoryTheory.Galois.CoproductMorphismComponents

/-!
# Consequences of the Stacks Galois category axioms

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN0 and the paragraph
following it (blueprint: lem-galois-axioms).
-/

@[expose] public section

universe wI wJ w v u

open CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- (blueprint: lem-galois-axioms) Stacks, paragraph after Lemma 0BN0.
A Galois object of a Stacks Galois category is a connected object whose
automorphism group has the same cardinality as its fibre. -/
def IsStacksGaloisObject {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) (X : C) : Prop :=
  IsConnected X ∧ Nat.card (Aut X) = Nat.card (F.obj X)

/-- (blueprint: lem-galois-axioms) Stacks, Lemma 0BN0 and the paragraph after it.
For a Galois category with fibre functor `F`, the seven conjuncts give faithfulness;
detection of monos and epis; detection of initial and terminal objects; epis between
connected objects; determination of a map on a connected source by one fibre element;
the automorphism bound and its transitivity criterion; and the component description
of maps between finite coproducts of connected objects.

For faithfulness, apply `F` to an equalizer and reflect its resulting isomorphism.
For mono and epi detection, apply `F` to the diagonal into a pullback and the fold
map out of a pushout, respectively, then reflect isomorphisms. An initial or terminal
object has empty or singleton fibre; conversely, compare an object with such a fibre
to an initial or terminal object and reflect the resulting bijection. For a map between
connected objects, the equalizer of its cokernel-pair maps is noninitial and hence
isomorphic to the target, giving epi. If two maps agree on one fibre element, their
equalizer is noninitial and hence isomorphic to the connected source. Evaluation at
one element is therefore injective on automorphisms; finiteness gives the cardinal
bound, with equality exactly when its orbit is the whole fibre. Finally, the
component description of maps between finite coproducts of connected objects is
`CategoryTheory.morphism_coproduct_connected_components`
(blueprint: lem-galois-coproduct-morphism-components). -/
theorem stacksGaloisCategory_axioms
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F) :
    Functor.Faithful F ∧
    (∀ {X Y : C} (f : X ⟶ Y),
      (Mono f ↔ Function.Injective (F.map f)) ∧
      (Epi f ↔ Function.Surjective (F.map f))) ∧
    (∀ X : C,
      (Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)) ∧
      (Nonempty (IsTerminal X) ↔
        ∃ s : F.obj X, ∀ t : F.obj X, t = s)) ∧
    (∀ {X Y : C}, IsConnected X → IsConnected Y →
      ∀ f : X ⟶ Y, Epi f) ∧
    (∀ {X Y : C}, IsConnected X →
      ∀ (a b : X ⟶ Y) (s : F.obj X), F.map a s = F.map b s → a = b) ∧
    (∀ X : C, IsConnected X → ∀ s : F.obj X,
      Function.Injective (fun g : Aut X => F.map g.hom s) ∧
      Nat.card (Aut X) ≤ Nat.card (F.obj X) ∧
      (IsStacksGaloisObject F X ↔ Nat.card (Aut X) = Nat.card (F.obj X)) ∧
      (IsStacksGaloisObject F X ↔
        ∀ t : F.obj X, ∃ g : Aut X, F.map g.hom s = t)) ∧
    (∀ (I : Type wI) (J : Type wJ) [Finite I] [Finite J]
      (Xi : I → C) (Yj : J → C) (X Y : C)
      (ιX : ∀ i, Xi i ⟶ X) (ιY : ∀ j, Yj j ⟶ Y),
      Nonempty (IsColimit (Cofan.mk X ιX)) →
      Nonempty (IsColimit (Cofan.mk Y ιY)) →
      (∀ i, IsConnected (Xi i)) → (∀ j, IsConnected (Yj j)) →
      ∀ f : X ⟶ Y,
        ∃ (α : I → J) (component : ∀ i, Xi i ⟶ Yj (α i)),
          ∀ i, ιX i ≫ f = component i ≫ ιY (α i)) := by
  have : HasFiniteLimits C := hG.hasFiniteLimits
  have : HasFiniteColimits C := hG.hasFiniteColimits
  have : PreservesFiniteLimits F := hG.preservesFiniteLimits
  have : PreservesFiniteColimits F := hG.preservesFiniteColimits
  have : F.ReflectsIsomorphisms := hG.reflectsIsomorphisms
  have hfaithful : F.Faithful := ⟨fun {X Y} a b h ↦ by
    have : IsIso (equalizer.ι (F.map a) (F.map b)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι a b)) := by
      rw [← equalizerComparison_comp_π a b F]
      exact IsIso.comp_isIso
    have : IsIso (equalizer.ι a b) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer⟩
  have hinitial (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
    rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
    exact Types.initial_iff_empty _
  have hterminal (X : C) : Nonempty (IsTerminal X) ↔
      ∃ s : F.obj X, ∀ t : F.obj X, t = s := by
    rw [(IsTerminal.isTerminalIffObj F X).nonempty_congr]
    constructor
    · rintro ⟨h⟩
      let huniq := Types.isTerminalEquivUnique _ h
      exact ⟨huniq.default, huniq.uniq⟩
    · rintro ⟨s, hs⟩
      exact ⟨(Types.isTerminalEquivUnique _).symm ⟨⟨s⟩, hs⟩⟩
  have hevaluation {X Y : C} (hX : IsConnected X) (a b : X ⟶ Y)
      (s : F.obj X) (h : F.map a s = F.map b s) : a = b := by
    have : IsIso (equalizer.ι a b) := by
      apply hX.noTrivialComponent _ (equalizer.ι a b)
      intro hi
      have hempty := (hinitial (equalizer a b)).mp ⟨hi⟩
      let e : F.obj (equalizer a b) ≅ {t : F.obj X // F.map a t = F.map b t} :=
        PreservesEqualizer.iso F a b ≪≫ Types.equalizerIso (F.map a) (F.map b)
      exact hempty.false (e.inv ⟨s, h⟩)
    exact eq_of_epi_equalizer
  have hnonempty {X : C} (hX : IsConnected X) : Nonempty (F.obj X) := by
    by_contra h
    obtain ⟨hi⟩ := (hinitial X).mpr (not_nonempty_iff.mp h)
    exact hX.notInitial hi
  refine ⟨hfaithful, ?_, fun X ↦ ⟨hinitial X, hterminal X⟩, ?_,
    @hevaluation, ?_, ?_⟩
  · intro X Y f
    constructor
    · constructor
      · intro h
        have : Mono (F.map f) := preserves_mono_of_preservesLimit F f
        exact (mono_iff_injective _).mp inferInstance
      · intro h
        have : Mono (F.map f) := (mono_iff_injective _).mpr h
        exact Functor.mono_of_mono_map F (inferInstance : Mono (F.map f))
    · constructor
      · intro h
        have : Epi (F.map f) := preserves_epi_of_preservesColimit F f
        exact (epi_iff_surjective _).mp inferInstance
      · intro h
        have : Epi (F.map f) := (epi_iff_surjective _).mpr h
        exact Functor.epi_of_epi_map F (inferInstance : Epi (F.map f))
  · intro X Y hX hY f
    obtain ⟨s⟩ := hnonempty hX
    exact ⟨fun {Z} a b h ↦ hevaluation hY a b (F.map f s) (by
      simpa only [F.map_comp, types_comp_apply] using congrArg (fun g ↦ F.map g s) h)⟩
  · intro X hX s
    have : Finite (F.obj X) := hG.finite_obj X
    have hinj : Function.Injective (fun g : Aut X ↦ F.map g.hom s) := by
      intro a b h
      exact Iso.ext (hevaluation hX a.hom b.hom s h)
    have hcard : IsStacksGaloisObject F X ↔
        Nat.card (Aut X) = Nat.card (F.obj X) := ⟨And.right, fun h ↦ ⟨hX, h⟩⟩
    refine ⟨hinj, Nat.card_le_card_of_injective _ hinj, hcard, ?_⟩
    rw [hcard]
    exact ⟨fun h ↦ ((Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, h⟩).2,
      fun h ↦ Nat.card_eq_of_bijective _ ⟨hinj, h⟩⟩
  · intro I J _ _ Xi Yj X Y ιX ιY hX hY hXi hYj f
    exact morphism_coproduct_connected_components F hG hX.some hY.some hXi hYj f

end CategoryTheory
