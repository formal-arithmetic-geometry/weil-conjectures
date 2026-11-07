/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Lifting isomorphisms of reductions by König's lemma

Let `K` and `L` be complexes of `𝒪_{E,X}`-module objects on `X_proét` with `L` derived complete,
and write `red_n` for the derived reduction modulo `ℓⁿ`. If for every `n ≥ 1` the reductions
`red_n K` and `red_n L` are isomorphic and there are only finitely many morphisms
`red_n K ⟶ red_n L`, then there is a morphism `f : K ⟶ L` whose reductions `red_n f` are all
isomorphisms (`ProEtale.exists_forall_isIso_derivedReduction_map`).

The isomorphisms `red_{n+1} K ≅ red_{n+1} L` form an inverse system of nonempty finite sets under
reduction `red_{n+1} ⟶ red_n` (`Mod.derivedExtendScalarsReduction`), which has a compatible
family by König's lemma (`nonempty_sections_of_finite_inverse_system`); a compatible family
lifts to `L` (`ProEtale.exists_derivedReduction_map_eq`). No choice of the isomorphisms is
canonical: this is used to prove *properties* (e.g. dualizability), never to construct data.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

open scoped CategoryTheory.Obj

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The reduction `red_n s` of a morphism `s : red_{n+1} K ⟶ red_{n+1} L` along
`𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`. -/
noncomputable abbrev derivedReductionStep (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (s : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L) :
    (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctor.obj L :=
  Mod.derivedExtendScalarsReduction _ (integersModPowTransition X ℓ E n) _
    (integersModPowReduction_comp_integersModPowTransition X ℓ E n) s

lemma isIso_derivedReductionStep (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (s : (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)
    [IsIso s] : IsIso (derivedReductionStep n s) := by
  dsimp only [derivedReductionStep, Mod.derivedExtendScalarsReduction]
  infer_instance

set_option maxHeartbeats 1000000 in
-- the reductions `red_{n+1}` are elaborated at several levels
/-- **Lifting isomorphisms of reductions** (König's lemma): if `L` is derived complete, and for
every `n` the reductions `red_{n+1} K`, `red_{n+1} L` are isomorphic with finitely many morphisms
between them, there is `f : K ⟶ L` all of whose reductions are isomorphisms. -/
theorem exists_forall_isIso_derivedReduction_map
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    (hfin : ∀ n : ℕ, Finite
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))
    (hne : ∀ n : ℕ, Nonempty
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ≅
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L)) :
    ∃ f : K ⟶ L, ∀ n : ℕ,
      IsIso ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map
        f) := by
  let T := fun n : ℕ ↦
    (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ≅
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L
  let r (n : ℕ) : T (n + 1) → T n := fun s ↦
    @asIso _ _ _ _ (derivedReductionStep (n + 1) s.hom) (isIso_derivedReductionStep (n + 1) s.hom)
  let F : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (X := T) fun n ↦ TypeCat.ofHom (r n)
  have : ∀ j, Finite (F.obj j) := fun j ↦ by
    have := hfin j.unop
    exact Finite.of_injective (fun e : T j.unop ↦ e.hom) fun e e' h ↦ Iso.ext h
  have : ∀ j, Nonempty (F.obj j) := fun j ↦ hne j.unop
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let t (n : ℕ) : T n := s (op n)
  have ht (n : ℕ) : r n (t (n + 1)) = t n := by
    have := hs (homOfLE (Nat.le_add_right n 1)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact this
  obtain ⟨f, hf⟩ := exists_derivedReduction_map_eq hL (fun n ↦ (t n).hom) fun n ↦ by
    rw [← congrArg Iso.hom (ht n)]
    exact Mod.map_comp_derivedReductionTransition_app _ _ _ _ _
  exact ⟨f, fun n ↦ (hf n) ▸ inferInstance⟩

end AlgebraicGeometry.ProEtale
