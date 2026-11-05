/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteChoice
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftIsomorphisms

/-! # Lifting finite isomorphisms with a prescribed stable property

For Frobenius equivariance one can choose compatible equivariant isomorphisms, without first
showing that a particular canonical isomorphism commutes with coefficient reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing
open scoped CategoryTheory.Obj

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- A property stable under reduction can be imposed on every reduction of the lift. -/
theorem exists_forall_isIso_property_derivedReduction_map
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    (P : ∀ n : ℕ,
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L) → Prop)
    (hfin : ∀ n : ℕ, Finite
      ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ⟶
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))
    (hne : ∀ n : ℕ, ∃ e :
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ≅
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L,
      P n e.hom)
    (hP : ∀ n s, P (n + 1) s → P n (derivedReductionStep (n + 1) s)) :
    ∃ f : K ⟶ L, ∀ n : ℕ,
      IsIso ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f) ∧
        P n ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f) := by
  let T := fun n : ℕ ↦
    (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj K ≅
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L
  let r (n : ℕ) : T (n + 1) → T n := fun s ↦
    @asIso _ _ _ _ (derivedReductionStep (n + 1) s.hom) (isIso_derivedReductionStep (n + 1) s.hom)
  have htfin (n : ℕ) : Finite (T n) := by
    have := hfin n
    exact Finite.of_injective (fun e : T n ↦ e.hom) fun e e' h ↦ Iso.ext h
  obtain ⟨t, htP, ht⟩ := exists_compatible_choices_with_property r (fun n e ↦ P n e.hom)
    htfin hne (fun n e he ↦ hP n e.hom he)
  obtain ⟨f, hf⟩ := exists_derivedReduction_map_eq hL (fun n ↦ (t n).hom) fun n ↦ by
    rw [← congrArg Iso.hom (ht n)]
    exact Mod.map_comp_derivedReductionTransition_app _ _ _ _ _
  refine ⟨f, fun n ↦ ?_⟩
  rw [hf n]
  exact ⟨inferInstance, htP n⟩

/-- Equality of reductions detects equality when the Milnor obstruction vanishes. -/
theorem eq_of_derivedReduction_map_eq
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hL : derivedCompleteIntegers ℓ E X L)
    [∀ n : ℕ, Finite (K⟦(1 : ℤ)⟧ ⟶
      (Mod.comap (integersModPowReduction X ℓ E (n + 1))).mapDerivedCategory.obj
        ((Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.obj L))]
    {f g : K ⟶ L}
    (h : ∀ n : ℕ,
      (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map f =
        (Mod.extendScalars (integersModPowReduction X ℓ E (n + 1))).leftDerivedFunctor.map g) :
    f = g := by
  apply eq_of_comp_unit_eq hL
  intro n
  rw [(derivedReduction_map_eq_iff (n + 1) f _).1 (h n),
    (derivedReduction_map_eq_iff (n + 1) g _).1 rfl]

end AlgebraicGeometry.ProEtale
