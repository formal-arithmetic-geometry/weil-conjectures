/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible

/-! # Weak contractibility of the separable generic point -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- The separable generic point of an integral scheme is weakly contractible.
Every covering sieve contains its identity. The singleton identity family is a
covering family of monomorphisms, with vacuous pairwise disjointness, contained
in the sieve. Apply the existing disjoint-cover criterion for weak contractibility.
Source: the geometric generic point in the scope counterexample,
`literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`.
(blueprint: lem-sf-generic-point-sep-weakly-contractible) -/
theorem genericPointSepWeaklyContractible
    {X : Scheme.{u}} [IsIntegral X] :
    (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.genericPointSep X) := by
  refine GrothendieckTopology.isWeaklyContractible_of_forall_mem (fun S hS ↦ ?_)
  let T := Scheme.ProEt.genericPointSep X
  refine ⟨PUnit.{u + 1}, fun _ ↦ T, fun _ ↦ 𝟙 T, ?_, ?_, ?_, ?_⟩
  · rw [Sieve.ofArrows, Presieve.ofArrows_pUnit,
      Sieve.generate_of_singleton_isSplitEpi]
    exact (Scheme.ProEt.topology X).top_mem T
  · intro i
    exact Scheme.ProEt.id_mem_genericPointSep X hS
  · intro i
    infer_instance
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim


end AlgebraicGeometry
