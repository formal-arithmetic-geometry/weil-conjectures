/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Generic inclusions with filtered source

Source: Stacks Project, Tags 01YE and 01YF, generic-point ideal inclusion and cokernel reduction.
(blueprint: lem-pc-s3-coherent-generic-filtered-extension)
-/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A generic ideal-sum inclusion with filtered source and smaller-support cokernel.

Source: Stacks Project, Tag 01YE and Tag 01YF, final generic-point paragraph
(https://stacks.math.columbia.edu/tag/01YE).
(blueprint: lem-pc-s3-coherent-generic-filtered-extension)

Proof: give T its reduced induced closed subscheme structure i : Z -> X.
Generic-point uniqueness identifies i(genericPoint Z) with ξ, and Z is integral.
Tag 01YE applied to the generic-annihilation hypothesis constructs a coherent
ideal I on Z, a finite rank r and a mono alpha : i_*(I^r) -> F which is an
isomorphism near ξ. Since ξ belongs to Supp F, its stalk is nonzero; consequently
r is positive and I is nonzero. Closed pushforward preserves coherence and
finite sums. The partial-sum chain of copies of i_*I therefore gives a coherent
integral filtration of A = i_*(I^r), each quotient being i_*I. Set Q to the actual
cokernel of alpha and g to its cokernel projection. Coherent cokernel closure
gives coherence of Q, and the mono alpha makes its cokernel sequence short
exact. Stalk exactness gives Supp Q contained in Supp F = T, while invertibility
near ξ gives Q_xi = 0. Since ξ belongs to T, containment is strict. This proves
the assertions without support induction and without claiming a filtration of F.
There is no zero-support case because a generic point belongs to its closed set. -/
theorem coherent_generic_filtered_extension
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj F, a • m = 0) :
    ∃ (A Q : X.Modules) (f : A ⟶ F) (g : F ⟶ Q) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      RingedSpace.IsCoherent X.toRingedSpace A ∧
      RingedSpace.IsCoherent X.toRingedSpace Q ∧ HasCoherentIntegralFiltration A ∧
      {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊂ (T : Set X) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
