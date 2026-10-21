/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.AdicNormalizedFibreData

/-! # Local normalized lattice comparison

Source: Bhatt--Scholze, §6.8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Local lattice charts and their natural intrinsic-fibre normalization.
Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Corollary 5.1.5.
(blueprint: lem-per-intrinsic-local-lattice-comparison).

Proof: realize a heart object as its constructible degree-zero sheaf. Choose its finite
lisse stratification, an etale lattice cover of the stratum containing the point, and an
affine refinement with a geometric lift. The completed-system equivalence supplies the
lattice reduction cone, its quotient and scalar equations, and finite free stalks.
For any specified chart and lattice presentation, compose ordinary balanced module
inverse images to the geometric point. The pullback compatibility of the reduction
equivalence identifies the pulled lattice with the inverse limit of the constant
finite-level stalk sheaves. Evaluate the corresponding finite free module at the final
object and rationalize to obtain E tensor_A lim N_n,x. This pulls back the reductions
before taking the limit; it does not interchange arbitrary stalks and limits.
Naturality of the cone identifies integral maps with inverse-limit maps. The constant
scalar action commutes with module inverse image and evaluation, so division by a
uniformizer power gives the asserted fractional map equation. All comparisons pass
through the same intrinsic fibre, giving independence from charts and presentations. -/
theorem intrinsic_local_lattice_comparison (X : Base.{u} l)
    (k : Type u) [Field k] [X.scheme.Over (Spec (.of k))]
    [LocallyOfFiniteType (X.scheme ↘ Spec (.of k))]
    [QuasiCompact (X.scheme ↘ Spec (.of k))]
    [IsSeparated (X.scheme ↘ Spec (.of k))] (hl : IsUnit (l : k))
    (R : Family.{u} l) :
    Nonempty (LocalLattices l E X (R.realization E X)) := by sorry

end AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre
