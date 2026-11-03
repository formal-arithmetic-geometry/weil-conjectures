/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalHomDualTorAmplitude
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.AlgebraicGeometry.DualTermFiniteProjective
import WeilConjectures.AlgebraicGeometry.FiniteProjectiveComplexHomology

/-! # Finite scalar presentations for point-perfect dual cohomology

Source: current blueprint, internal-Hom stability proof, perfect-factor membership.
Only the three terms adjacent to a cohomological degree
are involved; there is no scheme or local-cover descent in this assertion.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The cohomology of the termwise dual of a finite-projective condensed scalar
complex has a finite scalar matrix presentation for admissible coefficients.
No bound on the complex is required.

Source: current blueprint, internal-Hom stability proof, paragraph 3, membership
of the perfect factors.
(blueprint: lem-sfb-admissible-point-perfect-dual-cohomology).

Proof: A finite-free condensed module has endomorphism matrices over Λ(*).
The given splittings therefore identify each of the three terms needed for H^q
with the realization of a finite projective scalar module. The differentials,
and the equations saying their composite is zero, are scalar matrices as well.
Dualizing a finite free module gives the same finite free module, and dualizing
its idempotent splitting gives the dual finite projective scalar module. Uniqueness
of right duals identifies any chosen term duals, including their signed transpose
differentials, with these scalar duals. For finite, integral, and finite-extension
coefficients the scalar ring is Noetherian. Its finite kernels and cokernels are
finitely presented. Scalar realization is exact on these scalar modules: this is
ordinary constant sheafification for finite coefficients, completion-flatness for
integral coefficients, and preservation of split exact sequences for fields.
Consequently the scalar cohomology presentation realizes to the actual condensed
homology object. For the finite-subextension-valued algebraic closure, all the
finitely many entries of these three differential matrices and the relevant
idempotents lie in one finite coefficient subextension. Compute there and extend
scalars, which is exact for fields; this uses the finite-subextension ring itself.
Finally a coefficient-ring isomorphism preserves finite free modules, cokernels,
and homology, so the conclusion transports through each isomorphism in the
admissibility predicate. Zero ranks, zero rings, and zero differentials obey the
same finite matrix calculation. -/
theorem admissiblePointPerfect_dual_cohomology
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (F : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ)
    (hF : ∀ n : ℤ, FiniteProjectiveCondensedModule (Mon.mk Λ) (F.X n))
    [∀ n : ℤ, HasRightDual (F.X n)] :
    ∀ q : ℤ, Mod.IsFinitelyPresented Λ (F.rightDual.homology q) := by
  intro q
  apply finiteProjectiveComplex_homology_finitelyPresented Λ ℓ hΛ F.rightDual
  intro n
  exact dualTerm_finiteProjective Λ (F.X (-n)) (hF (-n))


end AlgebraicGeometry.ProEtale
