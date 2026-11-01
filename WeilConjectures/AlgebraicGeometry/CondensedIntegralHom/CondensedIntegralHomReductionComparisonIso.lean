/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! The coefficient comparison isomorphism needed by integral Hom reduction.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-hom-reduction.proof.md, first paragraph after the adjunction.
(blueprint: lem-coef-integral-hom-reduction-comparison-isIso).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedIntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The canonical evaluation-defined Hom reduction arrow `comparison n K L` is invertible, for
arbitrary (unbounded) `K` and `L`; no perfectness of `K` is assumed.

Source: blueprint proof of lem-coef-integral-hom-reduction, first paragraph
(blueprint: lem-coef-integral-hom-reduction-comparison-isIso).

Proof:
1. The two-term finite-free complex `[R --pi^(n+1)--> R]` resolves `A_(n+1)`;
   `principal_cone_tensor_normalization` at index `n` identifies it with `- tensor A_(n+1)`,
   with the canonical reduction maps. So `A_(n+1)` is perfect over `R`.
2. Represent `K` by a K-flat complex `P` and `L` by a K-injective complex `I`. Coning only the
   second variable, `Hom(P, Cone(pi^(n+1) on I))` is termwise `Cone(pi^(n+1) on Hom(P,I))` with
   the same signs (`homComplex_mappingCone_iso`). This gives an isomorphism
   `theta_n : Hom(K,L) tensor A_(n+1) ≅ Hom(K, L tensor A_(n+1))`, the transpose of evaluation
   tensored with `A_(n+1)` after reassociation.
3. The derived extension--restriction internal-Hom identity along `R → A_(n+1)` gives
   `Res Hom_(A_(n+1))(K_(n+1), L_(n+1)) ≅ Hom(K, Res L_(n+1))`, the unique one whose transpose is
   restricted evaluation after the unit. Composing its inverse with `theta_n` is the restriction
   of `comparison n K L`, because both are transposes of the same evaluation. Restriction is
   conservative, so `comparison n K L` is an isomorphism. -/
theorem comparison_isIso (n : ℕ)
    (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    IsIso (comparison l E X n K L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralHom
