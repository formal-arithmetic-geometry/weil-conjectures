/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularImmersionChart
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale

/-!
# Purity for regular closed immersions: `cl_i` is an isomorphism

Let `i : Z ⟶ X` be a regular closed immersion of pure codimension `c`, with `X` smooth over a
perfect field `k` and `Z` regular. The morphism `cl_i : Λ_Z ⟶ Ri^! (Λ_X(c)[2c])`, `1 ↦ [Z ⊂ X]`,
adjoint to the fundamental class (`AlgebraicGeometry.Etale.fundamentalClassMap`), is an
isomorphism (clause (c) of blueprint `sk-thm-regular`); in particular `[Z ⊂ X]` generates the
cohomology sheaf `𝓗⁰(Ri^! Λ_X(c)[2c])` at every geometric point (clause (b)).

This is Step 4 of the proof. The question is étale-local on `Z`. Near every point of `Z` there
is a Zariski frame `(U, f₁, …, f_c)` of `Z` together with an étale map
`u : U ⟶ 𝔸^c_B`, `B = 𝔸^m_k`, whose `c` fibre coordinates `t_a` pull back to the `f_a`
(`AlgebraicGeometry.IsRegularImmersion.exists_etale_affineSpace`). The frame class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` is the restriction along `u` of the class `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)` of the
zero section of `𝔸^c_B` (`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct`),
whose adjoint is an isomorphism by the model computation of `sk-prop-an`
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord`). Restriction of
supports along an étale map is an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_etale`), so the adjoint of a class is an
isomorphism after étale restriction if and only if the class's adjoint is so there
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_restrictSupportedClass_iff`). Applying this
twice — along `u` and along the frame `U ⟶ X` — shows that `cl_i` becomes an isomorphism on a
Zariski cover of `Z`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_fundamentalClassMap`: clause (c).
- `AlgebraicGeometry.Etale.isIso_homology_zero_map_fundamentalClassMap`: clause (b), generation.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_fundamentalClassMap`: finite reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

attribute [local instance] HasInvertibleExponent.opens

end Etale

end AlgebraicGeometry
