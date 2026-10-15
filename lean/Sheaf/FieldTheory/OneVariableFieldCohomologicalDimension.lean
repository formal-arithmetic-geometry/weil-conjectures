/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.RatFunc.Basic
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit

/-!
# Torsion étale cohomological dimension of a one-variable field

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-sc-one-variable-field-cd.md (blueprint: lem-sc-one-variable-field-cd).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- If `F` is separably closed, the rational function field `F(x)` has torsion étale
cohomological dimension at most one, in the ordinary derived-section sense.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-sc-one-variable-field-cd.md`
(blueprint: lem-sc-one-variable-field-cd).

Proof plan:
1. Index by finite subsets `S` of the nonzero polynomials in `F[x]`, and let `h_S` be
   their product (one for the empty subset). The rings `F[x, 1/h_S]` have filtered
   colimit `F(x)`, since every denominator appears at a singleton stage. By
   lem-weil-pbc-spec-colimit-limit their spectra have limit `Spec F(x)` and affine
   transition maps. The stages are quasi-compact and quasi-separated by
   lem-weil-pbc-affine-scheme-qcqs.
2. The algebraic closure `L` of `F` is purely inseparable: in characteristic zero
   `L = F`; in characteristic `p`, every algebraic element has a `p`-power in `F`.
   For any `F`-algebra `R`, the map to `R ⊗[F] L` is injective and every element of
   the tensor product has a `p`-power in `R`. A prime of `R` has a unique prime
   above it, consisting of elements with a suitable power in that prime; taking
   common exponents proves independence, ideal closure and primality. Basic opens
   correspond under the same power operation. Hence this map on spectra is a
   homeomorphism after every base change. By
   thm-weil-pbc-universal-homeomorphism-invariance the stage and its base change
   have equivalent étale topoi and the same cohomology. The additive equivalence
   preserves local torsion, expressed as the filtered union of the kernels of
   multiplication by `n!`, so it preserves the bound of def-sc-etale-torsion-cd.
3. Over `L`, the stages are affine, separated, finite-type schemes of dimension at
   most one: the product remains nonzero, the algebra has generators `x` and
   `1/h_S`, and localization of the polynomial PID has dimension at most one.
   Apply lem-sc-arbitrary-curve-cd with dimension bound one, then transfer back to
   `F` by step 2.
4. Finite subsets form a filtered index under union. The affine transitions,
   quasi-compact quasi-separated stages and uniform bound one satisfy
   lem-sc-cd-affine-limit. The limit `Spec F(x)` has the same bound, which is the
   claimed field bound by def-sc-etale-torsion-cd. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_ratFunc
    (F : Type u) [Field F] [IsSepClosed F] :
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of (RatFunc F))) 1 :=
  sorry

end AlgebraicGeometry.Scheme
