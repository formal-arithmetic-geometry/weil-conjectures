/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral
public import Sheaf.AlgebraicGeometry.CurveOpenConstructibleGeneral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds
import Sheaf.AlgebraicGeometry.DirectImageFinitenessInput
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.Etale.LocalDimension
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing

/-!
# Open-complement bounds over an algebraic closure of a finite field

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`lem-exc-open-complement-known.md`, statement and proof Steps 1-15
(blueprint: lem-exc-open-complement-known).

The independent dimension-zero and curve conclusions are included alongside the general bound.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact open immersion into a finite-type scheme of dimension at most `d`
over an algebraic closure of a finite field satisfies the open-complement condition with
bound `2 * d`. In dimension zero its direct image is exact extension by zero and preserves
constructibility, and the bound is zero. In dimension at most one the bound is already one.

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/lem-exc-open-complement-known.md`
(blueprint: lem-exc-open-complement-known).

Proof:
1. The algebraic closure k is separably closed (`def-pc-separably-closed`). Choose a
   positive exponent r killing A, enlarging any given exponent, even when A is zero.
   The integer N = ell^r is invertible in k and annihilates every section of an A-module.
2. The open immersion j is finite type (`lem-weil-pbc-qc-open-immersion-finite-type`).
   A finite affine cover of T and quasi-compactness of j give a finite affine cover of V
   (`lem-pqf-finite-affine-cover-qc-open`). Its rings are finite type over k by
   `lem-weil-pbc-lft-affine-pairs`, so V is finite type over k.
3. The open-subspace dimension inequality
   (`lem-weil-pbc-open-subspace-dimension-monotone`) gives dim V <= dim T <= d.
4. Apply clause (1) of `thm-exc-direct-image-input-holds`, with the coefficient data
   of `def-exc-direct-image-input`, to obtain constructibility in nonnegative degrees.
5. Negative degrees vanish by `lem-weil-pbc-derived-functor-negative-vanishing`, since
   j_* is additive and left exact (`def-weil-pbc-direct-image`) on Grothendieck abelian
   categories (`lem-weil-pbc-module-sheaves-grothendieck-abelian`). Zero is constructible
   by `def-weil-pbc-constructible-complexes`, including on the empty scheme.
6. For an affine etale U over T, its etale affine charts are finitely presented over
   affine charts of T (`def-weil-etale-morphism`, `def-sbc-locally-finite-presentation`).
   Their rings are finite type over k (`lem-weil-pbc-lft-affine-pairs`). Quasi-compactness
   of U (`lem-weil-pbc-affine-scheme-qcqs`) supplies a finite subcover, proving U/k finite type.
7. Identify local rings in etale affine charts by
   `lem-weil-pbc-affine-open-stalk-localization`. Their dimensions agree by
   `lem-sc-etale-local-dimension`. Taking suprema (`lem-pc-scheme-dimension-local-rings`)
   gives dim U <= dim T, including empty U.
8. The open W = V times_T U is quasi-compact by
   `lem-weil-pbc-open-immersion-base-change` and `lem-pc-quasi-compact-base-change`.
   Its finite affine cover and the same finite-type criterion show W/k finite type;
   the open-subspace inequality gives dim W <= d.
9. For q > 2d and an arbitrary A-module sheaf, its restriction to W is torsion killed
   by N (`lem-weil-pbc-etale-base-change-finite-limits`,
   `lem-weil-pbc-etale-inverse-image-restriction`). Clause (2) of the direct-image input
   gives H^q(W, M) = 0. By `sbc-lem-higher-direct-image-presheaf`, these are values of the
   presheaf whose sheafification is the abelian higher direct image.
10. Affine etale objects cover (`lem-weil-pbc-affine-etale-essentially-small-cover`).
    Any map from that locally zero presheaf to a sheaf is zero, since restrictions are
    jointly injective (`def-weil-pbc-abelian-etale-sheaves`). The universal property
    `def-weil-pbc-sheafification` makes its sheafification zero.
11. `lem-sbc-higher-direct-image-forget-comparison` then gives zero module higher image;
    every section module of its underlying zero abelian sheaf is zero.
12. Combine constructibility and vanishing to obtain `def-exc-open-complement-bound`
    with c = 2d. Empty V and empty T are covered by the same argument.
13. Independently, finite type over the Noetherian Spec k makes T Noetherian
    (`lem-weil-pbc-finite-type-over-noetherian`). If dim T <= 0, its space is finite
    discrete (`lem-sc-zero-dim-noetherian-finite-discrete`). The open image of j is closed,
    and the structure-sheaf map is surjective, so j is a closed immersion. The complementary
    clopen subschemes give the disjoint decomposition T = V disjoint union W.
14. By `lem-weil-pbc-etale-sheaf-clopen-product`, coefficient sheaves decompose into
    pairs on V and W, with A-actions componentwise. The evaluation formula of
    `def-weil-pbc-direct-image` identifies j_* with M |-> (M, 0), hence with extension
    by zero, an exact functor. Enough injectives
    (`lem-weil-pbc-module-sheaves-enough-injectives`) and
    `lem-sc-exact-functor-higher-derived-vanishing` give positive-degree vanishing.
    Degree zero is j_* by its injective resolution, and Step 5 gives negative vanishing.
    Extend a finite constructible stratification by the complementary zero stratum;
    `def-weil-pbc-constructible-complexes` gives constructibility and bound c = 0.
15. Independently, if dim T <= 1, ell is invertible on T because it is nonzero in k.
    Apply `thm-exc-curve-open-dimension-general` for vanishing above one and
    `thm-exc-curve-open-constructible-general` for constructibility in every degree.
    Together these give the open-complement condition with c = 1, independently of
    the general direct-image input. For d = 0 use the stronger bound of Steps 13-14. -/
theorem hasOpenComplementCondition_of_isAlgClosure_finite_and_lowDimension
    (k : Type u) [Field k]
    (hk : ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k)
    {T V : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)
    (hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0) :
    HasOpenComplementCondition A j (2 * d) ∧
      (topologicalKrullDim T ≤ 0 →
        IsClosedImmersion j ∧
        PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) j) ∧
        Nonempty (Etale.lowerStar (ModuleCat.{u + 1} A) j ≅
          Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j) ∧
        (∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          IsConstructibleEtaleModuleSheaf F →
            IsConstructibleEtaleModuleSheaf
              ((Etale.lowerStar (ModuleCat.{u + 1} A) j).obj F)) ∧
        HasOpenComplementCondition A j 0) ∧
      (topologicalKrullDim T ≤ 1 → HasOpenComplementCondition A j 1) := by
  sorry

end AlgebraicGeometry.Scheme
