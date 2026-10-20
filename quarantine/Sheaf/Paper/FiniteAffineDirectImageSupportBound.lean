/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Perverse.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.GroupTheory.Exponent
import WeilConjectures.AlgebraicGeometry.EtaleSupport
import Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The finite-coefficient affine direct-image support estimate

Source: BBD, Faisceaux pervers, Theorem 4.1.1 and its cohomology-sheaf reduction;
Stacks Project, Etale Cohomology, Tag 0F0X, lemma-interlude-I
(blueprint: lem-per-finite-affine-direct-image-support-bound).

The ordinary bounded-below derived direct image preserves the support condition.
The support is closed support, as in the existing finite-coefficient `SupportCondition`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An affine finite-type k-morphism between separated finite-type k-schemes sends
bounded-below complexes with constructible cohomology satisfying the support condition
to bounded constructible complexes satisfying the same condition. The finite coefficient
ring has additive exponent invertible in k. All derived categories here are the ordinary
small-etale derived categories of module sheaves.

Source: BBD, Theorem 4.1.1; Stacks Project, Tag 0F0X, lemma-interlude-I
(blueprint: lem-per-finite-affine-direct-image-support-bound).

Proof:
1. Put F_i = H^{-i}(L). For i < 0 the closed support has negative dimension, so is empty:
a nonempty space has dimension at least zero. Geometric-stalk conservativity
(lemma-weil-pbc-geometric-stalk-conservative) gives F_i = 0. The bounded-below hypothesis
bounds the other end, so only finitely many F_i, indexed by 0 <= i <= N, can be nonzero.
Thus L is bounded constructible; the zero complex permits N = 0.
2. The positive additive exponent e of the finite ring annihilates every section and
is invertible in k. Apply thm-dg-finite-type-constructibility to L and each F_i in degree
zero: Rf_*L and Rf_*F_i are bounded constructible. In particular all R^q f_*F_i are
constructible. Both schemes are Noetherian by lem-weil-pbc-finite-type-over-noetherian,
and are qcqs by finite type and separatedness.
3. If x has nonzero stalk in F_i, it belongs to its closed support Z_i. Its closure lies
in Z_i. By lem-sc-closed-irreducible-dimension-trdeg, trdeg_k kappa(x) <= dim Z_i <= i.
Thus the stalk support of the underlying torsion abelian sheaf lies in E_i(X).
4. Use lem-sbc-higher-direct-image-forget-comparison to identify the underlying abelian
sheaf of R^q f_*F_i. The estimate lem-kun-affine-direct-image-support-bound, applied to
that torsion sheaf, puts its stalk support in E_{i-q}(Y), empty when i-q < 0.
5. Its closed support Z is the closure of that stalk support S: a restriction vanishes
exactly when all its geometric stalks vanish. By
lem-weil-pbc-constructible-module-support-constructible, S is constructible. By
lem-sc-noetherian-closed-subset-finite-components and lem-sc-scheme-sober, Z is a finite
union of irreducible closed components C_j with generic points eta_j.
6. Every eta_j lies in S. Remove the other components to see that S intersect C_j is
dense in C_j. Express S as a finite union of locally closed subsets. Irreducibility
forces one of their intersections with C_j to be dense. A dense locally closed subset
is open in C_j and contains eta_j. This uses def-weil-constructible-subset; no closedness
of stalk support is assumed.
7. Steps 4 and 6 give dim C_j = trdeg_k kappa(eta_j) <= i-q. A chain in a finite union
of closed subsets lies in one component, so dim Z <= i-q. If i-q < 0 then S and Z are
empty and the sheaf vanishes by geometric-stalk conservativity.
8. The derived direct image commutes with shifts and distinguished triangles by
lem-weil-pbc-derived-direct-image-triangulated. For q = i-m, H^{-m}(Rf_*(F_i[i])) is
R^q f_*F_i. Step 7 bounds its closed support by m for q >= 0. For q < 0 it vanishes,
as a nonnegative injective resolution of F_i computes its right derived direct image.
9. The condition is extension closed: the long exact cohomology sequence from
lem-weil-heart-short-exact-triangles shows that the middle support in a triangle lies
in the union of the two outer supports. A finite union preserves the dimension bound.
10. Use the standard truncation triangles, def-sbc-standard-tstructure-derived-category
and lem-weil-heart-short-exact-triangles. Starting with zero below degree -N, finitely
many triangles build L from the F_i[i]. Applying Rf_* and steps 8-9 proves the support
condition; bounded constructibility was established in step 2. No finite Tor-amplitude
or separable-closure hypothesis is used. -/
theorem supportCondition_rightDerivedLowerStarPlus_of_isAffine
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : IsUnit (AddMonoid.exponent Λ : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsAffineHom f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hconstructible : ∀ r : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) r).obj L.obj))
    (hsupport : DerivedCategory.SupportCondition L.obj) :
    DerivedCategory.isBoundedConstructible Λ Y
        (((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj L).obj) ∧
      DerivedCategory.SupportCondition
        (((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj L).obj) := by
  sorry

end AlgebraicGeometry.Etale
