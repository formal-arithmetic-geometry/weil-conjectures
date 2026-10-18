/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import Sheaf.RepresentationTheory.BaseFieldContinuousCochains
import Sheaf.FieldTheory.FiniteFieldAbsoluteGalois
import Sheaf.GroupTheory.CyclicInflation
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.Etale.LocalDimension
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Uniform classical pro-étale cohomological bounds

Source: blueprint `sec-six-functors-basics/sk-prop-pe-unbounded-classical`, detail
`sk-prop-pe-unbounded-classical-bounds.md` and its proof
(blueprint: det-pe-unbounded-classical-bounds).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- The three uniform bounds in `det-pe-unbounded-classical-bounds`, for a finite-type source
and target over a finite or algebraically closed field.  The dimensions are the topological
Krull dimensions, with the empty scheme assigned dimension zero, and the bound is `2 * d + 1`.
Source: blueprint `sec-six-functors-basics/sk-prop-pe-unbounded-classical`, node
`det-pe-unbounded-classical-bounds` (blueprint: det-pe-unbounded-classical-bounds).
-/
def HasClassicalUniformBounds {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    {S R : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) (aR : R ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    [LocallyOfFiniteType aR] [QuasiCompact aR]
    (f : S ⟶ R) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsTorsion) : Prop :=
  let _ := hk
  let _ := hF
  let dS : ℕ := (topologicalKrullDim S).unbotD 0 |>.toNat
  let eS : ℕ := 2 * dS + 1
  (∀ (U : S.ProEt), proAffineEtale U.hom → ∀ q : ℤ, (eS : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} U.left).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.upperStar AddCommGrpCat.{u + 1} U.hom).obj
              ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj F)))))) ∧
    (∀ (V : R.ProEt), proAffineEtale V.hom → ∀ q : ℤ, (eS : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback f V.hom)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.upperStar AddCommGrpCat.{u + 1} (pullback.fst f V.hom)).obj
              ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj F)))))) ∧
    (∀ q : ℤ, (eS : ℤ) < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))

/-- Uniform vanishing for torsion étale sheaves over finite-type schemes over a finite or
algebraically closed field.  This is the three-part statement of
`det-pe-unbounded-classical-bounds`; the final conjunct repeats it with source `Y` and an
arbitrary finite-type map from `Y` to a finite-type `k`-scheme.

Source: blueprint `sec-six-functors-basics/sk-prop-pe-unbounded-classical`, node
`det-pe-unbounded-classical-bounds` (blueprint: det-pe-unbounded-classical-bounds).
Proof (the eleven steps of the node, with their dependency nodes):
1. Use `lem-exc-abelian-sheaves-gmodules` and `lem-exc-field-sections-stalk-invariants`
   to identify derived field sections with derived invariants. The additive equivalence
   preserves injectives by the Hom lifting criterion. Apply `det-base-field-cd-cochains`
   (1); torsion sections give torsion stalks.
2. For finite k, `det-base-field-cd-galois-group` identifies its absolute Galois group
   with the profinite integers. Every element of a discrete torsion module has finite
   orbit, generating a finite stable subgroup. Finite sums give a directed union of
   finite stable modules; use `det-base-field-cd-cochains` (2).
3. A finite stable module has exponent e and action through a finite cyclic quotient.
   Coordinate kernels are cofinal, so `det-base-field-cd-cochains` (3) computes its
   cohomology by finite quotients. Inflation to the quotient multiplied by e is zero
   in degrees at least two by `det-base-field-cd-inflation`. Every colimit class dies.
   For algebraically closed k use `lem-sf-separably-closed-torsion-cd`. Thus the
   all-torsion field dimension of `def-sc-etale-torsion-cd` is at most one.
4. `lem-kun-dimension-finite-type` gives finite dimension, agreeing with
   `def-kun-dimension` and `def-kun-topological-krull-dimension`; nonempty schemes have
   a length-zero chain by `lem-sc-scheme-sober`. Finite-type schemes over k are
   Noetherian by `lem-weil-pbc-finite-type-over-noetherian`. Each affine etale stage
   is finite type over k. For the products with X, finite affine covers over affine
   opens of Y give a finite affine cover using
   `lem-weil-pbc-fibre-product-affine-spectra`. The projection to X is etale by
   `lem-weil-pbc-etale-base-change-finite-limits`, hence finite type over k. The stages
   are qcqs: use `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` for compact
   opens and `lem-weil-pbc-locally-noetherian-quasi-separated`.
5. `lem-sc-etale-local-dimension` identifies the local dimensions of etale source
   and target. `lem-sc-scheme-stalk-dimension-generalization-chains`, generic points
   from `lem-sc-scheme-sober`, and the topological dimension definition bound every
   finite irreducible chain in an etale stage by the source dimension. This also
   applies to the product stages by etale base change; no separatedness is needed.
6. `thm-sc-finite-type-torsion-cd` with field bound one gives the common stage bound
   `2 * d + 1`. Empty stages have zero sections by the empty covering axiom.
   `lem-weil-pbc-inverse-image-torsion` keeps the pulled-back coefficients torsion.
7. `lem-sc-cd-affine-limit` gives the bound for U. Apply
   `lem-weil-pbc-comparison-pullback` to the etale pullback of G, and
   `lem-weil-proetale-weakly-etale-localization` to identify restriction to U.
   The inverse-image Kan colimit is evaluation: (W, graph) is initial before
   taking the opposite category. `sk-prop-sf-comparison` for the discrete ring
   of integers and the degree-zero complex identifies pro-etale and etale cohomology.
8. The fibre-product universal property identifies X times V with the limit of
   X times the V_i. Transition maps are affine by base change, using
   `lem-weil-pbc-affine-morphism-permanence`. These stages are qcqs with the bound
   from step 6, so `lem-sc-cd-affine-limit` gives the same bound on the product.
9. Its etale pullback coefficient is torsion. Use
   `lem-weil-pbc-comparison-pullback` and `sk-prop-sf-comparison` on this scheme,
   again only for G in degree zero, to obtain clause 2.
10. `lem-weil-pbc-higher-direct-image-sheafified-presheaf` identifies the higher
    image with the sheafified cohomology presheaf. Use
    `lem-weil-pbc-cohomology-over-object-localization`,
    `lem-weil-pbc-etale-site-localization-open`, and
    `lem-weil-pbc-etale-inverse-image-restriction` to identify coefficients.
    On affine etale target objects steps 4--6 give zero above the bound.
    Every etale object has an affine open covering, so this presheaf is locally
    zero. By the universal property in `def-weil-pbc-sheafification` its
    sheafification is zero, proving clause 3.
11. For empty X, all schemes in clauses 1--2 are empty, hence have zero sections
    and cohomology; direct image out of the zero sheaf category is zero as well.
    Thus the explicit empty bound one works. Repeat with source Y and an arbitrary
    finite-type target and map to obtain the last conjunct (including the identity).
-/
theorem classicalUniformBounds {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    HasClassicalUniformBounds hk aX aY g G hG ∧
      ∀ {Z : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
        [LocallyOfFiniteType aZ] [QuasiCompact aZ]
        (h : Y ⟶ Z) [LocallyOfFiniteType h] [QuasiCompact h]
        (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (hH : H.IsTorsion),
        HasClassicalUniformBounds hk aY aZ h H hH := by
  sorry

end AlgebraicGeometry.ProEtale

end
