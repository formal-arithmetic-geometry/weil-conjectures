module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated

import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.Algebra.Homology.RingedSiteGlobalHomDirectImage
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction

/-! # Perfect tensor tests detect upper bounds on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0GFH,
`proposition-detecting-bounded-above`, implication (7)(b) to (1)
(blueprint: lem-sfb-space-perfect-tensor-tests-upper-bound).

The recorded small affine etale ringed model presents the original module topos.
Its normalized closed tensor is computed on K-flat representatives. Integer-degree
hypercohomology is H⁰ RΓ of the corresponding shift, computed by K-injectives.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Separate upper bounds for all perfect tensor tests imply an upper bound for K.
The threshold is chosen after the perfect object; no common threshold is assumed.

Source: Stacks Project, Derived Categories of Spaces, Tag 0GFH,
`proposition-detecting-bounded-above`, implication (7)(b) to (1)
(blueprint: lem-sfb-space-perfect-tensor-tests-upper-bound).

Proof:
1. By lem-sfb-ringed-site-perfect-duality and
   lem-sfb-ringed-site-global-hom-direct-image, Hom(Q,E[i]) identifies with
   H^i RΓ(Q-dual tensor E). The dual of a perfect Q is perfect. The hypothesis
   therefore gives B_X(K), where B_W(E) says that each perfect Q on W has an
   individual upper bound for Hom(Q,E[i]).
2. Apply lem-sfb-space-qcqs-distinguished-square-induction to the property that
   every quasi-coherent E satisfying B_W(E) is bounded above. On an affine W,
   use Q = O_W and lem-sfb-affine-etale-derived-module-realization: derived
   global sections and the affine module realization identify all cohomology.
   This also covers the zero ring and the empty affine scheme.
3. For an elementary distinguished square U -> W <- V with V affine, use
   lem-sfb-space-supported-koszul-high-localization. Its supported perfect test
   and B_W(E) show that the actual unit E -> F = Ri_*(E|_U) is an isomorphism
   after truncation in degrees at least some a. Exact etale restriction and
   lem-sfb-space-derived-etale-chart-calculus preserve quasi-coherence;
   lem-sfb-space-qcqs-permanence and lem-sfb-space-derived-pushforward-coproducts
   ensure that F has quasi-coherent cohomology.
4. For each perfect Q take its window [c,d] from lem-sfb-space-perfect-ext-window.
   If L is the truncation below a of E or F, then for i >= a-c the cohomology
   of L[i] and L[i+1] vanishes throughout that window. Thus both Hom groups
   from Q vanish. The truncation triangle of lem-sf-derived-truncation-triangle
   and lem-weil-pbc-hom-into-triangle-exact identify the high-degree Hom groups
   of E and F. The high-truncation isomorphism therefore gives B_W(F).
5. For each perfect R on U, lem-sfb-space-perfect-open-retract supplies a
   perfect Q on W with R a retract of Q|_U. The canonical adjunction in
   lem-sfb-space-derived-etale-chart-calculus identifies Hom(Q|_U,E|_U[i])
   with Hom(Q,F[i]). Precompose with the retraction and then the section:
   every map from R to E|_U[i] is zero in high degrees. Hence B_U(E|_U).
6. The induction hypothesis gives a bound b_U for E|_U. The hypotheses of
   lem-sfb-space-derived-pushforward-upper-bound hold by step 3, so for some
   N >= 1 the cohomology of F vanishes in degrees m >= b_U+N. Taking
   b = max(a-1,b_U+N-1), the high-truncation isomorphism identifies H^m(E)
   with H^m(F) = 0 whenever m > b. This finishes the distinguished-square
   induction; apply it to K with B_X(K) from step 1.

The small ringed-model equivalence preserves cohomology, zero objects, local
finite-free retracts, the normalized derived tensor and derived global sections.
Thus the displayed vanishing conditions are those on the original small etale site. -/
theorem boundedAbove_of_perfect_tensor_tests
    (A : Type u) [CommRing A] (X : AlgebraicSpace (Spec (.of A)))
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (K : X.DerivedQCoh)
    (htests : ∀ P : X.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf P →
      ∃ bP : ℤ, ∀ i : ℤ, bP < i →
        IsZero ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
          X.smallEtaleModelTopology X.smallStructureSheaf).obj
            ((X.derivedDualityModel.closed.tensor.obj (P, K.obj))⟦i⟧))) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj K.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
