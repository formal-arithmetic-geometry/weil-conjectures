/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.FieldTheory.EtaleFieldGaloisClassification
import Sheaf.AlgebraicGeometry.FieldDiscreteModules
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.RingTheory.StrictHenselizationDimension
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.Paper.FiniteCoproductCohomologyAssembly
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.StrictlyHenselianQuotient
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.OpenDegreeZeroConstructible
import Sheaf.AlgebraicGeometry.OpenImmersionRestriction
import Sheaf.RepresentationTheory.DvrGalois
import Sheaf.RingTheory.FieldAlgebraStrictHenselizationExcellent
import Sheaf.RingTheory.PuncturedCurveBranches
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# Open direct-image constructibility on arbitrary curves

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-constructible-general.md`, statement and proof
(blueprint: thm-exc-curve-open-constructible-general).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every higher direct image of a constructible finite prime-power-torsion module sheaf
along an open immersion into a finite-type scheme of dimension at most one over a finite
field or its algebraic closure is constructible.
Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-curve-open-constructible-general.md`
(blueprint: thm-exc-curve-open-constructible-general).

Proof:
1. Finite type makes T locally Noetherian by `pqf-lem-locnoeth-lft` and quasi-compact by
   `def-weil-finite-type-morphism`. Its opens are Noetherian by
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`; hence j is quasi-compact, and its
   isomorphic diagonal makes it quasi-separated. An injective resolution in nonnegative
   degrees gives zero for q < 0 (`def-weil-pbc-direct-image`). Degree zero is
   `thm-fin-open-degree-zero`, and q > 1 vanishes by `thm-exc-curve-open-dimension-general`.
   It remains to treat G = R¹j_*F.
2. Let C be the closure of U and Z = C \ U. By
   `lem-sc-noetherian-closed-subset-finite-components` and `lem-sc-scheme-sober`, their
   irreducible decompositions are finite and have generic points. Every generic point of
   a component of C lies in U by density. A nonsingleton component D of Z would have a
   proper specialization e of its generic point, giving the strict chain
   closure {e} < D < C_i. This contradicts `def-kun-topological-krull-dimension`.
   Thus Z is a finite set of closed points.
3. Restrict an injective-resolution representative j_*I to U. The counit is an isomorphism
   by `lem-kun-open-immersion-restriction`, and is A-linear with exact restriction by
   `prop-weil-pbc-inverse-image-modules-exact`. Hence its positive cohomology vanishes.
   On W = T \ C, direct image evaluates on the empty fibre product, so is zero termwise
   (`def-weil-pbc-direct-image`). Thus G is zero on T \ Z = U disjoint union W.
4. At a geometric point over t in Z, `lem-sbc-higher-direct-image-forget-comparison` and
   `prop-weil-pbc-strict-henselization-stalk-formula` identify its underlying stalk with
   H¹(U times_T Spec R, F), R the strict henselization of the local ring at t. The affine
   colimit and residue-triple identifications are `def-weil-pbc-strict-henselization-limit`,
   `lem-weil-pbc-etale-local-ring-triples` and `lem-weil-pbc-strict-henselization-triples`.
   Its closed point maps to t by `lem-weil-pbc-strict-henselization-closed-fiber-backward`.
   By `lem-kun-closed-point-field`, the residue field of t is finite over k; its separable
   closure is algebraically closed of positive characteristic. In the finite-field case,
   Frobenius is bijective on every finite subextension, hence on the separable closure;
   perfection and separable closedness imply algebraic closedness. By
   `lem-exc-field-algebra-strict-henselization-excellent`, R and its reduction B are
   excellent Noetherian. By `lem-weil-pbc-strictly-henselian-quotient`, B is strictly
   henselian local with the same residue field. By `lem-sc-strict-henselization-dimension`,
   dim R is the local dimension, at most one by the chain bound on T. Reduction preserves
   the prime spectrum and dimension.
5. Replace R by B using `lem-weil-pbc-reduction-universal-homeomorphism` and
   `prop-weil-pbc-universal-homeomorphism-topos`. The pulled-back open misses the closed
   point. If dim B = 0, B is a field and this open is empty. Otherwise
   `lem-exc-punctured-curve-branches` writes the puncture as finitely many spectra of
   fraction fields of excellent strictly henselian DVRs with the same algebraically
   closed residue field. An open is a subcoproduct of these fields, possibly empty.
6. `lem-weil-pbc-finite-coproduct-cohomology-assembly` identifies H¹ with the finite product
   of branch cohomologies. The branch pullbacks have finite fibres by
   `lem-weil-pbc-inverse-image-stalk-germ` and `def-weil-pbc-constructible-complexes`.
   By `lem-exc-field-discrete-modules`, they correspond to finite discrete continuous
   A[G_i]-modules. Exact equivalences preserve injectives and identify section complexes
   with invariants, hence identify derived cohomology with `def-exc-continuous-cohomology`.
   `lem-weil-pbc-etale-module-cohomology-forget` identifies underlying abelian groups.
   The prime is different from the residue characteristic because it is invertible on T.
   The finite-module clause of `lem-exc-dvr-galois` gives finite H¹ on each branch; their
   finite product, including the empty product, is finite.
7. Restrict G to each reduced point scheme Spec κ(t) in Z. Its geometric fibre is finite
   by step 6 and `lem-weil-pbc-inverse-image-stalk-germ`. Under
   `lem-exc-field-discrete-modules` it is a finite continuous Galois module. The intersection
   of the finitely many element stabilizers is an open normal kernel with finite quotient.
   `lem-exc-etale-field-galois-classification` supplies the finite separable extension
   corresponding to this quotient. Its spectrum is an etale cover by
   `lem-weil-pbc-finite-separable-extension-etale` and trivializes the module. Thus each
   point restriction is finite locally constant. The open T \ Z and these finitely many
   closed points form a locally closed constructible partition, by the Noetherian clause
   of `def-weil-constructible-subset`. On the open G is zero; on the points it is lisse.
   `def-weil-pbc-constructible-complexes` now gives constructibility in degree one and hence
   in every degree. -/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve
    (k : Type u) [Field k]
    (hk : Finite k ∨ ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k)
    {T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (hdim : topologicalKrullDim T ≤ 1) (j : U ⟶ T) [IsOpenImmersion j]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (ℓ : ℕ) (hprime : ℓ.Prime) (hinv : IsUnit (ℓ : Γ(T, ⊤)))
    (hkill : ∃ n : ℕ, 0 < n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
