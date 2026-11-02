/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Data.Matrix.Mul
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedDetection
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-! # Direct finiteness of constructible condensed coefficient complexes

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence.
The finiteness argument is the agent-formulated ingredient recorded in the DAG.
(blueprint: lem-sf-condensed-constructible-direct-finiteness).

The ordinary derived category uses the existing internal-module presentation of module
sheaves. Its exact sectionwise equivalence is supplied by
`InternalModuleOperations.equivalence`; no completion condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A left inverse of an endomorphism of a bounded finite-constant-model constructible
complex over the condensed algebraic closure is also a right inverse.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
agent-formulated finiteness ingredient of native cone detection.
(blueprint: lem-sf-condensed-constructible-direct-finiteness).

Proof plan (the six steps of the DAG):
1. Transport internal modules to sectionwise module sheaves with
`lem-sfb-internal-module-operations-transport`. Exact pullback is supplied by
`det-prop-sfb-module-pullback-exact-main`, with composition comparisons from
`def-sfb-module-upper-star-comp`. For each integer q, apply cohomology to a and b to obtain
endomorphisms u and v of M = H^q(K) satisfying vu = 1. Work separately in every degree.
2. Use `sk-def-sfb-constructible` to choose a finite constructible locally closed
stratification for M and finite constant local models on pro-etale covers of its strata.
Each finitely presented scalar vector space has a finite basis (discard dependent vectors
from a finite generating list). The isomorphism clause of
`lem-sfb-constant-finite-free-presentation-extension` identifies its scalar extension with
a finite free coefficient module, including rank zero, without assuming flatness.
3. On each covering object W, evaluate the conjugated endomorphisms on every object V of
its slice site. These are linear maps on B(V)^r, where B is the commutative coefficient
ring sheaf. Their matrices D and A satisfy DA = 1. Apply
`lem-sf-commutative-square-matrix-direct-finiteness` to obtain AD = 1, including empty
matrices. Thus uv = 1 on the module sheaf over W.
4. `lem-sfb-proetale-object-inverse-image-restriction` identifies underlying abelian
inverse image to a covering object with restriction. The sheaf uniqueness axiom on each
base-changed covering family descends uv = 1 to the entire stratum.
5. Exact pullback makes ker u and coker u zero on every stratum. The scheme is qcqs by
`lem-weil-pbc-locally-noetherian-quasi-separated`. Refine the finite stratification using
`lem-fix-constructible-open-closed-refinement`. Nonempty leaves factor through original
strata, and composition comparisons give zero restriction; empty leaves have zero
abelian sheaves since the empty family covers the empty scheme. Induct up the finite
binary tree using `lem-exc-open-closed-detection` at every complementary qc open/closed
pair. Both kernel and cokernel vanish, so u is invertible.
6. This holds for every q, including zero cohomology. Apply
`lem-weil-pbc-unbounded-derived-iso-cohomology` to show that a itself is invertible in the
ordinary derived category. The equation ba = 1 then forces b = a⁻¹, hence ab = 1. This
uses the isomorphism criterion, not faithfulness of cohomology on derived morphisms. -/
theorem condensed_constructible_direct_finiteness (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)))
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X K)
    (a b : K ⟶ K) (hba : a ≫ b = 𝟙 K) : b ≫ a = 𝟙 K := by
  sorry

end AlgebraicGeometry.ProEtale
