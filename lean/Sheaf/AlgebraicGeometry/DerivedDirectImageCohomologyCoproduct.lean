/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum
import Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.Paper.HigherDirectImagePresheaf

/-! # Cohomology of a derived direct-image coproduct

Source: Stacks Project, Tags 08DZ and 08D5
(blueprint: lem-pc-derived-direct-image-cohomology-coproduct).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical direct-sum map on the cohomology sheaves of derived direct image
is an isomorphism in a fixed integer degree. Here `S` is the ambient derived coproduct;
its quasi-coherence is a consequence of the coproduct hypothesis, not an extra assumption.
Source: Stacks Project, Derived Categories of Schemes, Tag 08DZ, proof, with Tag 08D5(2)
(blueprint: lem-pc-derived-direct-image-cohomology-coproduct).

Proof. First choose representatives and use `derivedAmbientDirectSums`: the cohomology
of S is the direct sum of the cohomologies of E i, compatibly with the given maps ι.
Finite sums of quasi-coherent modules are quasi-coherent, and their directed colimit over
finite subsets of I is quasi-coherent by the affine-section colimit theorem. Thus S has
quasi-coherent cohomology, also for the empty family.

It suffices to check the sheaf map on affine opens V of Y. Restriction is exact and
preserves sums, and a restricted K-injective complex remains K-injective, so restriction
identifies derived direct image with that for f over V. The scheme f⁻¹V is qcqs. The
uniform cohomological bound of 08D5(2) supplies one bound N depending on this restricted
morphism, independent of i. Enlarge N so that the upper-truncation term in the triangle
τ≤(-N-1)E → E → τ≥(-N)E is sent to an object with zero cohomology in degrees q and q+1.
The long exact sequence identifies R^q f_*E with R^q f_*τ≥(-N)E, naturally, for every
summand and S. Exact sums imply that truncation commutes with this coproduct, so all
complexes now have a common cohomological lower bound a = -N.

Apply the natural bounded-below truncation spectral sequence, whose E₂ page is
R^p f_*H^r(E). On each affine open W of V, qcqs cohomology commutes with the direct sum
of the quasi-coherent H^r(E i). The higher-direct-image presheaf theorem and module-sheaf
colimit formula sheafify these compatible maps, proving commutation of R^p f_* with the
sheaf coproduct. Hence the E₂ comparison is an isomorphism. Exact sums identify kernels
and images of the differentials, so each later page comparison is an isomorphism. In
total degree q only 0 ≤ p ≤ q-a occurs; the finite filtrations given by convergence
therefore have isomorphic graded pieces. Induction using the short exact sequences of
successive filtration terms makes the comparison on the abutments an isomorphism.
Naturality identifies it with Sigma.desc of the maps induced by ι. Undo truncation and
restriction to conclude on Y. If q<a the bounded-below abutments are zero; for an empty
family the same argument compares zero objects. No compactness of Y is required because
N is chosen separately over each affine open. -/
theorem derivedDirectImage_cohomology_coproduct
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (q : ℤ) :
    IsIso (Sigma.desc (fun i ↦ (schemeHigherDirectImage f q).map (ι i))) := by
  sorry

end AlgebraicGeometry
