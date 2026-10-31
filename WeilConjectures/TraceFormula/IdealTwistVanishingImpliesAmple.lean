/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives

/-! # Vanishing of ideal twists implies ampleness

Source: Stacks Project, `coherent.tex`, Tag 0B5U, lemma-vanshing-gives-ample,
implication (3) ⇒ (1) (blueprint: lem-trf-ideal-twist-vanishing-implies-ample).
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Vanishing of first cohomology of every quasi-coherent ideal twist implies absolute ampleness.

Source: Stacks Project, `coherent.tex`, Tag 0B5U, lemma-vanshing-gives-ample,
implication (3) ⇒ (1) (blueprint: lem-trf-ideal-twist-vanishing-implies-ample).

Proof: Properness over the affine spectrum of a Noetherian ring gives quasi-compactness.
For each closed point, choose an affine neighbourhood and the reduced vanishing ideals of its
complement and of its complement together with the point.  Their quotient has a section with
residue one at the point.  Tensor the resulting short exact sequence by a suitable positive
power of the invertible module.  The assumed vanishing of the first cohomology of the smaller
ideal lifts this quotient section to a global section of the power, whose nonvanishing locus is
affine and contains the point.  The affine nonvanishing loci cover all closed points, and the
quasi-compact Kolmogorov closed-point argument shows that they cover the whole scheme.  These
are exactly the clauses in the absolute ampleness predicate.
-/
theorem idealTwistVanishing_implies_isAmple
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of R)) [IsProper f]
    (L : X.Modules) [L.IsInvertible]
    (h : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      ∃ n : ℕ, 0 < n ∧
        Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (Scheme.Modules.tensorObj I.toModules (L.tensorPow n)))) :
    Scheme.Modules.IsAmple X L := by
  sorry

end AlgebraicGeometry
