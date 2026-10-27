/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! # Proper direct image of bounded below coherent complexes

Source: Stacks Project, Perfect Complexes, Tag 0D0B
(lemma-direct-image-coherent-bdd-below), specialized to a proper morphism.
(blueprint: lem-sfb-proper-scheme-coherent-derived-image).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper derived direct image preserves coherent cohomology and boundedness below.
Source: Stacks Project, Perfect Complexes, Tag 0D0B, using Tag 08E2 and the
truncation spectral sequence of Tag 015J.
(blueprint: lem-sfb-proper-scheme-coherent-derived-image).

Proof:
1. Choose a lower bound a for G and a representative zero in degrees below a by
   def-sbc-standard-tstructure-derived-category. Module sheaves are Grothendieck abelian
   by lem-weil-pbc-ring-sheaves-grothendieck. Direct image is additive and left exact:
   lem-weil-pbc-ringed-topoi-module-adjunction gives its right-adjoint description, and
   lem-weil-pbc-right-adjoint-preserves-limits gives finite-limit preservation.
2. Apply thm-sp-truncation-e2 to obtain E₂^{p,q} = R^p f_* H^q(G) converging to
   H^{p+q}(Rf_*G), for the K-injective derived image def-pc-derived-direct-image.
   Terms vanish unless p >= 0 and q >= a. The filtration of H^n has F^0 = H^n,
   F^p = 0 for p >= n-a+1, and graded pieces E∞^{p,n-p}.
3. By lem-pc-coherent-hi, the nonnegative higher direct images of each coherent H^q(G)
   are coherent: f is proper and S locally Noetherian. Negative columns are zero and
   coherent by lem-weil-pbc-coherent-modules-kernel-cokernel-sum.
4. Induct through the pages using coherent kernels and cokernels, then use stabilization
   to obtain coherent E∞ terms. For n >= a, descend through the finite filtration from
   F^{n-a+1} = 0 to F^0 = H^n using coherent extension closure. All these closure steps
   use lem-weil-pbc-coherent-modules-kernel-cokernel-sum.
5. For n < a, the filtration identities give F^0 = 0 and hence H^n(Rf_*G) = 0.
   This is coherent too; thus all cohomology sheaves are coherent and bounded below. -/
theorem proper_scheme_coherent_derived_image
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (G : schemeDerivedCategory X)
    (hcoherent : ∀ j : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj G))
    (hbelow : ∃ a : ℤ, ∀ j : ℤ, j < a → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj G)) :
    (∀ j : ℤ, RingedSpace.IsCoherent S.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) j).obj
          ((schemeDerivedDirectImage f).obj G))) ∧
    (∃ a : ℤ, ∀ j : ℤ, j < a → IsZero
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) j).obj
          ((schemeDerivedDirectImage f).obj G))) := by
  sorry

end AlgebraicGeometry
