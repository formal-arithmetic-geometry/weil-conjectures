/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence


import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Spectral.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Affine-to-global cohomology over a zero-dimensional affine base

Source: Stacks Project, Tags 0A3G and 0732, and the fibre-chain dimension argument.
(blueprint: lem-sfb-zero-dimensional-base-affine-global).

Derived evaluation at an open object computes the ordinary module-derived sections of
its open slice. The ringed open comparison identifies that slice with the small
pro-etale site of the open subscheme, with the actual restricted ring and module.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- An affine-open cohomology bound gives the global bound obtained by adding the
geometric fibre dimension over a zero-dimensional affine base.

Source: Stacks Project, Tags 0A3G and 0732; Schemes Tag 01K1 and Algebra Tag 00P3.
(blueprint: lem-sfb-zero-dimensional-base-affine-global).

Proof plan:
1. Separated finite type over an affine makes X qcqs, hence its space is spectral and sober
(lem-weil-pbc-qcqs-over-affine, lem-weil-pbc-qcqs-scheme-spectral).
2. Dimension is unchanged by extension of the residue field to an algebraic closure
(lem-kun-dimension-extension), so each ordinary fibre has dimension at most e.
3. Every point of B is closed. A nonempty irreducible closed subset of X is the closure
of its generic point; its entire image therefore lies over one point of B. Every chain
of such subsets lies in one fibre, and def-pc-scheme-fibre identifies the underlying
fibre space. Thus dim X is at most e, also when X is empty.
4. The internal/sectionwise module equivalence preserves sections and restrictions,
and transports injective resolutions. Module-derived evaluation agrees with abelian
cohomology of the slice by lem-pe-ringed-site-derived-evaluation-slice. The weakly-etale
localization and ringed open comparison identify this with the actual open restriction.
5. Compose the pro-etale/etale and etale/Zariski morphisms of sites to obtain epsilon.
Its direct image evaluates on the same opens, and its abelian inverse image is exact.
6. The higher direct images are sheafifications of the open cohomology presheaves
(lem-weil-pbc-site-higher-direct-image-sheafified-presheaf). Above a these vanish on
the affine basis; their sheafifications are zero by the sheafification universal property.
7. The right adjoint epsilon_* preserves injectives, so the Grothendieck/Leray spectral
sequence has E2^(p,q) = H^p(X_Zar, R^q epsilon_* M_ab) and abuts to H^(p+q)(X_proet,M_ab).
8. Stacks 0A3G, lem-sfb-spectral-space-cohomology-dimension, kills p > e; Step 6 kills
q > a. For r > e+a every term on the r diagonal is zero. The finite exhaustive separated
filtration of the abutment has zero graded pieces, so the abutment is zero.
9. Transport back through the module/abelian comparison. No coefficient restriction,
Noetherianity, completeness or constructibility enters this argument; e=a=0 and empty
schemes are included. All degrees in the asserted range are positive, so natural-number
right-derived functors encode exactly the displayed integer-degree vanishings. -/
theorem proEtale_cohomology_vanishes_of_affine_of_zeroDimensional_base
    {B X : Scheme.{u}} [IsAffine B]
    (hB : ∀ p : PrimeSpectrum Γ(B, ⊤), p.asIdeal.IsMaximal)
    (g : X ⟶ B) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e a : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ B),
      topologicalKrullDim (pullback g b : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hlocal : ∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ, a < q →
      IsZero (((Mod.forget R ⋙ sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
        (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
          (op (Scheme.ProEt.mk U.ι))).rightDerived q).obj M))
    (r : ℕ) (hr : e + a < r) :
    IsZero (((Mod.forget R ⋙ sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 X)))).rightDerived r).obj M) := by
  sorry

end AlgebraicGeometry
