/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePerfectSupportExtension
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport

/-! # Perfect complexes on quasi-compact opens are retracts of global restrictions

Source: Stacks Project, Derived Categories of Spaces, Tag 09IX,
`lemma-direct-summand-of-a-restriction`
(blueprint: lem-sfb-space-perfect-open-retract).

The categories use the existing equivalent small affine etale ringed models.
For the open immersion, the canonical derived tensor pullback is exact restriction
on the small etale site. The open subspace is specified by its inclusion, using the
same representability-by-open-immersions predicate as `OpenSubspace`.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A perfect complex on a quasi-compact open is a retract of a global perfect restriction.
Source: Stacks Project, Derived Categories of Spaces, Tag 09IX,
`lemma-direct-summand-of-a-restriction`, via Tag 09IV with zero target and full support
(blueprint: lem-sfb-space-perfect-open-retract).

Proof:
1. For a quasi-compact open W containing U, require a perfect B on W with A a retract
   of B restricted to U. At W = U use A and identity maps. Apply
   lem-sfb-space-qc-open-enlargement-induction. Its step is a distinguished square
   W1 contained in W2 with an affine etale chart V; H = W1 times_W2 V is a
   quasi-compact open subscheme of V.
2. Restrict B to H. It is perfect and has quasi-coherent cohomology by
   lem-sfb-space-perfect-objects-compact. Transport to the Zariski site by
   lem-sfb-derived-etale-zariski-equivalence and lem-sfb-etale-detects-perfect.
   Apply lem-sc-affine-perfect-support-extension on V with full support to obtain
   D0 whose restriction is F0 direct-sum F0[1]. By lem-sc-perfect-qcoherent, D0
   lies in the quasi-coherent comparison category. Transport it back to an etale
   perfect D. The natural pullback comparison identifies its restriction to H
   with (B direct-sum B[1]) restricted to H.
3. Invert this overlap isomorphism and use lem-sfb-space-distinguished-derived-gluing
   to glue B direct-sum B[1] and D to R on W2. The square covers W2: by
   lem-sfb-space-reduced-closed-support, its closed complement is covered by V.
   Both restrictions of R are perfect, so their local bounded finite-free-summand
   models exhibit R as perfect on W2.
4. Restrict the gluing isomorphism e to U. The new section is the old section
   followed by the first biproduct inclusion and e inverse. The new retraction
   is e followed by the first projection and the old retraction. Their composite
   is the identity, by the biproduct identities and the old retraction equation.
5. The enlargement induction therefore reaches X and gives Q and the required
   section and retraction for the original A. Empty opens and the zero complex
   are included throughout; no nonemptiness hypothesis is needed. -/
theorem exists_perfect_open_retract
    {S : Scheme.{u}} (X U : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    (hXqc : CompactSpace (Point X.obj.obj)) (hXqs : IsAbsolutelyQuasiSeparated X)
    (i : U ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) i.hom.hom)
    (hUqc : CompactSpace (Point U.obj.obj)) (A : U.DerivedModules)
    (hA : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      U.smallStructureSheaf A) :
    ∃ Q : X.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf Q ∧
      ∃ (s : A ⟶ (derivedTensorPullback i).obj Q)
        (r : (derivedTensorPullback i).obj Q ⟶ A), s ≫ r = 𝟙 A := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
