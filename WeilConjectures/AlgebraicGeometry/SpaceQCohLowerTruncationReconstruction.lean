/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.CategoryTheory.KInjectiveComputes
import WeilConjectures.CategoryTheory.SiteTruncationDerivedLimit
import WeilConjectures.CategoryTheory.TruncationsAndHomotopyColimits

/-! # Lower-truncation reconstruction on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 08F6, lemma-nice-K-injective;
Tag 08F7, lemma-application-nice-K-injective, proof (2)
(blueprint: lem-sfb-space-qcoh-lower-truncation-reconstruction).

The existing small affine ringed model implements the size convention without changing
module sections. Quasi-coherent cohomology is tested through its specified equivalence
with the original module category. Products and the Roos triangle are in the ambient
unbounded derived category, with the actual canonical truncation projections.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A complex with quasi-coherent cohomology is the derived limit of its canonical
lower truncations, with the specified first map and transition endomorphism.
Source: Stacks Project, Tag 08F6; Tag 08F7, proof (2)
(blueprint: lem-sfb-space-qcoh-lower-truncation-reconstruction).

Proof:
1. Use the small skeleton of affine objects of X_et provided by the size convention
and the existing small ringed model. Every scheme chart is covered by affine opens
(lem-weil-pbc-affine-opens-basis). Their inclusions are etale
(lem-weil-pbc-open-immersion-etale); composition remains representable etale
(lem-trf-space-representable-etale-scheme-tests). Thus these objects cover X_et,
without quasi-compactness or separation assumptions on X.
2. The slice over a scheme chart U is U_et: composition and cancellation of etale
maps identify its objects and arrows, and both coverings are jointly surjective
etale families. Both structure rings evaluate on V as Gamma(V,O_V). Quasi-coherent
local presentations restrict to the same presentations on this slice, by
relocalization (def-pur-localized-ringed-site).
3. Module sheaves form a Grothendieck category
(prop-pur-kinjective-resolutions-exist), hence have enough injectives
(lem-sp-grothendieck-enough-injectives). Module-derived evaluation is abelian
cohomology on the slice (lem-pe-ringed-site-derived-evaluation-slice).
Represent each restricted quasi-coherent cohomology module by its Zariski module
(lem-trf-scheme-zariski-etale-quasi-coherent-equivalence). Its etale cohomology is
Zariski cohomology (lem-sc-etale-zariski-qcoh-comparison), which vanishes in positive
degrees on affine U (pqf-lem-affine-vanishing). An injective resolution of a module
is K-injective and computes the same cohomology, independently of the resolution
(lem-sp-kinjective-computes (1),(2)). This supplies the section-cohomology convention
required in the next step, with bound zero in every sheaf degree.
4. Apply lem-kun-site-truncation-derived-limit with d = 0 on this equivalent small
ringed site. It gives the ambient product and a distinguished triangle whose first
map is precisely the product lift of the canonical projections and whose middle
map is 1-s. Good truncations give the standard t-structure truncations and their
canonical maps (def-kun-truncations). Hence this is the asserted specified Roos
triangle (def-weil-derived-limit), not just an isomorphism of its first object. -/
theorem qcoh_lower_truncation_isDerivedLimitTriangle
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (E : X.DerivedModules) (hE : X.derivedQCohProperty E) :
    ∃ (_ : HasProduct (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
        (C := X.SmallModules)).truncGE (-(n : ℤ))).obj E)),
      ∃ δ : (∏ᶜ (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
          (C := X.SmallModules)).truncGE (-(n : ℤ))).obj E)) ⟶ E⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
          (C := X.SmallModules)).natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
              (Int.neg_le_neg (Int.ofNat_le.mpr (Nat.le_succ n)))).app E) E
          (Pi.lift (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
            (C := X.SmallModules)).truncGEπ (-(n : ℤ))).app E)) δ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
