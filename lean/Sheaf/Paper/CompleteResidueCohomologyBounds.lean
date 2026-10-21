/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Cohomological bounds from complete residue Tor amplitude

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1) and (2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

The completion is the inverse limit of constant quotient ring sheaves, not the
constant sheaf of the valuation ring. Level zero of the reduction API means the
positive exponent one, hence the residue field. No characteristic, constructibility,
or local constancy condition is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- A derived-complete complex has the same cohomological bounds as a Tor interval
of its residue reduction, tested after restriction to every small-site object.

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1),(2);
sites-cohomology.tex, Tags 0942 and 0947; algebraization.tex, Tag 099I
(blueprint: lem-sf-complete-residue-cohomology-bounds).

Proof:
1. Test residue Tor amplitude with the coefficient sheaf itself on X. The tensor
unit identity gives vanishing of residue cohomology outside [a,b].
2. Choose one flat-term K-flat resolution P by lem-pc-kflat-resolution. By
lem-pur-derived-change-of-rings its reductions compute every K_n. Their actual
chain maps 1_P tensor (C_(n+1) to C_n) give the canonical quotient transitions.
3. The DVR coefficient sequence 0 to k_X to C_(n+1) to C_n to 0 is short exact:
the first map sends r to varpi^n r; cancellation proves injectivity and identifies
its image with the quotient kernel. Surjectivity and these identities pass to
constant sheaves locally. Compatibility of the limit projections makes the maps
B_X-linear (def-weil-l-adic-coefficient-extension, def-weil-pbc-constant-sheaf).
4. Flatness of each term of P preserves this exact sequence
(def-pc-flat-sheaf-modules). Apply lem-weil-pbc-complex-ses-triangle and
lem-sf-derived-homology-long-exact to obtain the cohomology exact sequences.
5. Induction gives cohomology in [a,b] for all K_n. The exact sequence in degree b
also makes each canonical transition on H^b epimorphic.
6. Apply det-pe-milnor-sequence to this strict tower. By det-pe-products-derived,
its termwise product represents the product in D(Mod(B_X)), and localization
identifies 1-T with the tower transition endomorphism. Rotating the cone triangle
gives a Roos triangle (def-weil-abstract-derived-category,
def-weil-triangulated-category, def-weil-derived-limit). Completeness and the
uniqueness clause of lem-weil-derived-limit-existence identify K up to isomorphism
with this Milnor middle term.
7. For j<a and j>b+1 both outer Milnor terms vanish. At j=b+1, the right term is
zero and det-pe-milnor-epimorphic kills R^1 lim H^b(K_n), since its transitions are
epimorphic. Exactness gives the asserted vanishing in every remaining degree. -/
theorem complete_residue_cohomology_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X]
    (K : @DerivedCategory (integralTowerModules.{u, u} l E X) _
      (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
        (completedIntegralCoefficientSheafUnrestricted l E X)
        (integralCoefficientAbSheafify.{u, u} X)
        (integralCoefficientAbLocallyBijective.{u, u} X))
      (integralTowerHasDerivedCategory.{u, u} l E X))
    (_hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hTor : ∀ V : X.ProEt,
      HasProEtaleTorAmplitude.{u} V.left (Padic.coefficientExtensionRing l E 1)
        ((proEtaleRingDerivedPullback.{u} V.hom
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E 1))
          (proEtaleConstantRing V.left (Padic.coefficientExtensionRing l E 1))
          (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso.{u}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E 1)) V.hom)).obj
            ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K)) a b) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((@DerivedCategory.homologyFunctor (integralTowerModules.{u, u} l E X) _
        (@SheafOfModules.instAbelian X.ProEt inferInstance (ProEt.topology X)
          (completedIntegralCoefficientSheafUnrestricted l E X)
          (integralCoefficientAbSheafify.{u, u} X)
          (integralCoefficientAbLocallyBijective.{u, u} X))
        (integralTowerHasDerivedCategory.{u, u} l E X) j).obj K) := by
  sorry

end WeilConjectures
