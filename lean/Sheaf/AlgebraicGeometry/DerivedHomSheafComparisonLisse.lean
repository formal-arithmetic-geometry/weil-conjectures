/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses

/-!
# Comparison of local derived Hom with a bounded finite locally constant source

Source: Stacks Project, Cohomology on Sites, Tags 08JI, 08JA and 094G.
(blueprint: lem-weil-pbc-derived-hom-sheaf-comparison-lisse)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The canonical comparison of Hom sheaves is invertible for a bounded finite locally
constant source and an arbitrary bounded-below target. No Tor-amplitude condition is imposed.

Source: Stacks Project, Tags 08JI (bounded-above finite-free internal Hom), 08JA (derived
sections of internal Hom), and 094G (finite-ring derived local constancy).
(blueprint: lem-weil-pbc-derived-hom-sheaf-comparison-lisse)

Proof: The assertion is local on X for the etale topology. Finite-ring derived local constancy
provides an etale cover on which A is the constant complex of a bounded finite coefficient
complex. The finite coefficient ring is Noetherian, so its bounded finite cohomology gives a
bounded-above finite-free representative P. Choose a representative N of D vanishing below a.
The bounded-free RHom model has degree n equal to the finite sum of Hom(P^i,N^(i+n)) over
[a-n,b], where P vanishes above b. Each P^i is finite free, so these factors are finite powers
of N^(i+n). Exact inverse image and exact slice restriction preserve these powers, the
matrices defining the differential, and cohomology. The same model on the other site therefore
identifies comparison pullback of RHom with RHom of the pulled-back objects. On every slice,
sheafification of degree-zero derived sections of RHom is its degree-zero cohomology sheaf:
a K-injective representative computes those sections, and exact sheafification preserves the
kernel modulo image in degree zero. Under these identifications the displayed comparison is
H^0 of the model comparison. To check that it is this canonical map, represent a local actual
derived map by a chain map to a K-injective replacement. Both constructions take its class to
the class of its inverse image; the sheafification and comparison adjunctions determine the
map from these classes. Thus the comparison is invertible on the covering. The canonical
maps agree on overlaps by their same description on actual maps, and invertibility descends.
This argument also applies to zero complexes and the empty scheme. -/
theorem derivedHomSheafComparison_isIso_lisse
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hA : (DerivedCategory.TStructure.t
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).bounded A)
    (hAf : ∀ n : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj A))
    (hD : (DerivedCategory.TStructure.t
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).plus D) :
    IsIso (derivedHomSheafComparison X B A D) := by sorry

end AlgebraicGeometry.Scheme
