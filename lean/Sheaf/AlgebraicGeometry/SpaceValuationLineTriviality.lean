/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.SpaceProperFieldGlobalFunctions
import Sheaf.AlgebraicGeometry.PerfectJumpLoci
import Sheaf.AlgebraicGeometry.SpaceDualEffectiveLineTriviality
import WeilConjectures.AlgebraicGeometry.PerfectAffineModulePreimage
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.RingTheory.BoundedPseudoCoherentResidueModel
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections

/-! # Generic triviality of line modules over valuation bases

Source: Stacks Project, Moduli Stacks, Tag 0DNJ,
lemma-pic-functor-uniqueness-part, from “Denote f” to the final trivialization
(blueprint: lem-sfb-space-valuation-line-triviality).

All fibre products are the existing sheaf fibre products, with their first projections.
Restriction of a line module is the canonical tensor pullback on small etale module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A generically trivial line module on a proper flat finitely presented algebraic space
with integral geometric fibres over any valuation ring is trivial. Finite presentation is
local finite presentation together with quasi-compactness and quasi-separatedness. Geometric
integrality is reducedness and nonempty irreducibility of each algebraically closed fibre.

Source: Stacks Project, Moduli Stacks, Tag 0DNJ,
lemma-pic-functor-uniqueness-part, valuation-ring line-module argument
(blueprint: lem-sfb-space-valuation-line-triviality).

Proof:
1. Apply lem-sfb-proper-flat-space-derived-base-change to L and its internal dual.
   On a trivializing etale chart they are the structure module, hence quasi-coherent,
   finitely presented and flat over R. Their canonical derived direct images E and E-dual
   on Spec R are perfect and commute with ordinary and geometric field base changes.
2. The geometric generic fibre has only scalar functions by
   lem-sfb-space-proper-field-global-functions, so generic triviality makes both degree-zero
   fibre dimensions one. Upper semicontinuity and field-extension invariance from
   lem-sc-perfect-jump-loci give nonzero sections of both lines on the geometric closed
   fibre. Apply lem-sfb-space-dual-effective-line-triviality there. The line is trivial
   on that fibre, whose constants theorem then gives degree-zero dimension one.
3. Use lem-pc-perfect-affine-module-preimage and lem-pc-affine-qcoh-derived-equivalence
   to pass E to a pseudo-coherent ring complex with finite Tor amplitude. Its closed
   derived fibre has no negative cohomology. By lem-sfb-bounded-pseudocoherent-residue-model
   at the maximal ideal, it has a bounded finite-free model P with no negative terms
   and P^0 = R. The localization element is outside the maximal ideal, hence a unit.
   By lem-pc-flat-complex-derived-pullback, ordinary tensor computes its derived fibres.
4. The differential R -> P^1 vanishes after tensoring with K, since its kernel has
   dimension one. Injectivity of R -> K makes each matrix entry zero over R. Thus 1
   gives a class in H^0(P) that also generates the closed fibre. The affine equivalence
   and lem-sfb-space-affine-base-higher-image-sections in degree zero give a section s of L.
   Canonical derived base change identifies its fibre class with that of 1. On the
   geometric closed fibre it is a nonzero scalar in the now trivial line, so it generates.
5. The non-generator locus Z of s is closed: on each etale trivialization it is the
   zero locus of its coefficient, and transition units preserve this locus. It misses
   the closed fibre, as vanishing can be tested after field extension. Properness makes
   f(Z) closed in Spec R. Every nonempty closed subset of the spectrum of a local ring
   contains its closed point, so Z is empty. The local inverse coefficients glue to the
   inverse of s : O_X -> L. No rank, Noetherian, section or rigidification assumption is used. -/
theorem lineModule_trivial_of_generic_trivial_over_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (X : AlgebraicSpace (Spec (CommRingCat.of R)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (hproper : MapIsProper f) (hflat : MapIsFlat f)
    (hlfp : MapIsLocallyOfFinitePresentation f)
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : R →+* Ω),
      (enlargedFibreProduct f
        (ObjectProperty.homMk
          ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom a)) :
              Over.mk (Spec.map (CommRingCat.ofHom a)) ⟶
                Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
          schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom a))) ⟶
            schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of R)))))).IsReduced ∧
      IrreducibleSpace (Point (enlargedFibreProduct f
        (ObjectProperty.homMk
          ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom a)) :
              Over.mk (Spec.map (CommRingCat.ofHom a)) ⟶
                Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
          schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom a))) ⟶
            schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of R)))))).obj.obj))
    (L : X.Modules) (hL : X.IsLineModule L)
    (hgeneric : Nonempty
      ((moduleTensorPullback (enlargedFibreProductFst f
        (ObjectProperty.homMk
          ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
                Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
          schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⟶
            schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of R))))))).obj L ≅
        SheafOfModules.unit (enlargedFibreProduct f
          (ObjectProperty.homMk
            ((Scheme.fppfTopology.over (Spec (CommRingCat.of R))).yoneda.map
              (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) :
                Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
                  Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
            schemeSpace (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⟶
              schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of R)))))).structureSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit X.structureSheaf) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
