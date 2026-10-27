/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.SpaceUniversalRelativePurity
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.ProconstructibleClosureSpecialization

/-! # Constructibility of containment of fibre associated points

Source: Stacks Project, Divisors on Spaces, Tag 0CVV,
lemma-relative-assassin-constructible; Morphisms, Tag 05LW,
lemma-constructible-containing-open
(blueprint: lem-sfb-space-assassin-containment-constructible).

The containment locus uses the fibre of the existing relative assassin over each
scheme point. Tag 0CVV explicitly identifies this fibre with the associated points
of the fibre module, so this avoids a second construction of fibrewise association.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The points of the scheme base where all fibre associated points belong to `W`.
The relative assassin is already computed from the specified tensor pullback on
scheme charts. Its fibre over `y` is exactly the image of the fibre associated points.
Source: Stacks, Tag 0CVV, statement and first parenthesis of its proof
(blueprint: lem-sfb-space-assassin-containment-constructible). -/
def fibreAssassinContainmentLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : Over S) (f : X ⟶ schemeSpace Y) (M : X.Modules)
    (W : Set (Point X.obj.obj)) : Set Y.left :=
  {y | ∀ ξ : Point X.obj.obj, ξ ∈ relativeAssassin Y f M →
    mapPoint f.hom.hom ξ = schemePointMap (𝟙 (yoneda.obj Y)) y → ξ ∈ W}

/-- For a finitely presented space over a scheme and a finitely presented quasi-coherent
module, containment of the fibre associated points in a relatively quasi-compact open
subspace is locally constructible. If all generalizations of `y` satisfy containment,
an open neighbourhood of `y` satisfies it. Local constructibility is written with the
affine neighbourhoods stipulated in the node, and generalization as closure of a singleton.
Source: Stacks, Tags 0CVV and 05LW
(blueprint: lem-sfb-space-assassin-containment-constructible).

Proof:
1. Restrict to an arbitrary affine open B of Y. Finite presentation and quasi-compactness
   of W over B survive base change, using lem-sfb-space-flat-proper-fp-locality and
   lem-sfb-space-quasicompact-affine-tests. B is qcqs by
   lem-weil-pbc-affine-scheme-qcqs, so X_B is qcqs by lem-sfb-space-fp-qcqs-source.
2. Choose an affine surjective etale atlas T of X_B by lem-sfb-qc-space-affine-etale-atlas.
   By lem-sfb-space-qcqs-permanence its map to X_B is qcqs. A scheme map between two
   etale charts is etale by lem-trf-space-representable-etale-scheme-tests, so the atlas
   map is locally finitely presented by def-weil-etale-morphism. Composition is finitely
   presented by lem-sfb-space-separated-fp-composition. The inverse image H of W is
   quasi-compact over B, using lem-sfb-space-quasicompact-fppf-local and the affine tests.
3. Tensor pullback preserves finite presentations and quasi-coherence by
   def-trf-space-etale-module-functors and def-trf-space-quasi-coherent-module.
   Apply lem-sfb-space-qcoh-affine-chart-calculus to the pulled-back module on T.
   The equivalence lem-trf-scheme-zariski-etale-quasi-coherent-equivalence gives its
   finitely presented Zariski module F and identifies their fibre stalks, hence their
   associated points by def-trf-relative-assassin.
4. By lem-sfb-space-fibre-assassin-etale-atlas, the image of the associated points of
   each fibre of T is the associated-point set downstairs. Since H is the inverse image
   of W, containment downstairs is equivalent to containment in H upstairs.
5. Apply lem-sfb-scheme-assassin-open-constructible to T over B, F and H. This proves
   constructibility on every affine B and hence the required affine-local assertion.
6. For y with every generalization in the locus, choose an affine B containing y.
   Its constructible complement C cannot have y in its closure: B is spectral by
   lem-weil-pbc-qcqs-scheme-spectral and lem-weil-pbc-affine-scheme-qcqs, and
   lem-weil-pbc-spectral-proconstructible-closure-specialization, applied to the singleton
   family C, would produce a point of C generalizing y. Continuity of B into Y contradicts
   the assumption. Constructible complements use def-weil-constructible-subset.
7. B minus the closure of C is open in Y, contains y and lies in the locus. -/
theorem fibreAssassinContainment_locallyConstructible
    {X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (Y : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (f : X ⟶ schemeSpace Y)
    (_hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : X.QCoh) (_hM : SheafOfModules.IsFinitePresentation M.obj)
    (W : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (j : W ⟶ X)
    (_hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (_hW : MapIsQuasiCompact (j.hom.hom ≫ f.hom.hom)) :
    (∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧ IsAffineOpen V ∧
      Topology.IsConstructible
        ((Subtype.val : V → Y.left) ⁻¹'
          fibreAssassinContainmentLocus Y f M.obj (pointImage j.hom.hom))) ∧
    (∀ y : Y.left,
      (∀ t : Y.left, y ∈ closure ({t} : Set Y.left) →
        t ∈ fibreAssassinContainmentLocus Y f M.obj (pointImage j.hom.hom)) →
      ∃ V : Y.left.Opens, y ∈ V ∧
        (V : Set Y.left) ⊆
          fibreAssassinContainmentLocus Y f M.obj (pointImage j.hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
