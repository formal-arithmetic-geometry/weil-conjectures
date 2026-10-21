/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.ModuleObjects.LiftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula
import Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
import Sheaf.SixFunctors.OpenTensorNormalizationData
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Boundary vanishing for a proper refinement over a qcqs base

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md`, (2),
closed-complement calculation and its ambient localizing extension
(blueprint: lem-sfb-qcqs-proper-open-boundary-vanishing).

All three functors act on the ordinary unbounded derived categories of module objects
for the coefficient rings pulled back from the point. The closed immersion is specified
only by its underlying image; its source need not be the reduced closed complement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restriction to the boundary of a proper direct image of open extension by zero
vanishes on the ambient localizing closure of bounded constructible finite-Tor objects.

Source: blueprint main-20261015, sec-six-functors-basics,
`det-sf-comp-coherence-refinement.proof.md`, (2), closed-complement calculation
(blueprint: lem-sfb-qcqs-proper-open-boundary-vanishing).

Proof plan:
1. `lem-sfb-alpha-iso` identifies the coefficient-change map with an isomorphism.
   The module pullback of `sk-def-sfb-module-pushforward-pullback` has exact underlying
   abelian inverse image (`det-pe-topos-functoriality-inverse-image`), and exactness lifts
   by `det-prop-sfb-module-pullback-exact-lifted`. The exact functors act termwise by
   `lem-weil-pbc-exact-functor-derived-factorization`.
2. Form B' = Z' ×_Z B (`def-pc-fibre-product`). Its map a to Z' is a closed immersion
   and its map h_B to B is proper (`lem-weil-pbc-proper-fp-permanence`). Its underlying
   image is the inverse image of the image of i, as follows on affine ideal charts.
   The inverse-image hypothesis makes a complementary to j', including nonreduced B'.
3. J = D(j'_!) carries bounded constructible finite-Tor objects to such objects.
   Exactness and `lem-weil-pbc-exact-functor-complex-cohomology` preserve the bounds.
   For constructibility, on an affine open of Z' stratify the quasi-compact source open
   as in `sk-def-sfb-constructible`, then add its closed complement with zero model.
   The strata remain constructible by `def-weil-constructible-subset`; on a qcqs target
   a finite affine cover refines these to a global finite stratification. The open unit
   and mixed vanishing in `lem-sfb-condensed-support-derived-localization` identify the
   local models. `lem-sfb-condensed-support-projection-formula` preserves the Tor interval.
4. For each such generator, `lem-sfb-qcqs-proper-constructible-closed-base-change`
   identifies i* Rh* J K with R(h_B)* a* J K. Mixed restriction in
   `lem-sfb-condensed-support-derived-localization` makes a* J K zero. The derived
   adjunction of `sk-def-sfb-module-derived-pushpull` makes R(h_B)* preserve zero.
5. J and i* are triangulated by the exact derived factorization. Their sheaf adjunctions
   (`sk-def-sfb-module-lower-shriek`, `sk-def-sfb-module-derived-pushpull`) derive by
   `def-weil-exact-derived-adjunction`, so preserve ambient sums by
   `lem-weil-pbc-left-adjoint-preserves-colimits`. Minimality in
   `sk-def-localizing-closure` and step 3 put J of the source hull in the target hull.
   `lem-sfb-qcqs-proper-localizing-coproducts` then makes Rh* J preserve sums there.
   `lem-pc-right-derived-functor-triangulated` makes the composite triangulated.
6. The zero locus of this composite within the source hull is replete, closed under
   shifts, distinguished triangles, and ambient sums, including the empty sum.
   Step 4 includes every generator. Minimality of `sk-def-localizing-closure` proves
   vanishing for every object of the hull. No density or dimension assumption is used. -/
theorem qcqs_proper_open_boundary_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S Z Z' U B : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Z ⟶ S) (q' : Z' ⟶ S) [IsProper q] [IsProper q']
    (h : Z' ⟶ Z) [IsProper h] (hh : h ≫ q = q')
    (j : U ⟶ Z) (j' : U ⟶ Z')
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion j'] [QuasiCompact j']
    (hj : j' ≫ h = j) (hU : h ⁻¹' Set.range j = Set.range j')
    (i : B ⟶ Z) [IsClosedImmersion i] (hi : Set.range i = (Set.range j)ᶜ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (hK : localizingClosureProEtale Λ U K) :
    IsZero ((upperStar Λ i).mapDerivedCategory.obj
      ((moduleObjectDerivedPushforward Λ h).obj
        ((openImmersionLowerShriek Λ j').mapDerivedCategory.obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
