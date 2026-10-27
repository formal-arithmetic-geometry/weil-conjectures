/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity

/-!
# Openness of the very-tame locus

Source: Illusie--Laszlo--Orgogozo, Exposé VI Corollary 3.6 and
Exposé VIII Lemma 5.3.2(i), printed pp. 74 and 123
(blueprint: lem-per-very-tame-locus-open).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The very-tame locus is invariant and open, and strict inert pullback preserves it.
Source: Illusie--Laszlo--Orgogozo, Exposé VI Corollary 3.6 and
Exposé VIII Lemma 5.3.2(i), printed pp. 74 and 123
(blueprint: lem-per-very-tame-locus-open).

Proof:
1. For a strict equivariant etale map inducing inertia isomorphisms, finite presentation
   on affine charts and lem-weil-pbc-finite-type-algebra-noetherian give local
   Noetherianity upstairs. Pulling back fs charts gives fs. By
   lem-trf-ind-etale-strict-local-invariance the strict local rings agree. Strictness
   identifies log stalks, units, characteristic monoids and nonunit ideals, equivariantly
   for the identified inertia groups. Thus stratum regularity, the dimension formula,
   inertia-order invertibility and both identity-action tests agree.
2. This compares all geometric lifts: for a prescribed source point, use the
   prescribed-source-point clause of lem-weil-pbc-etale-cover-geometric-point-lift over
   the open image of the map. Every geometric lift downstairs has a lift upstairs with
   the same algebraically closed field. Composition gives the converse implication.
3. At a point of T apply lem-per-pointwise-diagonal-kummer-neighbourhood, with model
   A = B tensor over Lambda[P] with Lambda[Q]. For its acting inertia subgroup L,
   n = card L is invertible on the model. The stabilizer K at any model point has order
   dividing n. Each chart monomial is an eigenvector with unit eigenvalue, so K fixes
   its characteristic class and therefore the whole characteristic monoid. No faithful
   character pairing is required.
4. Let E be the face of monomials nonzero at that geometric point and J the ideal of
   monomials outside E. Both are L-stable. For h in K and e in E, evaluation shows that
   the eigenvalue chi_h(e) has residue 1. By lem-sbc-strict-local-roots-of-unity a
   nonidentity nth root differs from 1 by a unit, so chi_h(e) is 1 in the strict local
   ring. In its stratum quotient C the nonunit ideal is the extension of J. Monomials
   outside E vanish, those inside E are fixed, and B is fixed, so h fixes the image of
   A/J in C. By lem-trf-closed-immersion-strict-localization-cartesian, C is the strict
   local ring of Spec(A/J). The h-action and identity have the same structural map and
   residue embedding, hence agree by lem-weil-pbc-strict-henselization-functoriality.
   This verifies the stratum test, including nilpotents.
5. Every point of the model is therefore very tame. Steps 1--2 transfer this property
   to its image, which contains the original point and is open by
   lem-weil-pbc-etale-morphism-open-map. These images prove openness. A group element
   bijects geometric lifts and conjugates inertia, preserving its order, the identified
   log stalks, characteristic monoids, nonunit ideals and both identity-action tests.
   This proves invariance. Steps 1--2 give the strict inert pullback assertion. Empty
   schemes and empty loci are covered by the empty union.
-/
theorem isOpen_veryTameLocus {H : Type v} [Group H] [Finite H]
    (Y : FineSaturatedLogScheme.{u}) (a : FSLogGroupAction H Y)
    [Y.scheme.IsSeparated] (hregular : Y.IsLogRegular) :
    IsOpen a.toEtaleLogGroupAction.veryTameLocus ∧
      (∀ (g : H) (y : Y.scheme),
        (a.baseAction g).hom y ∈ a.toEtaleLogGroupAction.veryTameLocus ↔
          y ∈ a.toEtaleLogGroupAction.veryTameLocus) ∧
      ∀ (Y' : Scheme.{u}) (M' : EtaleLogStructure Y')
        (a' : EtaleLogGroupAction H M') (v : EtaleLogMap M' Y.logStructure),
        a'.IsEquivariant a.toEtaleLogGroupAction v →
        v.IsStrictEtale →
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (t' : Spec (.of Ω) ⟶ Y') (g : H),
          t' ≫ (a'.baseAction g).hom = t' ↔
            (t' ≫ v.base) ≫ (a.baseAction g).hom = t' ≫ v.base) →
        ∃ (hln : IsLocallyNoetherian Y') (hfs : M'.IsFineSaturated),
          (FineSaturatedLogScheme.mk Y' hln M' hfs).IsLogRegular ∧
            a'.veryTameLocus = Set.preimage (fun x : Y' ↦ v.base x)
              a.toEtaleLogGroupAction.veryTameLocus := by
  sorry

end AlgebraicGeometry
