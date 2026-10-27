/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.RingTheory.KoszulRegularSequence

import WeilConjectures.RingTheory.KoszulBaseChangeIso
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.QuasiRegularNoetherianLocal
import Sheaf.RingTheory.FlatQuotientFiberRegularSequence
import Sheaf.RingTheory.RelativeRegularEquationsBaseChange
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Universal Koszul regularity of relative H₁-regular immersions

Source: Stacks Project, Divisors, Tag 063V(2), with the relative H₁-regular
immersion definition immediately preceding Tag 063U
(blueprint: lem-sfb-relative-h1-immersion-universal-koszul).

The local equations use the kernel of the actual map on affine sections.
The base-changed arrow is the canonical map between the two parameter fibre products.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A relative H₁-regular immersion with locally finitely presented ambient morphism
is Koszul-regular after every parameter base change.
Source: Stacks Project, Divisors, Tag 063V(2), retaining its Koszul-regular consequence
(blueprint: lem-sfb-relative-h1-immersion-universal-koszul).

Proof:
1. Around a source point choose affine base and ambient charts with finitely presented
   ambient algebra B/A and finite H₁-regular equations f for I. Closed immersion affine
   charts identify the quotient with B/I, flat over A by
   lem-weil-pbc-flat-morphism-affine-criterion. Principal refinements preserve finite
   presentation, generation and H₁-vanishing by lem-sc-koszul-base-change-iso and
   lem-weil-pbc-localization-module-exact.
2. Apply lem-sfb-h1-flat-quotient-ambient-flat-neighbourhood and shrink the chart so that
   B/A is flat. The quotient stays flat by
   lem-pc-affine-flat-module-localization-preserves-flatness; localization preserves
   H₁-vanishing by the same Koszul comparison and exactness.
3. Apply lem-sfb-koszul-h1-flat-quotient-base-change-surjective to the residue field at
   the base point. Its source is zero, so the fibre equations are H₁-regular. The fibre
   is finitely presented over a field, hence Noetherian by lem-wf-affine-noetherian-components.
   The fibre prime is obtained by localization and reduction, as in
   def-weil-pbc-localization-at-prime.
4. Localize the fibre at that prime. It is Noetherian by
   lem-weil-pbc-localization-noetherian. The localized equations are H₁-regular by exact
   localization, hence quasi-regular by lem-per-h1-koszul-quasi-regular. They lie in the
   maximal ideal, so lem-pur-quasi-regular-noetherian-local makes them regular.
5. Apply lem-pur-flat-quotient-fiber-regular-sequence to obtain a principal neighbourhood
   with finite regular generators a for I. Its ambient algebra and its quotient remain
   A-flat by lem-pc-affine-flat-module-localization-preserves-flatness, and its ambient
   algebra remains finitely presented by the presentation of a principal localization.
6. For any A-algebra A', lem-pur-relative-regular-equations-base-change makes a tensor 1
   regular at every prime containing its ideal. The positive Koszul homology vanishes
   there by lem-weil-pbc-regular-sequence-koszul-regular, without assuming A' flat.
7. At other primes one equation is a unit. Wedge with its basis vector divided by that
   unit contracts the Koszul complex of def-weil-pbc-koszul-complex. All positive homology
   therefore vanishes at every prime, using lem-sc-koszul-base-change-iso and exact
   localization. A nonzero module element survives at a maximal ideal containing its
   annihilator, so the homology modules themselves vanish.
8. Cover the parameter change by affine charts. The tensor-product charts are open by
   lem-weil-pbc-open-fibre-product and are the required fibre products by
   lem-weil-pbc-fibre-product-affine-spectra. Their source is cut out by the tensor
   equations by lem-weil-pbc-tensor-quotient-base-change. Step 7 proves the conclusion
   at every source point. This includes the identity change; empty source charts are
   vacuous, and an empty sequence has Koszul complex concentrated in degree zero. -/
theorem relativeH1Immersion_universally_koszulRegular
    {Z P S : Scheme.{u}} (p : P ⟶ S) (i : Z ⟶ P)
    [LocallyOfFinitePresentation p] [IsImmersion i] [Flat (i ≫ p)]
    (hH1 : ∀ z : Z, ∃ U : P.affineOpens, i z ∈ U.1 ∧
      IsClosedImmersion (i ∣_ U.1) ∧
      ∃ (r : ℕ) (f : Fin r → Γ(P, U.1)),
        Ideal.span (Set.range f) = RingHom.ker (i.app U.1).hom ∧
          RingTheory.Sequence.IsH1Regular f)
    (S' : Scheme.{u}) (g : S' ⟶ S) :
    ∀ z' : (pullback (i ≫ p) g : Scheme.{u}), ∃ U : (pullback p g).affineOpens,
      (pullback.map (i ≫ p) g p g i (𝟙 S') (𝟙 S)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) z' ∈ U.1 ∧
      IsClosedImmersion
        (pullback.map (i ≫ p) g p g i (𝟙 S') (𝟙 S)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ∣_ U.1) ∧
      ∃ (r : ℕ) (f : Fin r → Γ(pullback p g, U.1)),
        Ideal.span (Set.range f) = RingHom.ker
          ((pullback.map (i ≫ p) g p g i (𝟙 S') (𝟙 S)
            (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm)).app U.1).hom ∧
          RingTheory.Sequence.IsKoszulRegular f := by
  sorry

end AlgebraicGeometry
