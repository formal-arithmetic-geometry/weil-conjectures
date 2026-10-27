/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ChowLemma
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Refining composites of standard ph families

Source: Stacks Project, Topologies, Tag 0DBF, lemma-refine-by-standard-ph, assertion (2)
(the proof calls it (3)) (blueprint: lem-trf-standard-ph-composite-refinement).

A finite affine open covering of a proper surjection, followed by such a covering over
its members, admits a refinement of the same form. The factorization equation is over
`T`, so every resulting map is also over the original base `S`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A composite of two standard ph families on an affine scheme has a standard refinement.

Source: Stacks Project, Topologies, Tag 0DBF, lemma-refine-by-standard-ph (2)
(blueprint: lem-trf-standard-ph-composite-refinement).

Proof plan, following the node:
1. If `T` is empty, use its identity and an empty affine open cover. Otherwise the
   first covering is nonempty, and a zero-length second cover forces its target empty.
2. Apply Chow's lemma (sk-thm-chow-projective) to each proper surjection over an affine
   `Uj`. Obtain a proper surjective projective domination and inverse-image open covers
   mapping to the original `Vji`. Use lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-qcqs-over-affine for the quasi-compactness hypotheses.
3. Take the scheme-theoretic closure of each domination in projective space over `U`.
   Its restriction to `Uj` is the original closed subscheme, by
   lemma-nagata-scheme-image-restrict-open and lemma-nagata-scheme-image-of-closed-immersion.
   The required quasi-compactness follows from lem-weil-pbc-qcqs-morphism-permanence
   and lem-weil-pbc-scheme-image-qc-kernel. The ambient projective space is proper
   and has the stated base change by lemma-nagata-projective-space-base-change-proper
   and lemma-nagata-projective-space-base-change-pullback.
4. Adjoin the reduced induced closed complement of `Uj` as a disjoint summand.
   By lem-weil-pbc-reduced-induced-closed-subscheme and
   lem-weil-pbc-scheme-coproduct-family this gives a proper surjection onto `U`
   whose inverse image of `Uj` is precisely the original domination.
5. Take the finite fibre product of these proper surjections over `U`, starting with
   `U` for the empty product. Properness and surjectivity persist by
   lem-weil-pbc-proper-fp-permanence and lem-weil-pbc-surjective-base-change.
   Compose with `p`; lem-weil-pbc-qcqs-over-affine gives quasi-compactness of `Z`.
6. Pull back the open covers of the dominations along the product projections.
   They cover `Z`, since every image point lies in some `Uj`. Refine these opens
   by affine opens (lem-pc-fppf-affine-open-cover), then select a finite subcover
   using def-weil-pbc-quasi-compact-scheme. Retain the chosen pair of indices and
   the restricted map to `Vji`; all constructions are over `T`, giving the equation.
7. All constructions stay in the fixed universe (def-weil-size-convention).
   Empty first-cover members require no second-cover index, and over nonempty `T`
   surjectivity forces the resulting cover to be nonempty. -/
theorem standard_ph_composite_refinement (S : Scheme.{u}) (T : Over S)
    [IsAffine T.left] (U : Scheme.{u}) (p : U ⟶ T.left) [IsProper p]
    (hp : Function.Surjective p) (m : ℕ) (Uj : Fin m → U.Opens)
    (hUaff : ∀ j, IsAffineOpen (Uj j)) (hUcover : (⨆ j, Uj j) = ⊤)
    (V : Fin m → Scheme.{u}) (q : ∀ j, V j ⟶ (Uj j).toScheme)
    (hqproper : ∀ j, IsProper (q j)) (hqsurj : ∀ j, Function.Surjective (q j))
    (n : Fin m → ℕ) (Vji : ∀ j, Fin (n j) → (V j).Opens)
    (hVaff : ∀ j i, IsAffineOpen (Vji j i)) (hVcover : ∀ j, (⨆ i, Vji j i) = ⊤) :
    ∃ (Z : Scheme.{u}) (r : Z ⟶ T.left), IsProper r ∧ Function.Surjective r ∧
      ∃ (N : ℕ) (Za : Fin N → Z.Opens),
        (∀ a, IsAffineOpen (Za a)) ∧ (⨆ a, Za a) = ⊤ ∧
        ∀ a, ∃ (j : Fin m) (i : Fin (n j)) (f : (Za a).toScheme ⟶ (Vji j i).toScheme),
          f ≫ (Vji j i).ι ≫ q j ≫ (Uj j).ι ≫ p = (Za a).ι ≫ r := by
  sorry

end AlgebraicGeometry.Scheme
