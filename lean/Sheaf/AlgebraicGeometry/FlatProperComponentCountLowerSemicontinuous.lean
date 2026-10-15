/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Algebra.Defs
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.Topology.Connected.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange
import Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting
import Sheaf.AlgebraicGeometry.SteinFiniteFibresResidueFields

/-!
# Lower semicontinuity of geometric connected component counts

Source: Stacks Project, More on Morphisms, Tag 0BUI,
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`
(blueprint: lem-weil-pbc-flat-proper-component-count-lower-semicontinuous).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, More on Morphisms, Tag 0BUI.
(blueprint: lem-weil-pbc-flat-proper-component-count-lower-semicontinuous)

The geometric fibres of a proper flat finitely presented morphism have finitely many
connected components. Their count is zero for an empty fibre and is lower semicontinuous,
expressed by the neighbourhood inequality. The function `n` is specified by `Nat.card` of
`ConnectedComponents`, the quotient by equality of maximal connected subsets.
Properness already implies quasi-compactness and quasi-separatedness, so finite
presentation is expressed by the remaining locally-of-finite-presentation condition.

Proof:
1. Restrict to an affine neighbourhood of a chosen point. Proper base change and flatness
   preserve the hypotheses. Apply affine Stein factorization
   (`lem-weil-pbc-stein-factorization-affine`) and its finite-fibre/residue-field lemma
   (`lem-weil-pbc-stein-finite-fibres-residue-fields`).
2. Apply `lem-weil-pbc-integral-fibre-etale-splitting`: after an affine etale neighbourhood
   the integral intermediate scheme splits into finitely many clopen pieces, each having
   one point over the chosen point, with purely inseparable residue extension. Pull these
   pieces back to a finite clopen partition of the source.
3. By `lem-weil-pbc-geometric-component-count-base-change` counts are unchanged at points
   of this neighbourhood. Flat base change and finite-presentation permanence give flat,
   locally finitely presented restrictions to each piece.
4. A purely inseparable residue extension gives a radicial fibre. Over an algebraic closure
   it has exactly one point: at most one by universal injectivity, and at least one by the
   unique-root embedding of a purely inseparable extension into that closure. Geometric
   connectedness of the Stein fibres makes each source piece nonempty and connected there.
5. These clopen connected nonempty pieces are exactly the connected components. Their
   finite number is the count at the chosen point. This works at every point, including
   the empty partition, whose count is zero.
6. By `lem-weil-pbc-flat-lfp-open`, each source piece has open image containing the chosen
   point. Intersect these finitely many images. Every geometric fibre over the intersection
   meets each piece: extension to the algebraic closure is faithfully flat and surjective
   on spectra (`lem-weil-pbc-field-extension-base-change-faithfully-flat` and
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`). Thus its count is at least the
   number of pieces. For zero pieces the inequality holds on the whole base.
7. The etale map is open (`lem-weil-pbc-etale-morphism-open-map`), so the image of this
   intersection is the desired open neighbourhood on the original base. Base-change
   invariance transfers the inequality. These neighbourhoods also make every strict
   superlevel set open, the equivalent lower-semicontinuity formulation.
-/
theorem Scheme.Hom.geometricComponentCount_lowerSemicontinuous
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    ∃ n : S → ℕ,
      (∀ s : S,
        Finite (ConnectedComponents (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u})) ∧
        n s = Nat.card (ConnectedComponents (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
            (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}))) ∧
      (∀ s : S, IsEmpty (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
          (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s) : Scheme.{u}) →
        n s = 0) ∧
      ∀ s : S, ∃ V : S.Opens, s ∈ V ∧ ∀ t : S, t ∈ V → n s ≤ n t := by
  sorry

end AlgebraicGeometry
