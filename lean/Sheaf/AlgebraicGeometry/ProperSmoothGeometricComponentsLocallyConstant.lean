/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure

/-!
# Geometric component counts in proper smooth families

Source: Stacks Project, `more-morphisms.tex`, Tag 0E0N,
`lemma-proper-flat-geom-red`, specialized to smooth morphisms
(blueprint: lem-weil-pbc-proper-flat-geometric-components-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- In a proper smooth family the geometric connected component count is finite and locally
constant, vanishes for empty fibres, and geometric connectedness persists near any point where
it holds. Source: Stacks Project, Tag 0E0N, `lemma-proper-flat-geom-red`
(blueprint: lem-weil-pbc-proper-flat-geometric-components-locally-constant).

Proof plan:
1. Smoothness gives flatness (lem-pc-smooth-flat) and geometrically reduced fibres
   (sbc-lem-smooth-geometrically-reduced). Properness survives base change
   (lem-pc-proper-base-change); the geometric fibre is the residue fibre extended to its
   algebraic closure (def-weil-geometric-fibre).
2. Apply thm-pc-semicontinuity-base-change, clauses (1) and (2), to the structure sheaf in
   degree zero. Its stalks are flat over the base by def-weil-flat-morphism. This gives finite
   fibre cohomology and upper semicontinuity, without assuming the base reduced.
3. A field extension is flat (lem-pc-field-extension-fpqc-cover). Flat cohomological base change
   (lem-pc-flat-base-change-cohom) identifies the extension of H⁰ with the geometric fibre's
   global sections. Properness gives quasi-compactness and quasi-separatedness, using
   def-weil-proper-morphism, def-weil-pbc-scheme-conventions and def-weil-closed-immersion.
   By lem-weil-pbc-proper-reduced-algclosed-global-sections-product these sections form a finite
   product of the algebraically closed field, indexed by the connected components. Comparing
   dimensions identifies the component count with the upper semicontinuous H⁰ dimension.
   Both are zero for an empty fibre.
4. lem-weil-pbc-flat-proper-component-count-lower-semicontinuous gives a neighbourhood on which
   the count is at least its value at the chosen point.
5. Upper semicontinuity gives a neighbourhood on which the count is at most that value.
   Intersect the neighbourhoods to obtain local constancy, also when the count is zero.
6. By lem-weil-geometrically-connected-algebraic-closure, geometric connectedness of a residue
   fibre is equivalent to connectedness of its algebraic-closure base change. Such a fibre has
   exactly one component. Local constancy and the reverse implication of the same lemma give
   the asserted neighbourhood of geometrically connected fibres. -/
theorem proper_smooth_geometric_components_locally_constant
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] :
    (∀ s : S, Finite (ConnectedComponents ↥(pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))) ∧
    IsLocallyConstant (fun s : S ↦ Nat.card (ConnectedComponents ↥(pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)))) ∧
    (∀ s : S, IsEmpty ↥(pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) →
      Nat.card (ConnectedComponents ↥(pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s))) = 0) ∧
    (∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s) →
      ∃ U : S.Opens, s ∈ U ∧
        ∀ t : S, t ∈ U → GeometricallyConnected (f.fiberToSpecResidueField t)) := by
  sorry

end AlgebraicGeometry
