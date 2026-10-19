/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Bad-locus contradiction for affine limit fibre dimensions

This is the bad-locus and Noetherian-fibre stabilization part of the affine limit dimension
argument. It is split from the final existence theorem so that the top-level implication remains
fully checked while this long construction can be proved independently.
Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`.
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound-core).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If every finite stage has a fibre of dimension strictly greater than `d`, then the limiting
fibre cannot have dimension at most `d`, under the finite type and closed-comparison hypotheses.
This is the bad-locus contradiction in Tag 05M5: the bad local-dimension loci are open complements,
their reduced closed subschemes have a nonempty affine inverse limit, and Noetherian stabilization
of a fixed limiting fibre produces a point contradicting the assumed bound.
Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`, affine specialization.
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound-core).
-/
theorem fibre_dimension_contradiction_of_all_stages_bad
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A C : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (hfinite : ∀ i : I, (φ.app i).hom.FiniteType)
    (hsurj : ∀ (i j : I) (hij : i ≤ j),
      Function.Surjective
        (pushout.desc (φ.app j) (C.map (homOfLE hij))
          (φ.naturality (homOfLE hij))).hom)
    (d : ℕ)
    (hbound : ∀ (p : Ideal ↥(colimit A)) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map (colimMap φ))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(colimit A) p.ResidueField))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞))
    (hbad : ∀ i : I, ∃ p : PrimeSpectrum (A.obj i),
      (d : WithBot ℕ∞) <
        topologicalKrullDim
          ↥(pullback (Spec.map (φ.app i))
            (Spec.map (CommRingCat.ofHom
              (algebraMap (A.obj i) p.asIdeal.ResidueField))) : Scheme.{u})) :
    False := by
  sorry

end AlgebraicGeometry
