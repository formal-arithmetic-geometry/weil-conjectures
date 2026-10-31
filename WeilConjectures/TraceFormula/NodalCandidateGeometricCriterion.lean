/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FirstFittingSingularSubscheme
public import WeilConjectures.AlgebraicGeometry.UnramifiedLocusBaseChange
public import WeilConjectures.TraceFormula.SyntomicLocusBaseChange
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Geometric points of the syntomic and unramified singular locus

Source: Stacks Project, curves.tex, Tag 0DSC, lemma-locus-where-nodal;
Divisors Tag 0C3I and Curves Tags 0C4D and 0C59.
(blueprint: lem-trf-nodal-candidate-geometric-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The complement of the image of the bad part of the first-Fitting singular
subscheme has exactly the smooth and ordinary nodal points on every geometric fibre.
This assertion is pointwise and constructs no open or maximal subscheme.

Source: Stacks Project, curves.tex, Tag 0DSC, lemma-locus-where-nodal,
with Divisors Tag 0C3I and Curves Tags 0C4D and 0C59.
(blueprint: lem-trf-nodal-candidate-geometric-criterion).

Proof: Embed an algebraic closure of the residue field of the image of the
geometric point into its algebraically closed coefficient field. Associativity
of pullbacks and preservation of pure relative dimension under field extension
make its fibre pure of dimension one; an empty fibre has no points to test.
On affine charts the relative differential module base changes to the tensor
of the old module, and the first Fitting ideal extends by the kernel-minor
base-change theorem. These identifications localize and identify the singular
closed subscheme after base change. The same theorem and the smooth-locus
criterion identify its complement with the smooth locus. Both the fibrewise
complete-intersection locus and the unramified locus of the singular subscheme
commute with base change. At a singular point in their intersection, the
unramified fibre stalk is its finite separable residue field. The corresponding
point of the curve is closed. The pointwise LCI criterion supplies an affine
LCI neighbourhood. Apply the nodal-point criterion using the already
algebraically closed coefficient field as its own algebraic closure; the
identity-base-change and stalk isomorphisms give the required nodal model.
Conversely, a node is closed by hypothesis; its nodal
completion gives an LCI neighbourhood and the maximal first-Fitting stalk
ideal by that criterion. The pointwise LCI and unramified criteria put it in
both loci. Closed immersions are injective on points, so a point lies outside
the image of the bad singular part exactly when every singular point over it
has these two properties. This proves the asserted equivalence. -/
theorem nodalCandidate_geometric_criterion
    (Y T : Scheme.{u}) (p : Y ⟶ T) [Flat p]
    [LocallyOfFinitePresentation p]
    (hgeom : ∀ (t : T) (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω]
      [IsAlgClosure (T.residueField t) Ω],
      Nonempty (pullback (C := Scheme.{u}) p
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
          T.fromSpecResidueField t)) →
      (pullback p (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)) ≫
        T.fromSpecResidueField t)).IsPureDimension 1)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ T)
    (x : pullback (C := Scheme.{u}) p g) :
    ((pullback.fst p g x) ∉
      (Scheme.firstFittingSingularSubscheme p) ''
        (((Scheme.firstFittingSingularSubscheme p) ⁻¹' p.fiberCompleteIntersectionLocus ∩
          unramifiedLocus (Scheme.firstFittingSingularSubscheme p ≫ p))ᶜ)) ↔
      (x ∈ (pullback.snd p g).smoothLocus ∨
        (x ∈ closedPoints (pullback (C := Scheme.{u}) p g) ∧ Nonempty
          (AdicCompletion
            (IsLocalRing.maximalIdeal ((pullback p g).presheaf.stalk x))
            ((pullback p g).presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))) := by
  sorry

end AlgebraicGeometry
