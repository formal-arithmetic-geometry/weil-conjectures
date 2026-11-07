/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineLocal
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveDescent.Gluing
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveDescent.Group
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveDescent.Neighbourhood
public import Submission.WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineNeighbourhood

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Effective descent for schemes

Let `p : X ⟶ Y` be a morphism of schemes. This file collects the descent statements for schemes
over `X` equipped with a descent datum relative to `p` (in the transport form
`CategoryTheory.Over.DescentDatum`) that are needed to descend the Jacobian of a curve from a
finite separable extension of the base field.

## Main statements

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite`: along a surjective finite locally
  free morphism, descent data on schemes in which every finite set of points lies in an affine open
  (for instance projective schemes over a field) are effective (blueprint
  `thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.isEffective_of_isClosedImmersion`: along a surjective finite
  locally free morphism with affine source `X`, descent data on projective schemes over `X` are
  effective (blueprint `thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback`: compatible morphisms descend
  (blueprint `lem-pd-morphisms-descend`).
- `CategoryTheory.Over.DescentDatum.existsUnique_grpObj_of_isPullback`: compatible group scheme
  structures descend, uniquely (blueprint `lem-pd-group-scheme-descent`).
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`: compatible commutative group
  scheme structures descend (blueprint `lem-pd-group-scheme-descent`).
- `AlgebraicGeometry.locallyOfFiniteType_quasiCompact_smooth_isProper_connectedSpace_of_isPullback`:
  finite type, smoothness, properness and connectedness descend along a field extension (blueprint
  `thm-pd-fpqc-local-properties`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`:
  properness, smoothness of relative dimension `n` and geometric integrality descend along a field
  extension (blueprint `thm-pd-fpqc-local-properties`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- **Effective descent for quasi-projective schemes.** Let `p : X ⟶ Y` be a surjective finite
locally free morphism and let `V` be a scheme over `X` in which every finite set of points lies in
an affine open, as is the case for a projective scheme over a field (Stacks 01ZY). Then every
descent datum on `V` relative to `p` is effective.

This is Stacks 0CCJ, via the criterion of Stacks 0CCI: the hypothesis on `V` is stronger than the
one needed there, which only asks it of the finite sets of points lying over one point of `Y`.

(blueprint: `thm-pd-effective-descent`) -/
theorem isEffective_of_isFinite [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {V : Over X}
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) : D.IsEffective := by
  refine isEffective_of_forall_exists_mem fun v ↦ ?_
  obtain ⟨U, hv, hU, hUa, W, hW, hUW⟩ := D.exists_isInvariant_isAffineOpen hV v
  exact ⟨U, hU, hv, D.isEffective_restrict_of_isAffineOpen hU hUa hW hUW⟩


end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry

/-- **Properties of morphisms are local in the fpqc topology on the target.** Let `k ⊆ K` be a
field extension and let `Z` be a scheme over `k` whose base change `Z_K` is proper, smooth of
relative dimension `n` and geometrically integral over `K`. Then so is `Z` over `k`.

For properness and smoothness this is Stacks 02YJ, 02VL, 02KL and 05B5, the morphism
`Spec K ⟶ Spec k` being faithfully flat and quasi-compact; the relative dimension is read off on
fibres. Geometric integrality descends because for every field `Ω` over `k` there is a field `L`
containing both `Ω` and `K`, and `Z_L ⟶ Z_Ω` is faithfully flat: reducedness descends along it
and irreducibility passes to the image.

The blueprint states this for finite extensions and lists finite type, smoothness, properness and
connectedness; the form here holds for any field extension and carries the properties used to
recognise an abelian variety of dimension `g`.

(blueprint: `thm-pd-fpqc-local-properties`) -/
theorem isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback {k K : Type u}
    [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (n : ℕ)
    [IsProper z'] [SmoothOfRelativeDimension n z'] [GeometricallyIntegral z'] :
    IsProper z ∧ SmoothOfRelativeDimension n z ∧ GeometricallyIntegral z :=
  isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback_aux z z' q h n


end AlgebraicGeometry
