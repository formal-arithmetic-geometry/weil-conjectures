/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyConstant.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # Fibre dimension in a proper flat finitely presented family of spaces

Source: Stacks Project, spaces-more-morphisms.tex, Tags 0D4R, 0D4N and the
fibre-dimension convention (blueprint: lem-sfb-proper-flat-space-fibre-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension of the actual residue-field fibre is the supremum of the topological
Krull dimensions of all its affine representable étale scheme charts.
Source: Stacks Project, spaces-more-morphisms.tex, lemma-dimension-fibre and Tag 0D4N
(blueprint: lem-sfb-proper-flat-space-fibre-dimension). -/
noncomputable def fibreDimension {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace T) (t : T.left) : WithBot ℕ∞ :=
  ⨆ (U : Over S) (_ : IsAffine U.left)
    (a : yoneda.obj U ⟶ Limits.pullback f.hom.hom
      (yoneda.map (Over.homMk (T.left.fromSpecResidueField t) rfl :
        Over.mk (T.left.fromSpecResidueField t ≫ T.hom) ⟶ T)))
    (_ : IsEtale a), topologicalKrullDim U.left

/-- Proper flat finitely presented algebraic-space families have locally constant fibre dimension,
and fibre dimension is preserved by arbitrary base change.
Source: Stacks Project, spaces-more-morphisms.tex, Tags 0D4R, 0D4N and the fibre-dimension
convention (blueprint: lem-sfb-proper-flat-space-fibre-dimension).

Proof:
1. Apply lem-sfb-space-flat-proper-fp-locality at every field-valued base change.
   The resulting space is separated and finite type. Choose an affine coproduct atlas
   using lem-a1-space-affine-etale-cover and lem-weil-pbc-scheme-coproduct-family.
   Its summand inclusions are étale by lem-weil-pbc-open-immersion-etale and
   lem-trf-space-chartwise-etale-permanence. Apply
   lem-sfb-space-etale-atlas-topological-dimension: its dimension is the supremum of
   the dimensions of the clopen summands, directly from def-kun-topological-krull-dimension.
   For any further affine étale chart V, adjoining V to the atlas gives another atlas
   (étaleness on the two clopen summands is def-weil-etale-morphism). The same atlas
   theorem and lem-weil-pbc-open-subspace-dimension-monotone bound dim V by that dimension.
   Thus the chart supremum equals the topological dimension, also for empty fibres.
2. Apply lem-sfb-flat-space-fibre-dimension-lower-semicontinuous and
   lem-sfb-proper-space-fibre-dimension-upper-semicontinuous. These give finiteness and,
   at a fibre of dimension d, the open neighbourhood {n > d-1} ∩ {n ≤ d} on which n=d.
   At an empty fibre use {n ≤ -1}. Every level set is open; its complement is the union
   of the other open level sets, so it is closed too.
3. For h:T'→T and t' in T', def-weil-residue-field supplies κ(h(t'))→κ(t').
   The universal property in lem-trf-space-fibre-products-etale-covers identifies the
   new fibre with the field extension of the old one: both represent pairs of maps to X
   and Spec κ(t') with equal composites to T. Apply
   lem-sfb-space-field-extension-dimension; the separated finite-type hypotheses follow
   from lem-sfb-space-flat-proper-fp-locality. Step 1 identifies both dimensions with
   the chart supremum. This gives equality of the functions, including empty fibres.
4. Taking level sets in this pointwise equality gives their stated inverse-image
   equality. This is the equality of clopen loci with induced open subspaces.
   Taking T'=Spec K includes arbitrary extensions of residue fields.
-/
theorem proper_flat_fp_fibreDimension_isLocallyConstant_and_baseChange
    {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace T)
    (hflat : MapIsFlat f) (hproper : MapIsProper f)
    (hfp : MapIsLocallyOfFinitePresentation f ∧
      MapIsQuasiCompact f.hom.hom ∧ MapIsQuasiCompact (pullback.diagonal f.hom.hom)) :
    (∀ t : T.left, fibreDimension f t = ⊥ ∨
      ∃ d : ℕ, fibreDimension f t = (d : WithBot ℕ∞)) ∧
    IsLocallyConstant (fibreDimension f) ∧
    (∀ d : ℕ, IsClopen {t : T.left | fibreDimension f t = (d : WithBot ℕ∞)}) ∧
    (∀ (T' : Over S) (h : T' ⟶ T),
      fibreDimension (enlargedFibreProductFst
        (ObjectProperty.homMk ⟨yoneda.map h⟩ : schemeSpace T' ⟶ schemeSpace T) f) =
          fibreDimension f ∘ h.left) ∧
    (∀ (T' : Over S) (h : T' ⟶ T) (d : ℕ),
      {t' : T'.left | fibreDimension (enlargedFibreProductFst
        (ObjectProperty.homMk ⟨yoneda.map h⟩ : schemeSpace T' ⟶ schemeSpace T) f) t' =
          (d : WithBot ℕ∞)} = h.left ⁻¹' {t : T.left |
            fibreDimension f t = (d : WithBot ℕ∞)}) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
