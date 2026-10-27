/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrata

/-! # Lower semicontinuity of fibre dimension for flat algebraic spaces

Source: Stacks Project, spaces-more-morphisms.tex, Tag 0D4P,
lemma-dimension-fibres-flat, with scheme target; more-morphisms.tex, Tag 0D4H
(blueprint: lem-sfb-flat-space-fibre-dimension-lower-semicontinuous).

The fibre dimension is the supremum over affine representable etale charts of the
actual presheaf fibre product with the canonical residue-field point.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension of the fibre is the supremum of the topological Krull dimensions
of all its affine representable etale charts. The empty fibre has value bottom.
Source: Stacks Project, Tag 0D4P, using the fibre convention of Tag 0D4N
(blueprint: lem-sfb-flat-space-fibre-dimension-lower-semicontinuous). -/
def affineEtaleFibreDimension {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) (t : T.left) : WithBot ℕ∞ :=
  ⨆ (U : Over S) (_ : IsAffine U.left)
    (a : yoneda.obj U ⟶ Limits.pullback f
      (yoneda.map (Over.homMk (U := Over.mk (T.left.fromSpecResidueField t ≫ T.hom))
        (V := T) (T.left.fromSpecResidueField t) rfl)))
    (_ : IsEtale a), topologicalKrullDim U.left

/-- Flat finite-presentation families over a scheme have finite or empty fibres, and
open strict dimension superlevel sets. For integer a >= -1 and finite natural-valued
dimension, the condition `(a + 1).toNat ≤ dimension` is precisely `dimension > a`;
for a = -1 it includes every nonempty fibre and excludes bottom.
Quasi-compactness and quasi-separatedness use `MapIsQuasiCompact` for the map
and its canonical relative diagonal, respectively, as in the recorded family definitions.
Source: Stacks Project, Tag 0D4P, lemma-dimension-fibres-flat, scheme-target case;
Tag 0D4H, lemma-dimension-fibres-flat
(blueprint: lem-sfb-flat-space-fibre-dimension-lower-semicontinuous).

Proof:
1. Cover the target by affine opens. Quasi-compactness and
   lem-trf-space-qc-finite-affine-atlas-refinement supply an affine surjective etale
   atlas U of each restricted source. Chartwise flatness and local finite presentation
   give these properties for U -> V. By lem-trf-space-fibre-products-etale-covers,
   its residue-field fibres are surjective etale atlases of the original fibres.
2. Apply lem-sfb-space-etale-atlas-topological-dimension using quasi-separatedness.
   The affine scheme fibre U_t is among the defining charts. For any other affine
   chart W, use the atlas W disjoint union U_t and open-subspace dimension monotonicity
   to bound dim W by dim U_t. Thus the defining supremum equals dim U_t, also if empty.
3. The affine ring map is finitely presented by
   lem-weil-pbc-lfp-affine-opens-finite-presentation. Its finitely many generators
   persist under base change. The affine morphism is quasi-compact, so
   lem-fin-finite-type-fibre-dimension-bound gives finite dimension of every fibre.
4. For dimension n > a, use lem-weil-pbc-dimension-supremum-local-dimensions to attain
   n, lem-trf-locally-algebraic-dimension-components to find a component of dimension n,
   and lem-weil-pbc-scheme-sober to choose its generic point, of local dimension n.
5. By lem-sbc-flat-fibre-dimension-strata that point belongs to the constant local
   fibre-dimension open H_n. By lem-weil-pbc-flat-lfp-open its image is an open
   neighbourhood in the target. Every fibre there has dimension at least n, by the
   supremum-of-local-dimensions formula and step 2.
6. These neighbourhoods show openness on every affine target open, hence globally.
   At a = -1 this is the nonempty-fibre locus. Empty targets are vacuous; the same
   affine cover proves the pointwise value-range assertion. -/
theorem affineEtaleFibreDimension_finite_isOpen_of_flat
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hflat : MapToSchemeIsLocally (@Flat) X T f)
    (hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f)
    (hqc : MapIsQuasiCompact f)
    (hqs : MapIsQuasiCompact (pullback.diagonal f)) :
    (∀ t : T.left, affineEtaleFibreDimension X T f t = ⊥ ∨
      ∃ n : ℕ, affineEtaleFibreDimension X T f t = (n : WithBot ℕ∞)) ∧
    (∀ a : ℤ, -1 ≤ a →
      IsOpen {t : T.left |
        ((a + 1).toNat : WithBot ℕ∞) ≤ affineEtaleFibreDimension X T f t}) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
