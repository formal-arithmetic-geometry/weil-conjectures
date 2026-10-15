/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.AlgebraicGeometry.AffineChartBaseChangeIso
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.FieldTheory.SeparableExtension
import Sheaf.RingTheory.RegularLocalSeparableResidueSmooth
import Sheaf.RingTheory.SmoothAtPrimeFieldExtensionDescent

/-!
# Geometric regularity and smoothness over a field

Source: Stacks Project, Varieties, Tags 038X (lemma-geometrically-regular-smooth)
and 038T (definition-geometrically-regular).
(blueprint: lem-weil-pbc-geometric-regularity-smooth-field-criterion)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism locally of finite type over a field is smooth precisely when every
finitely generated field base change has regular local rings at all points.
Finite generation is as a field, expressed by `IntermediateField.FG` for the top field.
Source: Stacks Project, Varieties, Tags 038X and 038T.
(blueprint: lem-weil-pbc-geometric-regularity-smooth-field-criterion)

Proof following the node:
1. If `f` is smooth, take a smooth affine chart around the image of a point after
   field extension. Use `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, identify its
   base change by `lem-weil-pbc-affine-chart-base-change-iso`, and apply
   `lem-weil-pbc-smooth-ring-map-base-change-composition`. Its localizations are regular
   by `lem-weil-pbc-smooth-over-field-regular-local`; identify the stalk using
   `lem-weil-pbc-affine-open-stalk-localization`.
2. Conversely, choose a finite type affine chart `Spec A` around any point, with prime `p`.
   Its residue field `K` is finitely generated over `k` by
   `lem-weil-pbc-finite-type-residue-field-extension-finitely-generated`.
3. In `B = K ⊗[k] A`, the multiplication map to `K` induced by the residue map has
   maximal kernel `q`, contracts to `p`, and has residue field `K`. Construct it using
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`, and identify its localized
   residue field by `def-weil-pbc-localization-at-prime`.
4. The hypothesis and `lem-weil-pbc-affine-open-stalk-localization` make `B_q` regular.
   The algebra `B` is finite type over `K`, and its residue extension is the identity,
   separable by `def-weil-pbc-separable-field-extension`. Apply
   `lem-weil-pbc-regular-local-separable-residue-smooth` to obtain smoothness at `q`.
5. Descend smoothness to `p` with `lem-weil-pbc-smooth-at-prime-field-extension-descent`.
   Thus some principal localization `A_g`, with `g ∉ p`, is smooth over `k`.
6. By `lem-weil-pbc-principal-localization-open-immersion`, this is an open neighbourhood
   of the original point; `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` makes its
   structure morphism smooth. These opens cover `X`, so `def-sbc-smooth-morphisms`
   gives smoothness of `f`. For the empty scheme both conditions are vacuous. -/
theorem smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Smooth f ↔
      ∀ (L : Type u) [Field L] [Algebra k L], (⊤ : IntermediateField k L).FG →
        ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}),
          IsRegularLocalRing
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) := by
  sorry

end AlgebraicGeometry
