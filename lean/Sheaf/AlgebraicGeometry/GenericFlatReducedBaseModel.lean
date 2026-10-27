/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # An integral affine generic-flat model over the reduced base

Source: Stacks Project, Tag 0578, first proof paragraph, and Tag 052A.
(blueprint: lem-trf-generic-flat-reduced-base-model)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite type family over an irreducible base has an integral affine open in
its reduction on which it is flat and locally finitely presented, with the same
residue fields and canonical fibres.

Source: Stacks Project, Tag 0578, first proof paragraph; Tags 052A and 054M.
(blueprint: lem-trf-generic-flat-reduced-base-model)

Proof:
1. Apply lem-weil-pbc-reduction-universal-homeomorphism to Y. Its reduction is
   reduced, and the reduction map is a closed immersion and a homeomorphism.
   Lift the generic point along this homeomorphism. Its closure is the entire
   reduction, which is therefore irreducible and integral (def-pc-integral-scheme).
2. Base change f to the reduction. The locally-finite-type and quasi-compact
   base-change assertions (lem-weil-pbc-lft-base-change and
   lem-weil-pbc-qcqs-morphism-permanence) preserve finite type. Apply
   lem-sbc-generic-flat-finite-presentation to obtain a nonempty open with flat,
   locally finitely presented restricted family.
3. The lifted generic point belongs to this open. Use
   lem-weil-pbc-affine-opens-basis to choose an affine neighbourhood W within it.
   Reducedness restricts to W, and its generic point has closure W; hence W is
   nonempty and integral, by def-pc-reduced-scheme and def-pc-integral-scheme.
4. Pullback pasting identifies X ×_Y W with the restriction of the preceding
   family. Finite type, flatness and local finite presentation persist by
   lem-weil-pbc-lft-base-change, lem-weil-pbc-qcqs-morphism-permanence and
   lem-weil-pbc-flat-morphism-base-change.
5. The reduction homeomorphism takes W onto an open V containing eta.
   Its injectivity gives uniqueness of the generic lift. The reduction closed
   immersion induces residue-field isomorphisms by
   lem-weil-pbc-closed-immersion-residue-field-iso; so does W's open inclusion by
   lem-weil-pbc-residue-field-point-naturality. Composition gives the stated
   residue-field map of q.
6. Use lem-weil-pbc-fibre-of-base-change and these residue-field isomorphisms.
   The two projection equations characterize the canonical fibre comparison,
   which is an isomorphism. The generic fibre is locally finitely presented by
   base change (lem-weil-pbc-qcqs-morphism-permanence). -/
theorem exists_integral_affine_genericFlat_reducedBase {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [IrreducibleSpace Y]
    (η : Y) (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ W : Y.nilradical.subscheme.Opens,
      (W : Set Y.nilradical.subscheme).Nonempty ∧ IsAffineOpen W ∧
      IsIntegral W.toScheme ∧
      LocallyOfFiniteType (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)) ∧
      QuasiCompact (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)) ∧
      Flat (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)) ∧
      LocallyOfFinitePresentation (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)) ∧
      (∃ V₀ : Y.Opens, η ∈ V₀ ∧
        Topology.IsOpenEmbedding (W.ι ≫ Y.nilradical.subschemeι) ∧
        Set.range (W.ι ≫ Y.nilradical.subschemeι) = (V₀ : Set Y)) ∧
      (∀ w : W.toScheme,
        IsIso ((W.ι ≫ Y.nilradical.subschemeι).residueFieldMap w) ∧
        ∃ e : (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)).fiber w ≅
            f.fiber ((W.ι ≫ Y.nilradical.subschemeι) w),
          e.hom ≫ f.fiberι ((W.ι ≫ Y.nilradical.subschemeι) w) =
            (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)).fiberι w ≫
              pullback.fst f (W.ι ≫ Y.nilradical.subschemeι) ∧
          e.hom ≫ f.fiberToSpecResidueField ((W.ι ≫ Y.nilradical.subschemeι) w) =
            (pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)).fiberToSpecResidueField w ≫
              Spec.map ((W.ι ≫ Y.nilradical.subschemeι).residueFieldMap w)) ∧
      (∃ ηW : W.toScheme, (W.ι ≫ Y.nilradical.subschemeι) ηW = η ∧
        (∀ w : W.toScheme, (W.ι ≫ Y.nilradical.subschemeι) w = η → w = ηW) ∧
        IsGenericPoint ηW (Set.univ : Set W.toScheme) ∧
        LocallyOfFinitePresentation
          ((pullback.snd f (W.ι ≫ Y.nilradical.subschemeι)).fiberToSpecResidueField ηW)) := by
  sorry

end AlgebraicGeometry
