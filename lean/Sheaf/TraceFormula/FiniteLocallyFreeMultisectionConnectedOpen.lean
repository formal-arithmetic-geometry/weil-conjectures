/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField

import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.FlatReducedSectionComponentOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat

/-!
# Descent of a connected open using a finite locally free multisection

Source: Stacks Project, More on Morphisms, Tag 057I, label
`lemma-descent-connected-fibres`.
(blueprint: lem-trf-finite-locally-free-multisection-connected-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A flat finitely presented family with geometrically reduced fibres and a finite locally free
multisection admits a quasi-compact open whose nonempty fibres are geometrically connected and
which agrees with the original family over a prescribed geometrically connected fibre.

Source: Stacks Project, More on Morphisms, Tag 057I, label `lemma-descent-connected-fibres`.
Proof:
1. Base change along `p` to get `Y = X ×_B Z` with its induced section. Flatness, finite
   presentation and geometric reducedness persist under base change, so the relative connected
   component `C` containing the section is open (`lem-trf-flat-reduced-section-component-open`,
   `lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`).
2. Over `Z ×_B Z`, the two inverse images of `C` are the component loci for the two sections
   (`lem-sbc-section-component-cartesian`). At each point above `b₀` they are the whole fibre,
   by geometric connectedness. Their openness gives a neighbourhood `W` of this finite fibre
   on which each section belongs to the other section's component locus.
3. Finite locally free maps are open and closed, and stable under base change and composition
   (`lem-trf-finite-locally-free-composition`, `lem-weil-pbc-finite-morphism-permanence`,
   `lem-weil-pbc-flat-lfp-open`, `lem-weil-pbc-finite-closed-map-finite-fibres`). Shrink to an
   affine neighbourhood `V` of `b₀` whose inverse image in `Z ×_B Z` lies in `W`, and further
   inside the image of `Z`. Then `Z_V → V` is finite locally free and surjective, hence fpqc.
4. Membership of each section in the other's component forces equality of the two pulled-back
   component loci. Descend `C` to an open in `X_V` along the induced fpqc cover
   (`lem-weil-pbc-open-subscheme-fpqc-descent`).
5. On the affine base `V`, `C` is quasi-compact (`lem-trf-section-component-quasi-compact`).
   Its image under the finite surjective cover is the descended open, which is quasi-compact.
6. Over `b₀`, `C` is the whole fibre after faithfully flat base change, so the descended fibre
   equals `X_b₀`. Every nonempty descended fibre becomes a connected component containing a
   rational section point after extension to a point of `Z_b`; it is geometrically connected
   by `lem-sbc-connected-rational-point-geometrically-connected`. Reflect this along the field
   extension (`lem-weil-geometrically-connected-check-after-extension`). Finally view the open
   of `X_V` as an open of `X`.
(blueprint: lem-trf-finite-locally-free-multisection-connected-open) -/
theorem exists_quasiCompact_open_geometricallyConnected_fibres_of_finiteLocallyFree_multisection
    {X B Z : Scheme.{u}} (f : X ⟶ B) (p : Z ⟶ B) (σ : Z ⟶ X)
    (hσ : σ ≫ f = p) [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] (hred : ∀ b : B, GeometricallyReduced (f.fiberToSpecResidueField b))
    [Scheme.Hom.IsFiniteLocallyFree p] (b₀ : B)
    (hp₀ : Set.Nonempty (Set.range (p.fiberι b₀)))
    (hconn : GeometricallyConnected (f.fiberToSpecResidueField b₀)) :
    ∃ (X0 : Scheme.{u}) (i : X0 ⟶ X), IsOpenImmersion i ∧ CompactSpace X0 ∧
      IsIso (Scheme.Hom.fiberMap (a := i ≫ f) (b := f) i rfl
        (B.fromSpecResidueField b₀)) ∧
      (∀ b : B, Set.Nonempty (Set.range ((i ≫ f).fiberι b)) →
        GeometricallyConnected ((i ≫ f).fiberToSpecResidueField b)) := by
  sorry

end AlgebraicGeometry
