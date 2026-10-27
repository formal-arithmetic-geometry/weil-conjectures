/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.UnmarkedFiniteOpenPartsSpace
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint

/-!
# The scheme of section-marked finite open parts

Source: Stacks Project, More on Groupoids in Spaces, Tags 04RI and 04RR,
with the residue-field construction in Tag 04RW and More on Morphisms, Tag 02LK
(blueprint: lem-sfb-section-marked-finite-parts-scheme).

## Main definitions and statements

* `SectionMarkedFiniteOpenPair` is the pair set of the marked finite-part functor.
* `exists_section_marked_finite_parts_scheme` gives its representing scheme, its
  universal open and closed part, and its residue-field points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pairs `(a, Z)` consisting of a map to `Y` and a finite open part of its fibre product
with `X`, through which the base-changed section factors. The two projection equations
express that factorization without choosing a second fibre-product construction.
The witness is a proposition, so only the map and the open are part of the pair's data.
Source: Stacks Project, More on Groupoids in Spaces, equation (04RQ), preceding Tag 04RR
(blueprint: lem-sfb-section-marked-finite-parts-scheme). -/
abbrev SectionMarkedFiniteOpenPair {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (T : Over S) :=
  Σ a : T ⟶ Y, {Z : (pullback f.left a.left).Opens //
    IsFinite (Z.ι ≫ pullback.snd f.left a.left) ∧
      ∃ s : T.left ⟶ Z.toScheme,
        s ≫ Z.ι ≫ pullback.fst f.left a.left = a.left ≫ σ.left ∧
        s ≫ Z.ι ≫ pullback.snd f.left a.left = 𝟙 T.left}

/-- The section-marked finite-part functor is represented by a separated étale scheme.
The equivalences are natural for pullback of opens: the two equations on `b` uniquely
specify the fibre-product map. The pair at `𝟙 M` is the universal part; its first map is
`g` by the forgetful equation, and its finiteness and section factorization are carried
by `SectionMarkedFiniteOpenPair`. The additional `IsClosed` makes it open and closed.
Source: Stacks Project, More on Groupoids in Spaces, Tags 04RI, 04RR, 04PH and 04RW;
More on Morphisms, Tag 02LK (blueprint: lem-sfb-section-marked-finite-parts-scheme).

Proof:
1. Locally finite presentation implies locally finite type. Apply
   lem-sfb-unmarked-finite-open-parts-space to obtain the unmarked algebraic space
   `p : E → Y` and its chartwise étaleness.
2. Each finite open part of `X_T` is closed: `X_T → T` is separated by
   lem-weil-pbc-separated-lqf-base-change; its finite open part is proper over `T`
   by lem-weil-pbc-finite-closed-map-finite-fibres. Apply
   lemma-nagata-proper-to-separated-target to its inclusion into `X_T`.
3. For two parts `Z₁, Z₂` over `T`, their differences are open and closed in the
   finite `Zᵢ`. Their images in `T` are closed by finiteness and open by
   lem-weil-pbc-flat-lfp-open: flatness and local finite presentation survive base
   change and open restriction (lem-weil-pbc-flat-morphism-base-change and
   lem-weil-pbc-qcqs-morphism-permanence). The complement of the two images is
   therefore closed and represents equality of the parts under every base change,
   using lem-weil-pbc-base-change-image. Thus `p` is separated. Apply
   lem-a1-separated-etale-space-scheme to obtain the unmarked scheme `E`.
4. Pull the universal open and closed part on `E` back along the section to obtain
   an open and closed subscheme `M ⊆ E`. A map to `E` factors through `M` exactly
   when its pair contains the section, giving the displayed natural equivalences.
   The map `g` is separated and étale by the closed diagonal of `p` and
   lem-weil-pbc-etale-composition-cancellation. The universal part remains finite,
   open and closed by lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-open-immersion-base-change and lem-weil-pbc-closed-immersion-base-change.
5. At `y` with `f` quasi-finite at `σ(y)`, the point is isolated in its fibre by
   lem-weil-pbc-quasi-finite-at-point-isolated. Apply
   lem-weil-pbc-etale-local-finite-at-point-elementary and restrict its finite open
   part to `Spec κ(y)`. It contains the fibre section, hence defines a point
   `q : Spec κ(y) → M` over `y`. For its image `m`, the residue maps
   `a : κ(y) → κ(m)` and `b : κ(m) → κ(y)` satisfy `ba = 1` by
   lem-weil-pbc-morphism-from-spec-field and lem-weil-pbc-residue-field-point-naturality.
   Injectivity of the field map `b` then gives `ab = 1`, so `a` is an isomorphism.
6. The unmarked atlas is in the chosen universe. Schemehood glues those charts;
   `M` and its universal part are opens of fibre products of schemes in that same
   universe, as required by def-weil-size-convention. -/
theorem exists_section_marked_finite_parts_scheme {S : Scheme.{u}} (X Y : Over S)
    (f : X ⟶ Y) [IsSeparated f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    ∃ (M : Over S) (g : M ⟶ Y)
      (e : ∀ T : Over S, (T ⟶ M) ≃ SectionMarkedFiniteOpenPair f σ T),
      (∀ (T : Over S) (q : T ⟶ M), (e T q).1 = q ≫ g) ∧
      (∀ (T T' : Over S) (h : T' ⟶ T) (q : T ⟶ M),
        ∃ b : pullback f.left (e T' (h ≫ q)).1.left ⟶
            pullback f.left (e T q).1.left,
          b ≫ pullback.fst f.left (e T q).1.left =
            pullback.fst f.left (e T' (h ≫ q)).1.left ∧
          b ≫ pullback.snd f.left (e T q).1.left =
            pullback.snd f.left (e T' (h ≫ q)).1.left ≫ h.left ∧
          (e T' (h ≫ q)).2.val = b ⁻¹ᵁ (e T q).2.val) ∧
      IsSeparated g.left ∧ Etale g.left ∧
      IsClosed ((e M (𝟙 M)).2.val : Set ↑(pullback f.left (e M (𝟙 M)).1.left)) ∧
      (∀ y : Y.left, f.left.IsQuasiFiniteAtPoint (σ.left y) →
        ∃ m : M.left, g.left m = y ∧ IsIso (g.left.residueFieldMap m)) := by
  sorry

end AlgebraicGeometry
