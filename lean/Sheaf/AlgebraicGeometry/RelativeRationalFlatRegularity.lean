/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Sheaf.AlgebraicGeometry.RelativeRationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Flat detection of relative rational regularity

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, Section 2.5, pp.55--58,
especially Proposition 5 (blueprint: lem-sfb-relative-rational-flat-regularity).

The first conjunct gives the maximal representative, uniqueness, the uniquely characterized
flat composite, its exact domain, and descent of everywhere-defined representatives.
The second gives the smooth open-product specialization. The composite is specified on
all representatives by the canonical restriction of the given map, so its existence is
not an assumption about an arbitrary rational map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flat pullback detects the full domain of a relative rational map, and an open in a
smooth product with nonempty projection fibres gives a flat surjective test map.
Source: BLR 2.5, definitions and graph description, pp.55--57; Proposition 5, p.58
(blueprint: lem-sfb-relative-rational-flat-regularity).

Proof:
1. Finite type over the Noetherian base makes X, X', Y and X times Y Noetherian
   (lem-weil-pbc-finite-type-over-noetherian, lem-sfb-finite-type-composition-base-change).
   Their opens have quasi-compact inclusions (lem-sfb-noetherian-open-immersion-qc).
   The graph maps and restrictions of p are quasi-compact, and p is locally finitely
   presented (lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-proper-fp-permanence,
   pqf-lem-lft-fp-locnoeth).
2. Representatives agree on their overlaps: the common fibrewise dense open is
   schematically dense by lem-sfb-smooth-fibrewise-dense-open-base-change, after
   lem-weil-pbc-smooth-restrict-open-subschemes. Apply
   lemma-nagata-ext-scheme-theoretically-dominant-separated and then
   lem-weil-pbc-scheme-morphism-gluing. This gives the unique maximal representative
   and uniqueness for representatives defined everywhere, without reducing the base.
3. The closed graph is independent of representatives: restrict its kernel ideal to
   a common fibrewise dense open and use injectivity of restriction. Use
   lemma-nagata-scheme-image-ideal-qc and lemma-nagata-scheme-image-partial-section.
4. The maximal domain is exactly the union of opens on which the first graph projection
   is an isomorphism. The inverse projection gives a representative; glue it to any
   existing representative (lem-weil-pbc-scheme-morphism-gluing).
5. Fibres of p are flat and locally finitely presented by
   lem-sfb-pointwise-flatness-base-change and lem-weil-pbc-qcqs-morphism-permanence,
   hence open by lem-weil-pbc-flat-lfp-open. The inverse image of every representative
   domain is therefore fibrewise dense. Pullback gives a unique composite class and
   the inclusion of the inverse image of the original domain in the composite domain.
6. Apply lem-sfb-scheme-image-flat-base-change to the quasi-compact graph map:
   the composite graph is the pullback of the original graph along p.
7. The image V of the composite domain is open. Its map from the composite domain is
   flat, surjective and quasi-compact. The original graph projection over V becomes
   an isomorphism on this cover, hence is an isomorphism by
   lem-weil-pbc-fpqc-descend-isomorphism. Step 4 yields the reverse domain inclusion.
8. If p is surjective and the composite is everywhere defined, the domain equality
   forces the original domain to be all of X. Step 2 gives existence and uniqueness.
9. For the open-product clause, base change makes the second projection smooth
   (lem-pc-proper-base-change), hence flat (sbc-lem-smooth-criterion). Restriction
   to E preserves smoothness. Composition gives smoothness over S
   (lem-trf-smooth-composition). Nonempty fibres give surjectivity. The product is
   Noetherian, so the open inclusion is quasi-compact and of finite type; composition
   gives finite type over S. The previous clauses now apply to this projection. -/
theorem relative_rational_flat_regularity
    {S X X' Y : Scheme.{u}} [IsNoetherian S]
    (sX : X ⟶ S) (sX' : X' ⟶ S) (sY : Y ⟶ S)
    [Smooth sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    [Smooth sX'] [LocallyOfFiniteType sX'] [QuasiCompact sX']
    [Smooth sY] [LocallyOfFiniteType sY] [QuasiCompact sY] [IsSeparated sY] :
    (∀ φ : Scheme.RelativeRationalMap sX sY,
      (∃! f : φ.domain.toScheme ⟶ Y,
        φ.Represents φ.domain f ∧
        ∀ (a : Scheme.RelativePartialMap sX sY), a.classOf = φ →
          ∀ h : a.domain ≤ φ.domain, X.homOfLE h ≫ f = a.hom) ∧
      (∀ f g : X ⟶ Y,
        φ.Represents ⊤ (X.topIso.hom ≫ f) →
        φ.Represents ⊤ (X.topIso.hom ≫ g) → f = g) ∧
      (∀ (p : X' ⟶ X), p ≫ sX = sX' → Flat p →
        ∃! ψ : Scheme.RelativeRationalMap sX' sY,
          φ.IsComposite p ψ ∧ ψ.domain = p ⁻¹ᵁ φ.domain ∧
          (Surjective p →
            (∃ f : X' ⟶ Y, ψ.Represents ⊤ (X'.topIso.hom ≫ f)) →
            ∃! f : X ⟶ Y, φ.Represents ⊤ (X.topIso.hom ≫ f)))) ∧
    (∀ (H : Scheme.{u}) (sH : H ⟶ S),
      Smooth sH → LocallyOfFiniteType sH → QuasiCompact sH →
      ∀ E : (pullback sH sX).Opens,
        (∀ x : X, Nonempty ((E.ι ≫ pullback.snd sH sX).fiber x)) →
        Flat (E.ι ≫ pullback.snd sH sX) ∧
        Surjective (E.ι ≫ pullback.snd sH sX) ∧
        Smooth (E.ι ≫ pullback.snd sH sX ≫ sX) ∧
        LocallyOfFiniteType (E.ι ≫ pullback.snd sH sX ≫ sX) ∧
        QuasiCompact (E.ι ≫ pullback.snd sH sX ≫ sX)) := by
  sorry

end AlgebraicGeometry
