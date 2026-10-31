/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec

/-!
# Affine-cover criterion for quasi-affine morphisms

Source: Stacks Project, Morphisms of Schemes, Tag 01SM, lemma-characterize-quasi-affine,
equivalence (1) and (2) (blueprint: lem-sfb-quasi-affine-affine-cover-criterion).

The theorem states that quasi-affineness of a morphism is equivalent to the existence of an
arbitrary affine-open cover of the target whose inverse images are quasi-affine schemes. The
cover index type is unrestricted except for the scheme universe, and may be empty.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A morphism is quasi-affine exactly when this holds on an arbitrary affine-open cover of its
    target.

Source: Stacks Project, Morphisms of Schemes, Tag 01SM, lemma-characterize-quasi-affine,
equivalence (1) and (2) (blueprint: lem-sfb-quasi-affine-affine-cover-criterion).

Proof, following Tag 01SM and the six steps of the node:
1. If `h` is quasi-affine, choose an affine-open cover of `Q`. Each inverse image is
   quasi-affine by def-nagata-quasi-affine-morphism. This includes the empty cover.
2. Conversely, write `Pj = h` inverse `Qj`. By
   lem-trf-quasi-affine-canonical-affine-embedding each `Pj` is quasi-compact and separated,
   hence quasi-separated by lem-pc-separated-quasi-separated. Affine `Qj` are qcqs by
   lem-weil-pbc-affine-scheme-qcqs, so lem-weil-pbc-qcqs-morphism-permanence makes the
   restrictions qcqs. Apply lem-pc-quasi-compact-local-on-target to obtain QuasiCompact h.
3. The opens `Pj` times over `Qj` with `Pj` cover `P` times over `Q` with `P`, by
   lem-weil-pbc-open-fibre-product. The restriction of the diagonal of `h` is the diagonal
   of each restriction. These are quasi-compact, so lem-pc-quasi-compact-local-on-target
   makes the diagonal quasi-compact: h is quasi-separated by def-weil-quasi-separated-morphism.
4. Apply lem-sfb-canonical-relative-affinization to h. The canonical map c from P to the
   relative spectrum of h pushforward O_P identifies over each Qj with Pj.toSpecΓ, an
   open immersion by lem-trf-quasi-affine-canonical-affine-embedding.
5. If c(x) = c(x'), their images in Q agree, and a Qj containing that image reduces
   injectivity to the open immersion on Pj. Composing the chart open immersions gives
   open immersions into the relative spectrum. Apply
   lem-weil-pbc-open-immersion-injective-local-source to conclude c is an open immersion.
6. Over any affine open U of Q, the relative spectrum is affine by
   lem-weil-pbc-affine-morphism-relative-spec. The restriction of c is an open immersion
   by lem-weil-pbc-open-immersion-base-change. Its source is quasi-compact because h is
   quasi-compact (def-weil-finite-type-morphism). Thus this inverse image is a
   quasi-compact open of an affine scheme, and def-nagata-quasi-affine-morphism gives
   IsQuasiAffineHom h. No quasi-compactness or quasi-separatedness of Q is used.
-/
theorem isQuasiAffineHom_iff_exists_affineOpen_cover {P Q : Scheme.{u}} (h : P ⟶ Q) :
    IsQuasiAffineHom h ↔
      ∃ (J : Type u) (Qj : J → Q.Opens),
        (⨆ j : J, Qj j) = ⊤ ∧
          ∀ j : J, IsAffineOpen (Qj j) ∧ (h ⁻¹ᵁ Qj j).toScheme.IsQuasiAffine := by
  sorry

end AlgebraicGeometry
