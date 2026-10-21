/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Schematic closure inside a Noetherian compactification

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization/det-nagata-density-normalization-setup.md`.
(blueprint: det-nagata-density-normalization-setup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The schematic closure and its complementary open in a Noetherian compactification.
Source: blueprint main-20261015, density-normalization setup, clauses (1)--(4)
(blueprint: det-nagata-density-normalization-setup).

Proof: (1) Noetherian opens are quasi-compact by
lem-weil-pbc-noetherian-open-subscheme-noetherian. Their affine intersections are
quasi-compact, giving quasi-separatedness by
lem-weil-pbc-quasi-separated-affine-cover-criterion. This also makes j and j_V
quasi-compact. (2) Apply lemma-nagata-immersion-open-in-scheme-image to j; the
canonical image factorization gives j_Z followed by i equals j, with j_Z open,
quasi-compact and schematically dense. (3) The image is a closed subspace of a
Noetherian space; its opens are closed in quasi-compact ambient opens, so it is
qcqs by the same affine-intersection criterion. The complementary open is qc.
(4) Factorization makes j(X) disjoint from V. A point of the fibre product would
contradict disjointness, so that product is empty. (5) The other product has
inverse (id_X,j_Z) to its first projection. Closed-immersion monicity identifies
its second projection with the first followed by j_Z; pullback uniqueness checks
both inverse equations. (6) Apply lem-weil-pbc-closed-immersion-proper to i and p.
-/
theorem nagataDensityNormalizationSetup {X S : Scheme.{u}} (f : X ⟶ S)
    (c : Compactification f) [IsNoetherian c.Z] :
    IsOpenImmersion c.i.toImage ∧ QuasiCompact c.i.toImage ∧
    IsSchemeTheoreticallyDominant c.i.toImage ∧ c.i.toImage ≫ c.i.imageι = c.i ∧
    CompactSpace c.Z ∧ QuasiSeparatedSpace c.Z ∧
    CompactSpace c.i.image ∧ QuasiSeparatedSpace c.i.image ∧
    CompactSpace (Scheme.openComplementOfIsClosedImmersion c.i.imageι).toScheme ∧
    IsClosedImmersion c.i.imageι ∧
    IsOpenImmersion (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι ∧
    QuasiCompact (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι ∧
    Set.range c.i.base ∩
      Set.range (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι.base = ∅ ∧
    IsEmpty (pullback c.i (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι : Scheme) ∧
    IsIso (pullback.fst c.i c.i.imageι) ∧
    pullback.snd c.i c.i.imageι = pullback.fst c.i c.i.imageι ≫ c.i.toImage ∧
    IsProper (c.i.imageι ≫ c.g) := by
  sorry

end AlgebraicGeometry
