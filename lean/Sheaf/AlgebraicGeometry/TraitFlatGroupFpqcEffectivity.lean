/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Fpqc effectivity for flat group schemes over a trait

Source: Anantharaman, Schemas en groupes, espaces homogenes et espaces algebriques
sur une base de dimension 1, Memoires SMF 33 (1973), Theorem 4.A, printed p.53,
flat case over a trait; section 4.2, Steps 4--6, printed pp.57--62.
(blueprint: lem-sfb-trait-flat-group-fpqc-effectivity).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- An fpqc sheaf of groups over a discrete valuation ring is representable if it has
a separated flat locally finitely presented group-scheme model on an fpqc base cover.
The groups need not be commutative, and the model need not be quasi-compact.

The representing equivalence `e` is a natural bijection on underlying sets. The equality
with `hP` says that the group structure transported through it is the given structure
on `P`, so this is representation as a group sheaf. This formulation permits the group
values and the schemes to live in independent universes.

Source: Anantharaman, Memoires SMF 33 (1973), Theorem 4.A, printed p.53,
and section 4.2, Steps 4--6, printed pp.57--62.
(blueprint: lem-sfb-trait-flat-group-fpqc-effectivity).

Proof plan:
1. Use lem-sfb-flat-trait-group-finite-component-opens to obtain an open subgroup H
   and a covering family of invariant open subfunctors U_a with finite-presentation
   models. Retain its integral fpqc normalization covers B_a with finite fibres and
   almost homogeneous decompositions; no quasi-compactness of the whole model follows.
   The recorded component lemma assumes a strictly henselian DVR; applying it here
   requires an additional reduction, flagged in the worker report for stage 3.
2. Open subfunctors are fpqc sheaves: glue in F and note that the open locus where
   a glued section belongs to the subfunctor contains the images of the cover.
   Apply lem-sfb-fpqc-finite-presentation-normalization-model to H. Its representing
   scheme N inherits the group maps from universal points. Left translation is
   homogeneous, with inverse (y,x) ↦ (yx⁻¹,x) to (g,x) ↦ (gx,x).
   Apply lem-sfb-semitrait-almost-homogeneous-affine-neighbourhoods to N, then
   pqf-lem-locnoeth-lft and lem-sfb-integral-finite-fibre-fpqc-affine-descent to descend H.
3. Base change H to each B_a. Flatness, separatedness and finite type persist by
   lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-separated-base-change and
   lem-sfb-finite-type-composition-base-change; no etaleness of B_a is used.
4. Apply the normalization-model lemma to (U_a) over B_a. The original model retains
   flatness, separatedness and finite presentation by these base-change lemmas and
   lem-weil-pbc-qcqs-morphism-permanence. The almost homogeneous decomposition pulls
   back to the normalization. The affine-neighbourhood lemma and the locally
   Noetherian lemma give a model to which integral fpqc affine descent applies.
5. Descend U_a again along B_a to S using its original finite-presentation model,
   the affine-neighbourhood property just obtained, and local Noetherianness.
   Do this separately for every a; no uniform finite cover of all pieces is needed.
6. Since Zariski covers are fpqc, F is a Zariski sheaf. The representable open
   subfunctors U_a cover F on every test scheme. Apply lem-pc-schemes-criterion to
   obtain a representing S-scheme. -/
theorem trait_flat_group_fpqc_effectivity
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ GrpCat.{v})
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (CommRingCat.of R)))
      (F ⋙ forget GrpCat))
    {T : Scheme.{u}} (p : T ⟶ Spec (CommRingCat.of R))
    [Flat p] [Surjective p] [QuasiCompact p]
    (P : Over T) [hP : GrpObj P]
    [IsSeparated P.hom] [Flat P.hom] [LocallyOfFinitePresentation P.hom]
    (hmodel : ∃ e : (((Over.map p).op ⋙ F) ⋙ forget GrpCat).RepresentableBy P,
      GrpObj.ofRepresentableBy P ((Over.map p).op ⋙ F) e = hP) :
    (F ⋙ forget GrpCat).IsRepresentable := by
  sorry

end AlgebraicGeometry
