/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification

/-!
# Schematic closure inside a Noetherian compactification

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-lem-nagata-density-normalization/det-nagata-density-normalization-setup.md
(blueprint: det-nagata-density-normalization-setup)
-/


@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
The schematic closure setup for a compactification with Noetherian ambient scheme.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-lem-nagata-density-normalization/det-nagata-density-normalization-setup.md,
node det-nagata-density-normalization-setup (blueprint: det-nagata-density-normalization-setup).

Proof source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-lem-nagata-density-normalization/det-nagata-density-normalization-setup.proof.md.
Proof plan (the six steps of the DAG node):
1. The compactification supplies an open immersion and a proper map. By
   lem-weil-pbc-noetherian-open-subscheme-noetherian, every ambient open is quasi-compact.
   The affine-intersection criterion lem-weil-pbc-quasi-separated-affine-cover-criterion
   makes the ambient scheme quasi-separated. Inverse images of affine opens under the
   open inclusions identify with ambient opens, so both inclusions are quasi-compact.
2. An open immersion is an immersion. Apply lemma-nagata-immersion-open-in-scheme-image
   to the quasi-compact immersion: its canonical image factor is a quasi-compact open
   immersion and scheme-theoretically dense. The equality is Scheme.Hom.toImage_imageι,
   the canonical factorization of def-nagata-scheme-image-factor. No reducedness is used.
3. The image inclusion identifies the image with a closed subset F. Every open of the
   image has the form F intersect O for an ambient open O. To make this quasi-compact,
   extend a relative cover to O and add O minus F; the finite subcover of O restricts to
   one of F intersect O. Apply this to the whole image and affine intersections for qcqs.
   The open complement has precisely F as closed complement, with its given scheme structure.
4. The factorization puts the open image in F, disjoint from its complement. A point of
   the pullback with the complement would project to a point in both, so this scheme is empty.
5. The closed immersion is a monomorphism: on affine charts maps through A/I agree when
   their composites with the surjection A to A/I agree. The pullback projection to X has
   inverse the pair (identity, toImage). The first composite is the identity by its first
   projection; monicity identifies its second projection with the image factor, and
   pullback uniqueness gives the other identity. This also gives the displayed second
   projection formula.
6. Apply lem-weil-pbc-closed-immersion-proper to the proper compactification map and
   the closed image inclusion, proving that their composite is proper.
The proof is postponed at stage 2.
-/
theorem nagataDensityNormalizationSetup {X S : Scheme.{u}} (f : X ⟶ S)
    (c : Compactification f) [IsNoetherian c.Z] :
    IsOpenImmersion c.i.toImage ∧
      QuasiCompact c.i.toImage ∧
      IsSchemeTheoreticallyDominant c.i.toImage ∧
      c.i.toImage ≫ c.i.imageι = c.i ∧
      CompactSpace c.Z ∧
      QuasiSeparatedSpace c.Z ∧
      CompactSpace c.i.image ∧
      QuasiSeparatedSpace c.i.image ∧
      CompactSpace (Scheme.openComplementOfIsClosedImmersion c.i.imageι).toScheme ∧
      IsClosedImmersion c.i.imageι ∧
      IsOpenImmersion ((Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι) ∧
      QuasiCompact ((Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι) ∧
      Set.range c.i.base ∩
          Set.range (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι.base = ∅ ∧
      IsEmpty
        (CategoryTheory.Limits.pullback c.i
          (Scheme.openComplementOfIsClosedImmersion c.i.imageι).ι : Scheme) ∧
      IsIso (CategoryTheory.Limits.pullback.fst c.i c.i.imageι) ∧
      CategoryTheory.Limits.pullback.snd c.i c.i.imageι =
        CategoryTheory.Limits.pullback.fst c.i c.i.imageι ≫ c.i.toImage ∧
      IsProper (c.i.imageι ≫ c.g) := by
  sorry

end AlgebraicGeometry
