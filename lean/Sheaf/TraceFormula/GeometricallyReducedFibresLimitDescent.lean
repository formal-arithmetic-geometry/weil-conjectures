/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import Sheaf.TraceFormula.GeometricReducedFibreLocusConstructible

/-!
# Geometrically reduced fibres descend along affine inverse limits

Source: Stacks Project, `more-morphisms.tex`, Tags 0579 and 0576, and
`limits.tex`, Tag 05F4 (blueprint: lem-trf-geometrically-reduced-fibres-limit-descent).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/--
For an inverse system of quasi-compact quasi-separated schemes with affine transitions,
a finite-presentation family whose geometric fibres are reduced over the limit has reduced
geometric fibres at every sufficiently late stage.

Source: Stacks Project, `more-morphisms.tex`, Tags 0579 and 0576, and `limits.tex`, Tag 05F4;
(blueprint: lem-trf-geometrically-reduced-fibres-limit-descent).
Proof: the reduced-geometric-fibre locus of the finite-presentation family over the fixed stage
is constructible by Tag 0579.  Its inverse image on the limit is the whole limit by Tag 0576,
so the limit image is contained in that constructible locus.  Tag 05F4 then gives a later stage
whose image is contained in the same locus.  Applying Tag 0576 again identifies that containment
with geometric reducedness of every fibre at each later stage.  Empty schemes and fibres remain
allowed throughout, and no flatness hypothesis is used.
-/
theorem exists_eventually_geometricallyReduced_fibres
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (a : I) {Y : Scheme.{u}}
    (q : Y ⟶ D.obj (op a)) [LocallyOfFinitePresentation q] [QuasiCompact q]
    [QuasiSeparated q]
    (hred : ∀ s : c.pt,
      GeometricallyReduced ((pullback.snd q (c.π.app (op a))).fiberToSpecResidueField s)) :
    ∃ b : I, ∃ hab : a ≤ b,
      ∀ (i : I) (hbi : b ≤ i) (s : D.obj (op i)),
        GeometricallyReduced
          ((pullback.snd q (D.map (homOfLE (hab.trans hbi)).op)).fiberToSpecResidueField s) := by
  sorry

end AlgebraicGeometry
