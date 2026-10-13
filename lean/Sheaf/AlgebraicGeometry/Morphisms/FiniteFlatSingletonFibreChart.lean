/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A finite flat chart with a singleton fibre

Source: Stacks Project, Tags 02LK and 0BJH.
(blueprint: lem-sbc-finite-flat-singleton-fibre-chart)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Etale localization separates the selected point from the other points of its fibre.

Source: Stacks Project, Tag 02LK (more-morphisms-lemma-etale-makes-quasi-finite-finite),
and Tag 0BJH (pione-lemma-ramification-quasi-finite-flat), first proof paragraph.
(blueprint: lem-sbc-finite-flat-singleton-fibre-chart)

Proof: Apply 02LK to the finite, hence quasi-finite, morphism at x. After an etale
base neighbourhood T of f(x), select the finite open-and-closed piece Z containing
an appropriate lift z of x and having only z above g(z). The map a to X and the
map b to Y are etale and the square commutes. Flatness is preserved by base
change and restriction; the schemes are locally Noetherian because etale maps
are locally of finite type. For each w in Z, g is etale at w if and only if
f is etale at a(w): the equation a f = g b and etale b identify the etale
loci of g and a f, and etale localization on the source identifies the latter
with the inverse image of the etale locus of f. These loci are open, so being
etale at a point is expressed by the existence of the indicated open neighbourhood.
No ramification hypothesis or positive-dimension hypothesis is used. -/
theorem exists_finite_flat_singleton_fibre_chart
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X) :
    ∃ (Z T : Scheme.{u}) (a : Z ⟶ X) (b : T ⟶ Y) (g : Z ⟶ T) (z : Z),
      Etale a ∧ Etale b ∧ IsFinite g ∧ Flat g ∧
      IsLocallyNoetherian Z ∧ IsLocallyNoetherian T ∧
      a ≫ f = g ≫ b ∧ a z = x ∧
      (∀ w : Z, g w = g z → w = z) ∧
      (∀ w : Z, (∃ V : Z.Opens, w ∈ V ∧ Etale (V.ι ≫ g)) ↔
        ∃ V : X.Opens, a w ∈ V ∧ Etale (V.ι ≫ f)) := by sorry

end AlgebraicGeometry.Scheme
