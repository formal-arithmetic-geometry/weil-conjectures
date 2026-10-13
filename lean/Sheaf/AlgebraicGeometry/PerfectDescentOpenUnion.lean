/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # PerfectDescentOpenUnion

Source: Stacks Project, Tag 09RF (blueprint: lem-pc-perfect-descent-open-union).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The induction step for descent: glue descent on a quasi-compact open and an
additional affine open.
Source: Stacks Project, Tag 09RF, the two-open induction step
(blueprint: lem-pc-perfect-descent-open-union).

Proof: Given an open-immersion presentation of `W ⊔ V` and a perfect complex on
its limit base change, restrict to the inverse images of `W` and `V`. Apply the two
hypotheses to descend those restrictions. Directedness gives a common later stage;
derived pullback preserves perfectness. Quasi-separatedness makes `W ∩ V`
quasi-compact, so its map to `Spec R_i` is finitely presented. Apply Tag 09RE to
the overlap identification and its inverse, then stabilize the two inverse
relations, obtaining an isomorphism on a stage overlap. Use derived adjunction to
view the two comparison maps as maps into the restriction of `Rf_* E`. Restriction
of derived direct image to opens agrees with the restricted morphism's direct
image (Tag 08FE). The overlap equation makes these adjoints compatible. Tag 08DG
glues the two objects and their maps into `Rf_* E`. The glued object is perfect
because this is local on the two opens. The adjoint of the glued map is an
isomorphism: on each member of the pulled-back cover it is the given comparison
isomorphism, so the cone has zero cohomology sheaves. Open-immersion and pullback
identifications give exactly the stated canonical map for the union. -/
theorem perfect_descent_open_union
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (W V : Xi.Opens) (hW : IsCompact (W : Set Xi)) (hV : IsAffineOpen V)
    (dW : PerfectDescentOnOpen R c i Xi s W)
    (dV : PerfectDescentOnOpen R c i Xi s V) :
    PerfectDescentOnOpen R c i Xi s (W ⊔ V) := by sorry

end AlgebraicGeometry
