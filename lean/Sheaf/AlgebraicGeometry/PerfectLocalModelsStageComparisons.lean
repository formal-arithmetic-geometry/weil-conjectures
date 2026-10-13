/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedOpenGluingObjects
import Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Stage object with compatible local limit comparisons

Source: Stacks Project, Tag 09RF, two-open induction and the object construction of Tag 08DG.
(blueprint: lem-pc-perfect-local-models-stage-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The base-change and derived open-restriction types need this elaboration budget.
set_option synthInstance.maxHeartbeats 400000 in
-- Elaborating the transported overlap restrictions needs this instance-search budget.
/-- Construct a stage object and compatible local comparisons, before gluing any global map.
Source: Stacks Project, Tags 09RE, 09RF and 08DG, two-open construction.
(blueprint: lem-pc-perfect-local-models-stage-comparisons).

Proof: Work on the directed tail above j. The overlap of the compact opens is
quasi-compact: the base-changed structure morphism is quasi-separated and its
base Spec R_j is affine, hence Y_j is quasi-separated. The overlap's inclusion
is a quasi-compact open immersion; composing it with the base-changed finite
presentation structure morphism gives a finite presentation map to Spec R_j.
Restrict A and B to this overlap; pullback
preserves their perfectness. Restrict the specified limit comparisons and compose
the first with the inverse of the second to get the prescribed overlap isomorphism.
The coherent composition and open-restriction comparisons identify these objects
with the limit pullbacks of the two overlap restrictions. Apply perfect morphism
continuity on the tail to descend the isomorphism and its inverse, then stabilize
their two inverse equations at a common stage k. The descended transition has the
prescribed limit pullback, including its compatibility equation.
Let f_kj : Y_k to Y_j be the canonical stage transition. The cocone equation
and baseChangeMap_comp give g_k followed by f_kj = g_j. Set U' = f_kj inverse U
and V' = f_kj inverse V; inverse image preserves unions and the total open, so
these opens cover Y_k and their g_k inverse images are P and Q.
Apply derived open object gluing on this inverse-image cover of Y_k, with the two
pulled objects and this transition, to construct F and local identifications. On
each covering open its restriction is isomorphic to a perfect pullback; composing
the strictly perfect local model isomorphisms proves perfectness is iso invariant.
The restriction/pullback
comparison identifies the derived pullback along the inclusion with this exact
restriction, giving the two perfectness assertions. Pointwise neighbourhood
witnesses are left to the caller, as is the global morphism.
Pull these local identifications to the limit, use the original comparisons to E,
and compose with the restriction/pullback comparisons to obtain pU and pV.
On the overlap the object-gluing transition equation and the prescribed limit
pullback of the descended transition identify the two composites. Transport the two
isomorphisms backwards through the derived equivalences
induced by Modules.overEquiv P and Q. These equivalences are fully faithful, so their
preimages are isomorphisms. Naturality of the equivalence units and of the exact
restriction-composition comparisons identifies the overlap equation with equality
of the displayed derivedOpenHomRestriction maps.
No global map to E is constructed here: the caller must apply Hom Mayer-Vietoris.
Empty schemes and overlaps are harmless, equal opens use the same transition
formula, and directedness of the tail needs no strictness of the preorder.
The stage object is an existential witness, not data of a definition. -/
theorem perfect_local_models_stage_comparisons
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    :
    let Yj := pullback t (Spec.map (R.map (homOfLE hij)))
    let X := pullback t (Spec.map (c.ι.app i))
    let gj := baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
    ∀ (U V : Yj.Opens) (hcover : U ⊔ V = ⊤)
      (hU : IsCompact (U : Set Yj)) (hV : IsCompact (V : Set Yj))
      (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
      (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
      (E : schemeDerivedCategory X)
      (φU : (derivedPullback (gj ∣_ U)).obj A ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ U)).mapDerivedCategory.obj E)
      (φV : (derivedPullback (gj ∣_ V)).obj B ≅
        (schemeOpenRestriction X (gj ⁻¹ᵁ V)).mapDerivedCategory.obj E),
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))))),
        ∃ (U' V' : (pullback t
            (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens),
          U' ⊔ V' = ⊤ ∧
          U'.toScheme.IsPerfect ((derivedPullback U'.ι).obj F) ∧
          V'.toScheme.IsPerfect ((derivedPullback V'.ι).obj F) ∧
        let P := gj ⁻¹ᵁ U
        let Q := gj ⁻¹ᵁ V
        let L := (derivedPullback g).obj F
        let RU := (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) P).mapDerivedCategory
        let RV := (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) Q).mapDerivedCategory
        ∃ (pU : RU.obj L ≅ RU.obj E) (pV : RV.obj L ≅ RV.obj E),
          derivedOpenHomRestriction X.toRingedSpace
              (homOfLE (show P ⊓ Q ≤ P from inf_le_left)) (E := L) (F := E) pU.hom =
            derivedOpenHomRestriction X.toRingedSpace
              (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)) (E := L) (F := E) pV.hom := by sorry

end AlgebraicGeometry
