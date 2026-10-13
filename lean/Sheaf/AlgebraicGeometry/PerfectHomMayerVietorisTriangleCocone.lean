/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.AlgebraicGeometry.PerfectHomLocalComparison
public import Sheaf.AlgebraicGeometry.PerfectHomTriangleRow
import Sheaf.AlgebraicGeometry.PerfectThickClosure
import Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial
import Sheaf.AlgebraicGeometry.PerfectHomStageColimit

/-! # Coherent Mayer--Vietoris triangle cocones before forming Hom rows

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-triangle-cocone).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

/-- A geometric cocone of distinguished triangles in D(O_Y), obtained by pushing
stage Mayer--Vietoris triangles to Y. Central Hom identifications are pinned to
canonical pullback transport. The four outer column comparisons are local.
No abelian-group row, zero-composite witness, or short-complex presentation is
supplied by this statement.

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-triangle-cocone).

Proof:
1. Pull U,V back to Y and to each finite and limit stage. The cover of Y is
   exhaustive since the range of t is U union V. These schemes and opens are qcqs:
   s is qcqs over an affine scheme, stage projections are affine, and the two opens
   are compact (V is affine). Their intersections are compact by quasi-separatedness.
2. Pull back P,Q. Localized strictly perfect models show that these and their open
   restrictions are perfect. Shifts are perfect by thick closure; Q and all its
   pullbacks therefore have quasi-coherent cohomology. At each stage use the
   K-injective Mayer--Vietoris triangle, and push it to Y by the triangulated derived
   direct image of the stage projection. Its first object is the direct image of Q
   pulled to that stage. Do the same for the limit stage.
3. For a stage transition h use the unit Q_j -> Rh_* Lh* Q_j and the natural
   Mayer--Vietoris boundary construction. Compare the pushed local terms using the
   right-derived comparison determined by its derivation unit; do not choose an
   arbitrary unpinned isomorphism. The universal property of the right derived
   functor gives the identity and composition equations: both sides are derived
   lifts of the same underived direct-image comparison, hence equal. Naturality of
   the K-injective short exact sequence, including its boundary, gives morphisms
   of triangles. These equations give the triangle functor D and its cocone d.
4. The Hom adjunction for the stage projection, followed by the zero-shift
   comparison, gives e; its limit version gives b. For a transition the adjunct of
   f followed by the unit on Q is pullback(f), followed by pullback of the unit and
   the counit. The adjunction triangle identity cancels these last two maps.
   Conjugating by the counit-pinned pullback composition comparison gives precisely
   perfectStageMap. The same calculation for a cocone leg gives perfectLimitMap.
5. The four neighboring terms are, by open adjunction, the stage Hom diagrams of
   the restricted perfect pairs, with Q shifted by -1 at the first two terms.
   The two-open terms are products and the intersection terms are single diagrams.
   Present each with perfect_hom_stage_colimit. Underlying-set preservation of
   filtered group colimits and preservation of binary products identify their
   column maps with the basic and product constructors of PerfectHomLocalMap;
   conjugate by the adjunction and shift equivalences using its equiv constructor.
   All comparison equations use the units pinned in step 3. Empty opens have zero
   local groups, and the same constructions apply. No filtered-colimit exactness
   or continuity theorem is used. -/
theorem perfect_hom_mayerVietoris_triangle_cocone
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    : ∃ (D : Set.Ici i ⥤ Triangle (schemeDerivedCategory Y)) (d : Cocone D),
        (∀ j, D.obj j ∈ distTriang (schemeDerivedCategory Y)) ∧
        d.pt ∈ distTriang (schemeDerivedCategory Y) ∧
        ∃ (e : ∀ j : Set.Ici i, ULift.{u} (P ⟶ (D.obj j).obj₁⟦(0 : ℤ)⟧) ≃
          ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q))
          (b : ULift.{u} (P ⟶ d.pt.obj₁⟦(0 : ℤ)⟧) ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici i) (hjk : j ≤ k)
          (f : ULift.{u} (P ⟶ (D.obj j).obj₁⟦(0 : ℤ)⟧)),
          e k ⟨f.down ≫ (D.map (homOfLE hjk)).hom₁⟦(0 : ℤ)⟧'⟩ =
            perfectStageMap R s j.property hjk (e j f)) ∧
        (∀ (j : Set.Ici i) (f : ULift.{u} (P ⟶ (D.obj j).obj₁⟦(0 : ℤ)⟧)),
          b ⟨f.down ≫ (d.ι.app j).hom₁⟦(0 : ℤ)⟧'⟩ =
            perfectLimitMap R c s j.property (e j f)) ∧
        ∀ (r : Fin 5), r.val ≠ 2 →
          PerfectHomLocalMap R c i X s₀ U V
            (colimit.desc ((D ⋙ perfectHomTriangleRowFunctor Y P).flip.obj r)
              ⟨(perfectHomTriangleRow Y P d.pt).obj r,
                (perfectHomTriangleRowCoconeMap Y P D d).app r⟩) := by sorry

end AlgebraicGeometry
