/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetSheafComparison
public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite

/-! # Eventual compatibility of finitely many stage sections

Source: Stacks Project, Sites Tag 0A35; Étale Cohomology Tag 0EYL.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Finitely many affine local sections with a common image at the limit become
compatible at some later stage. No covering hypothesis or covering conclusion is needed.

Source: Stacks Project, Sites Tag 0A35, equation-compute-pullback-to-limit
and its finite-matching argument; Étale Cohomology Tag 0EYL.
(blueprint: lem-weil-pbc-sets-eventual-local-stage-matching-compatibility).

Proof: The base change Y_j of W is affine, since W is affine and the transition
map is affine. For each ordered pair q,q', form P = V_q ×_{Y_j} V_q'. This is
an affine étale object over D(j). Restrict s_q and s_q' to P. Naturality of the
sheaf comparison and the given equations with t show that these two sections
have the same image on the base change of P to the limit.
Restrict the original inverse system to stages above j; its limit is still c.pt.
Apply the affine-site colimit presentation (0EYL), the equivalence between full
and affine étale sheaves, and the section formula of 0A35 to the sheaf H_j and
object P. The two equal limit sections are equal in this filtered colimit, so
they become equal at one later stage. Unit-compatible inverse-image composition
identifies these colimit transition maps with the comparisons in the statement.
There are finitely many pairs. Directedness gives one common later stage for
all their equality witnesses; transporting equalities to it preserves them.
Base change preserves each overlap. Every pair of arrows with equal composites
into Y_j' factors through the base-changed overlap, so restricting its equality
proves Presieve.Arrows.Compatible. The isomorphism d merely changes the target
of the family and cancels in the equal-composite condition. If n = 0, the
compatibility condition is vacuous and the identity refinement suffices. Empty
overlaps cause no exception: a sheaf has a unique section on the empty object.
No section is selected to define an object. -/
theorem etaleSet_eventualLocalStageCompatibility
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).FullAffineEtale)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))) :
    let H := fun j : Over (op i₀) ↦ (Scheme.etaleSetPullback (D.map j.hom)).obj G
    let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let Y := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W.obj
    let e := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app W.obj
    let β := fun j : Over (op i₀) ↦
      etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G
    ∀ (j : Over (op i₀)) (n : ℕ) (V : Fin n → (D.obj j.left).Etale)
      (a : ∀ q, V q ⟶ Y j) (s : ∀ q, (H j).obj.obj (op (V q))),
      (∀ q, IsAffine (V q).left) →
      (∀ q, (β j).hom.app (op (V q)) (s q) =
        L.obj.map ((B j).map (a q) ≫ (e j).inv).op t) →
    ∃ (j' : Over (op i₀)) (r : j' ⟶ j),
      let b := MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)
      let hr := (D.map_comp r.left j.hom).symm.trans
        (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
      let d := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (D.map r.left) (D.map j.hom) (D.map j'.hom) hr.symm).app W.obj
      let V' := fun q ↦ b.obj (V q)
      let a' := fun q ↦ b.map (a q) ≫ d.inv
      let s' := fun q ↦ (etaleSetSheafComparison (D.map r.left) (D.map j.hom)
        (D.map j'.hom) hr G).hom.app (op (V q)) (s q)
      Presieve.Arrows.Compatible (H j').obj a' s' := by sorry

end AlgebraicGeometry
