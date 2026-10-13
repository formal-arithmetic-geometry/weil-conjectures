/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# Exterior tensor quotients

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 800000 in
-- Naturality compares exterior restrictions across the ring-sheaf module interfaces.
set_option backward.isDefEq.respectTransparency false in
/-- An epimorphism induces an epimorphism on a tensor of exterior sheaves.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: new-exterior-tensor-quotient).

Proof: Apply the sectionwise exterior-power functor to `g`, and then sheafify. The
sectionwise map takes a pure wedge to the wedge of its images, and commutes with
restrictions by naturality of `g`. Tensor it with the identity of the first exterior
sheaf. This gives the displayed formula. To check epimorphy, suppose two morphisms
have equal composites with this map. Evaluate that equality on tensors of pure wedges
and apply `exteriorTensor_lift_hom_ext g r s`: it proves equality of the morphisms
from their values on these lifted generators. This is the cancellation property
defining an epimorphism. The extensionality theorem handles simultaneous local lifts
and local generation, including degree zero; the empty wedge is preserved. -/
theorem exteriorTensor_quotient_exists {X : Scheme.{v}} (A B C : X.Modules)
    (g : B ⟶ C) [Epi g] (r s : ℕ) :
    ∃ q : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶
        exteriorSheaf A r ⊗ exteriorSheaf C s,
      Epi q ∧ ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        q.val.app (op U)
            (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s)
            (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))) := by
  let p : exteriorSheafPresheaf B s ⟶ exteriorSheafPresheaf C s :=
    { app := fun U ↦ by
        let : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        exact ModuleCat.ofHom (exteriorPower.map s (g.val.app U).hom)
      naturality := by
        intro U V f
        let : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        let : CommRing (X.ringCatSheaf.obj.obj V) :=
          inferInstanceAs (CommRing (X.presheaf.obj V))
        apply ModuleCat.hom_ext
        apply exteriorPower.linearMap_ext (R := X.presheaf.obj U)
        apply AlternatingMap.ext
        intro c
        change exteriorPower.map s (g.val.app V).hom
            (exteriorSheafRestriction B s f (exteriorPower.ιMulti (X.presheaf.obj U) s c)) =
          exteriorSheafRestriction C s f
            (exteriorPower.map s (g.val.app U).hom
              (exteriorPower.ιMulti (X.presheaf.obj U) s c))
        have hm := (Classical.choose_spec
          (exteriorSheafRestriction_existsUnique B s f)).1 c
        have hn := (Classical.choose_spec
          (exteriorSheafRestriction_existsUnique C s f)).1
            (fun i ↦ g.val.app U (c i))
        have hu := exteriorPower.map_apply_ιMulti (R := X.presheaf.obj U) (n := s)
          (g.val.app U).hom c
        have hv := exteriorPower.map_apply_ιMulti (R := X.presheaf.obj V) (n := s)
          (g.val.app V).hom (fun i ↦ B.val.map f (c i))
        have ht : (fun i ↦ g.val.app V (B.val.map f (c i))) =
            (fun i ↦ C.val.map f (g.val.app U (c i))) := by
          funext i
          exact PresheafOfModules.naturality_apply g.val f (c i)
        exact (congrArg (exteriorPower.map (R := X.presheaf.obj V) s
          (g.val.app V).hom) hm).trans (hv.trans
            ((congrArg (exteriorPower.ιMulti (X.presheaf.obj V) s) ht).trans
              (hn.symm.trans (congrArg (exteriorSheafRestriction C s f) hu).symm))) }
  let e : exteriorSheaf B s ⟶ exteriorSheaf C s :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p
  have he (U : X.Opens) (c : Fin s → B.val.obj (op U)) :
      e.val.app (op U) (exteriorSheafSection B s U c) =
        exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i)) := by
    let : CommRing (X.ringCatSheaf.obj.obj (op U)) :=
      inferInstanceAs (CommRing (X.presheaf.obj (op U)))
    let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 X.ringCatSheaf.obj)
    have hn := congrArg (fun k ↦ k.app (op U)
      (exteriorPower.ιMulti (X.presheaf.obj (op U)) s c)) (adj.unit.naturality p).symm
    change e.val.app (op U) (exteriorSheafSection B s U c) =
      (adj.unit.app (exteriorSheafPresheaf C s)).app (op U)
        (exteriorPower.map s (g.val.app (op U)).hom
          (exteriorPower.ιMulti (X.presheaf.obj (op U)) s c)) at hn
    exact hn.trans (congrArg ((adj.unit.app (exteriorSheafPresheaf C s)).app (op U))
      (exteriorPower.map_apply_ιMulti (R := X.presheaf.obj (op U))
        (g.val.app (op U)).hom c))
  let q := (𝟙 (exteriorSheaf A r)) ⊗ₘ e
  have hq (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)) :
      q.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
        tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s)
          (exteriorSheafSection A r U a)
          (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))) := by
    change ((𝟙 (exteriorSheaf A r)) ⊗ₘ e).app U _ = _
    rw [tensorHom_app_tmulSection]
    change tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s)
      (exteriorSheafSection A r U a) (e.val.app (op U) (exteriorSheafSection B s U c)) = _
    rw [he]
  refine ⟨q, ?_, hq⟩
  constructor
  intro D φ ψ hcomp
  apply exteriorTensor_lift_hom_ext g r s
  intro U a c
  rw [← hq U a c]
  exact congrArg (fun k ↦ k.val.app (op U)
    (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c))) hcomp

end AlgebraicGeometry.Scheme.Modules
