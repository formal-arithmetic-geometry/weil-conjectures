/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.Topology.InverseImageModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

import Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
import Mathlib.CategoryTheory.Limits.Final.Type
import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-! # Extension of the inverse image of a regular module

Source: Stacks Project, Sheaves on Spaces, Tags 008X, 008Y and 008A.
(blueprint: stage3-inverse-image-regular-extension).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings
namespace SheafOfModules
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝓡" S =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S

private def isoOfHomEquiv {C : Type*} [Category C] (M N : C)
    (e : ∀ P, (M ⟶ P) ≃ (N ⟶ P))
    (he : ∀ P Q (a : M ⟶ P) (b : P ⟶ Q), e Q (a ≫ b) = e P a ≫ b) : M ≅ N where
  hom := (e N).symm (𝟙 N)
  inv := e M (𝟙 M)
  hom_inv_id := by
    apply (e M).injective
    rw [he, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := he M N (𝟙 M) ((e N).symm (𝟙 N))
    simpa using h.symm

set_option maxHeartbeats 800000 in
-- The hom equivalences unfold dependent section modules and both scalar restrictions.
/-- Extending the inverse image of the regular module gives the regular target module,
with the canonical unit normalization.
Source: Stacks Project, Sheaves on Spaces, Tags 008X, 008Y and 008A.
(blueprint: stage3-inverse-image-regular-extension).

Proof: Compose the change-of-rings hom equivalence with the inverse-image
module hom equivalence. Maps from the regular source module correspond to
compatible global sections. Precomposition by the inverse-image map on opens
is a bijection on compatible sections, since that functor is final. Thus maps
from the extended inverse-image regular module to any B-module correspond,
naturally in that module, to maps from the regular B-module. The elementary
representable-functor argument constructs inverse module maps. For their unit
normalization, the two adjunction section formulas identify the adjunct of
the forward isomorphism on a with its value on the sheafification of 1 tensor
the abelian inverse-image unit of a. The hom equivalence sends that isomorphism
to the identity of the regular B-module, so its adjunct sends 1 to 1.
Linearity then sends a = a • 1 to t(η_A(a)) • 1 = t(η_A(a)). This applies also
to zero rings and empty opens, since neither the section equivalence nor the
identity and linearity calculations use nontriviality or nonemptiness. -/
theorem inverseImageRegularExtension
    {T T' : TopCat.{u}} (g : T ⟶ T') (A : T'.Sheaf CommRingCat.{u})
    (B : T.Sheaf CommRingCat.{u}) (t : TopCat.Sheaf.inverseImageRing g A ⟶ B) :
    ∃ e : changeOfRings.{u, u, u} t
        (TopCat.Sheaf.inverseImageModule g A (unit (𝓡 A))) ≅ unit (𝓡 B),
      ∀ (V : (Opens T')ᵒᵖ) (a : A.obj.obj V),
        e.hom.val.app ((Opens.map g).op.obj V)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
            (changeOfRingsPresheaf.{u, u, u} t
              (TopCat.Sheaf.inverseImageModule g A (unit (𝓡 A))))).app
                ((Opens.map g).op.obj V)
                ((1 : B.obj.obj ((Opens.map g).op.obj V)) ⊗ₜ[
                  (TopCat.Sheaf.inverseImageRing g A).obj.obj ((Opens.map g).op.obj V),
                  (t.hom.app ((Opens.map g).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map g) AddCommGrpCat.{u} (Opens.grothendieckTopology T')
                    (Opens.grothendieckTopology T)).unit.app
                      ((toSheaf (𝓡 A)).obj (unit (𝓡 A)))).hom.app V a))) =
          (t.hom.app ((Opens.map g).op.obj V)).hom
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map g) CommRingCat.{u} (Opens.grothendieckTopology T')
              (Opens.grothendieckTopology T)).unit.app A).hom.app V a) := by
  classical
  let C := TopCat.Sheaf.inverseImageRing g A
  let η : (𝓡 A) ⟶ ((Opens.map g).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology T') (Opens.grothendieckTopology T)).obj (𝓡 C) :=
    (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g) CommRingCat.{u} (Opens.grothendieckTopology T')
        (Opens.grothendieckTopology T)).unit.app A)
  let Q := pushforward.{u} (F := Opens.map g) η
  let L := restrictScalars ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map t)
  let M := unit (𝓡 A)
  let I := TopCat.Sheaf.inverseImageModule g A M
  let F := changeOfRings.{u, u, u} t I
  obtain ⟨E, hE, adj, hadj⟩ := exists_changeOfRingsAdjunction T C B t
  obtain ⟨φ, hφ, _, _⟩ := moduleInverseImageAdjunction g A
  let se (N : SheafOfModules.{u} (𝓡 B)) : N.sections ≃ (Q.obj (L.obj N)).sections :=
    Equiv.ofBijective ((Opens.map g).op.sectionsPrecomp)
      (Functor.bijective_sectionsPrecomp (Opens.map g).op
        (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}))
  let q (N : SheafOfModules.{u} (𝓡 B)) : (F ⟶ N) ≃ (M ⟶ Q.obj (L.obj N)) :=
    (Iso.homCongr (eqToIso (hE I)).symm (Iso.refl N)).trans
      ((adj.homEquiv I N).trans (φ M (L.obj N)))
  have hq (N : SheafOfModules.{u} (𝓡 B)) (a : F ⟶ N)
      (V : (Opens T')ᵒᵖ) (x : A.obj.obj V) :
      (q N a).val.app V x = a.val.app ((Opens.map g).op.obj V)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} t I)).app ((Opens.map g).op.obj V)
            ((1 : B.obj.obj ((Opens.map g).op.obj V)) ⊗ₜ[
              C.obj.obj ((Opens.map g).op.obj V),
              (t.hom.app ((Opens.map g).op.obj V)).hom]
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (Opens.map g) AddCommGrpCat.{u} (Opens.grothendieckTopology T')
                (Opens.grothendieckTopology T)).unit.app
                  ((toSheaf (𝓡 A)).obj M)).hom.app V x))) := by
    dsimp only [q, Equiv.trans_apply]
    rw [hφ]
    exact hadj I N a _ _
  have hnq (N N' : SheafOfModules.{u} (𝓡 B)) (a : F ⟶ N) (b : N ⟶ N') :
      q N' (a ≫ b) = q N a ≫ Q.map (L.map b) := by
    ext V
    change (q N' (a ≫ b)).val.app V (1 : A.obj.obj V) =
      b.val.app ((Opens.map g).op.obj V) ((q N a).val.app V (1 : A.obj.obj V))
    rw [hq, hq]
    rfl
  let eqv (N : SheafOfModules.{u} (𝓡 B)) : (F ⟶ N) ≃ (unit (𝓡 B) ⟶ N) :=
    (q N).trans ((Q.obj (L.obj N)).unitHomEquiv.trans
      ((se N).symm.trans N.unitHomEquiv.symm))
  have heqv (N : SheafOfModules.{u} (𝓡 B)) (a : F ⟶ N) :
      se N (N.unitHomEquiv (eqv N a)) =
        (Q.obj (L.obj N)).unitHomEquiv (q N a) := by
    exact (congrArg (se N) (N.unitHomEquiv.apply_symm_apply
      ((se N).symm ((Q.obj (L.obj N)).unitHomEquiv (q N a))))).trans
        ((se N).apply_symm_apply _)
  have hn (N N' : SheafOfModules.{u} (𝓡 B)) (a : F ⟶ N) (b : N ⟶ N') :
      eqv N' (a ≫ b) = eqv N a ≫ b := by
    apply N'.unitHomEquiv.injective
    apply (se N').injective
    rw [heqv, unitHomEquiv_comp_apply, hnq, unitHomEquiv_comp_apply]
    have hs := heqv N a
    apply PresheafOfModules.sections_ext
    intro V
    exact congrArg (fun z ↦ b.val.app ((Opens.map g).op.obj V) (z.val V)) hs.symm
  let e := isoOfHomEquiv F (unit (𝓡 B)) eqv hn
  refine ⟨e, ?_⟩
  intro V a
  have h := (eqv (unit (𝓡 B))).apply_symm_apply (𝟙 (unit (𝓡 B)))
  change eqv (unit (𝓡 B)) e.hom = 𝟙 _ at h
  have hs := congrArg
    (fun z ↦ se (unit (𝓡 B)) ((unit (𝓡 B)).unitHomEquiv z)) h
  dsimp only [eqv, Equiv.trans_apply] at hs
  erw [(unit (𝓡 B)).unitHomEquiv.apply_symm_apply,
    (se (unit (𝓡 B))).apply_symm_apply] at hs
  have hv := congrArg (fun z ↦ z.val V) hs
  change (q (unit (𝓡 B)) e.hom).val.app V (1 : A.obj.obj V) =
    (1 : B.obj.obj ((Opens.map g).op.obj V)) at hv
  rw [← hq]
  rw [show a = a • (1 : A.obj.obj V) by exact (mul_one a).symm]
  rw [(q (unit (𝓡 B)) e.hom).val.app V |>.hom.map_smul, hv]
  change (t.hom.app ((Opens.map g).op.obj V)).hom
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g) CommRingCat.{u} (Opens.grothendieckTopology T')
      (Opens.grothendieckTopology T)).unit.app A).hom.app V a) * 1 = _
  rw [mul_one]
  simp only [smul_eq_mul, mul_one]


end
end SheafOfModules
