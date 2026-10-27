/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Category.AlgCat.TensorAlgebra

/-! # The canonical ring object of a ring sheaf

Source: blueprint main-20261015, det-def-sfb-ring-object-sheaf.
(blueprint: det-def-sfb-ring-object-sheaf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Forgetting a ring sheaf to abelian groups preserves the sheaf condition.
Source: det-def-sfb-ring-object-sheaf, first clause
(blueprint: det-def-sfb-ring-object-sheaf).
Proof: a matching family of underlying sections is exactly a matching family
of ring sections. Glue it uniquely in the ring sheaf. Addition, zero and negation
commute with this gluing by uniqueness, proving the abelian sheaf condition. -/
@[instance] theorem hasSheafCompose_forget₂_ringCat_ab
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w}) := by
  exact hasSheafCompose_of_preservesLimitsOfSize J

/-- The canonical ring structure transported along the sheafification counit,
with its extension, uniqueness, commutativity and ring-map properties.
Source: blueprint main-20261015, det-def-sfb-ring-object-sheaf
(blueprint: det-def-sfb-ring-object-sheaf).
Proof: the ring presheaf has its pointwise monoid structure. Strong monoidal
sheafification transports it to the sheafification. Its counit is invertible
since inclusion of sheaves is fully faithful; transport the monoid structure
along this counit. The triangle identities give the multiplication and unit
extension formulas. The sheafification Hom bijection gives uniqueness of each
extension and hence of the structure. The transported symmetry proves
commutativity when all section rings commute. Naturality of the counit and
functoriality of monoidal sheafification prove the ring-map assertion.
-/
theorem ringObjectOfSheafOfRings {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal] (S : Sheaf J RingCat.{w}) :
    Presheaf.IsSheaf J (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) ∧ IsIso ((sheafificationAdjunction J
    Ab.{w}).counit.app ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)) ∧ (∃! (m : @MonObj
    (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w}) ((sheafCompose J (forget₂ RingCat.{w}
    Ab.{w})).obj S)), m.one = @MonObj.one (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w})
    (Sheaf.sheafifyRingPresheaf J S.obj) (Sheaf.monObj_presheafToSheaf_obj J (S.obj ⋙ forget₂
    RingCat.{w} Ab.{w})) ≫ (Sheaf.sheafifyRingPresheafIso J S).hom ∧ m.mul =
    (Sheaf.monoidalCategory J Ab.{w}).tensorHom (Sheaf.sheafifyRingPresheafIso J S).inv
    (Sheaf.sheafifyRingPresheafIso J S).inv ≫ @MonObj.mul (Sheaf J Ab.{w}) _
    (Sheaf.monoidalCategory J Ab.{w}) (Sheaf.sheafifyRingPresheaf J S.obj)
    (Sheaf.monObj_presheafToSheaf_obj J (S.obj ⋙ forget₂ RingCat.{w} Ab.{w})) ≫
    (Sheaf.sheafifyRingPresheafIso J S).hom ∧ (@Functor.LaxMonoidal.μ (Sheaf J Ab.{w}) _
    (Sheaf.monoidalCategory J Ab.{w}) (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
    (sheafToPresheafLaxMonoidal Ab.{w} J) ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ≫ m.mul.hom = @MonObj.mul (Cᵒᵖ ⥤
    Ab.{w}) _ _ (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂)) ∧ (∀ g :
    (Sheaf.monoidalCategory J Ab.{w}).tensorObj ((sheafCompose J (forget₂ RingCat.{w}
    Ab.{w})).obj S) ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ⟶ ((sheafCompose J
    (forget₂ RingCat.{w} Ab.{w})).obj S), @Functor.LaxMonoidal.μ (Sheaf J Ab.{w}) _
    (Sheaf.monoidalCategory J Ab.{w}) (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
    (sheafToPresheafLaxMonoidal Ab.{w} J) ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S) ≫ g.hom = @MonObj.mul (Cᵒᵖ ⥤ Ab.{w}) _
    _ (S.obj ⋙ forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂) → g = m.mul) ∧
    (@Functor.LaxMonoidal.ε (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w}) (Cᵒᵖ ⥤ Ab.{w})
    _ _ (sheafToPresheaf J Ab.{w}) (sheafToPresheafLaxMonoidal Ab.{w} J) ≫ m.one.hom =
    @MonObj.one (Cᵒᵖ ⥤ Ab.{w}) _ _ (S.obj ⋙ forget₂ RingCat.{w} Ab.{w})
    (S.obj.monObjCompForget₂)) ∧ (∀ g : (Sheaf.monoidalCategory J Ab.{w}).tensorUnit ⟶
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S), @Functor.LaxMonoidal.ε (Sheaf J
    Ab.{w}) _ (Sheaf.monoidalCategory J Ab.{w}) (Cᵒᵖ ⥤ Ab.{w}) _ _ (sheafToPresheaf J Ab.{w})
    (sheafToPresheafLaxMonoidal Ab.{w} J) ≫ g.hom = @MonObj.one (Cᵒᵖ ⥤ Ab.{w}) _ _ (S.obj ⋙
    forget₂ RingCat.{w} Ab.{w}) (S.obj.monObjCompForget₂) → g = m.one) ∧ ((∀ (U : Cᵒᵖ) (a b :
    S.obj.obj U), a * b = b * a) → @IsCommMonObj (Sheaf J Ab.{w}) _ (Sheaf.monoidalCategory J
    Ab.{w}) (Sheaf.braidedCategory J Ab.{w}) ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj
    S) m)) ∧ (∀ {T : Sheaf J RingCat.{w}} (f : S ⟶ T), @IsMonHom (Sheaf J Ab.{w}) _
    (Sheaf.monoidalCategory J Ab.{w}) ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S)
    ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj T) (Sheaf.monObj_sheafCompose_obj J S)
    (Sheaf.monObj_sheafCompose_obj J T) ((sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map f)) := by
  let := Sheaf.monoidalCategory J Ab.{w}
  let A := (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj S
  let m : MonObj A := Sheaf.monObj_sheafCompose_obj J S
  let : MonObj A.obj := S.obj.monObjCompForget₂
  have hmul := Sheaf.μ_comp_map_mul A
  have hone := Sheaf.ε_comp_map_one A
  refine ⟨A.property, inferInstance, ?_, ?_⟩
  · refine ⟨m, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact MonObj.ofIso_one (Sheaf.sheafifyRingPresheafIso J S)
      · exact MonObj.ofIso_mul (Sheaf.sheafifyRingPresheafIso J S)
      · exact hmul
      · intro g hg
        exact Sheaf.tensor_hom_ext (hg.trans hmul.symm)
      · exact hone
      · intro g hg
        exact Sheaf.unit_hom_ext (hg.trans hone.symm)
      · exact Sheaf.isCommMonObj_sheafCompose_obj J S
    · intro n hn
      exact MonObj.ext n m (hn.2.1.trans
        (MonObj.ofIso_mul (Sheaf.sheafifyRingPresheafIso J S)).symm)
  · intro T f
    exact Sheaf.isMonHom_sheafCompose_map J f

end CategoryTheory
