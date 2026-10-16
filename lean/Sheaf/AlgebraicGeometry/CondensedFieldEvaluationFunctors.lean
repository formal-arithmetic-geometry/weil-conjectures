/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Evaluation of condensed-field modules over one geometric point

Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Continuous coefficient of a regular endomorphism at a geometric point. -/
@[irreducible] noncomputable def condensedFieldPointCoefficient
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (f : Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω)))) : E :=
  ((((condensedFieldContinuousMapIso E (Spec (.of Ω))).inv.hom ≫ f.hom ≫
    (condensedFieldContinuousMapIso E (Spec (.of Ω))).hom.hom).hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))) (ULift.up 1)).down z

/-- The regular-module normalization of evaluation over a geometric point. -/
def CondensedFieldPointScalarProperty
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⥤
      ModuleCat.{u + 1} E) : Prop :=
  ∃ b : H.obj (Mod.regular
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω)))) ≃ₗ[E] E,
    ∀ f : Mod.regular
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⟶
        Mod.regular
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))),
      b (H.map f (b.symm 1)) =
        condensedFieldPointCoefficient E Ω z f

/-- Evaluation at the final object over one algebraically closed field.

Source: Bhatt--Scholze, Example 4.2.11; Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-field-evaluation-functors).

Proof in words. Apply final-object sections to the underlying abelian sheaf and its
internal action. Sections is lax monoidal: its tensorator sends a pair of sections to
its tensor section, so its image is an internal module over the ring of global sections.
The canonical continuous realization identifies this ring with ULift E: every continuous
function on the one-point spectrum is constant, and evaluation at z is its inverse.
Transport the action along this ring isomorphism and use the tensor universal property
for internal modules in abelian groups to obtain an ordinary E-module. The internal
linearity diagrams make all evaluated arrows E-linear; they are unchanged as additive
maps, hence this functor is additive. Over an algebraically closed field every covering
of the final object splits. Consequently abelian sections preserves finite colimits.
The forgetful functor from internal modules computes those colimits, and the ordinary
module forgetful functor reflects them; hence evaluation preserves finite colimits.
The regular module gives E with its usual action. Evaluate its endomorphism at 1 to
get the displayed normalization, since both coefficient identifications are the
specified continuous realization followed by evaluation at z. -/
theorem exists_condensedField_point_evaluation
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω)) :
    ∃ H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) (Spec (.of Ω))) ⥤
        ModuleCat.{u + 1} E,
      H.Additive ∧ PreservesFiniteColimits H ∧ CondensedFieldPointScalarProperty E Ω z H := by
  sorry

/-- The continuous coefficient ring is commutative, sectionwise. -/
instance continuousCoefficientRingObj_isComm
    (E : Type u) [NormedField E] :
    IsCommMonObj (Profinite.continuousCoefficientRingObj E) :=
  Sheaf.isCommMonObj_sheafCompose_obj
    (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E)
    (by
      intro S a b
      apply ULift.ext
      change (a.down * b.down : C(S.unop, E)) = b.down * a.down
      exact mul_comm a.down b.down)

/-- Pull a module to a geometric point after canonical coefficient change. -/
@[irreducible] noncomputable def condensedFieldGeometricModulePullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
      ((upperStar AddCommGrpCat.{u + 1} p).obj (condensedRingObj Λ X)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T) :=
  Mod.comap (inv (condensedPullbackHom Λ p)) ⋙ CondensedRing.upperStar Λ a

instance condensedFieldGeometricModulePullback_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    (condensedFieldGeometricModulePullback Λ p a).Additive := by
  unfold condensedFieldGeometricModulePullback
  infer_instance

instance condensedFieldGeometricModulePullback_preservesFiniteColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    PreservesFiniteColimits (condensedFieldGeometricModulePullback Λ p a) := by
  unfold condensedFieldGeometricModulePullback
  infer_instance

/-- Pulling back from X and then to T agrees with pullback along the composite. -/
noncomputable def condensedFieldGeometricModulePullbackComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    (upperStar AddCommGrpCat.{u + 1} p).mapMod (condensedRingObj Λ X) ⋙
        condensedFieldGeometricModulePullback Λ p a ≅
      CondensedRing.upperStar Λ (a ≫ p) := by
  unfold condensedFieldGeometricModulePullback
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((upperStar AddCommGrpCat.{u + 1} p).mapMod (condensedRingObj Λ X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ p)).symm)
      (CondensedRing.upperStar Λ a) ≪≫
    (CondensedRing.upperStarComp Λ a p).symm

/-- The geometric module pullback carries the regular module to the regular module.
Its first factor is the canonical coefficient comparison; the second factor is the
regular-module comparison for coefficient module inverse image. -/
@[irreducible] noncomputable def condensedFieldGeometricRegularIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X V T : Scheme.{u}} (p : V ⟶ X) (a : T ⟶ V) :
    (condensedFieldGeometricModulePullback Λ p a).obj
        (Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj (condensedRingObj Λ X))) ≅
      Mod.regular (condensedRingObj Λ T) := by
  unfold condensedFieldGeometricModulePullback
  exact (CondensedRing.upperStar Λ a).mapIso
      (Mod.regularIsoOfIsIso (condensedPullbackHom Λ p)) ≪≫
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ a)).app
      (((upperStar AddCommGrpCat.{u + 1} a).mapMod (condensedRingObj Λ V)).obj
        (Mod.regular (condensedRingObj Λ V))) ≪≫
    Mod.regularIsoOfIsIso (condensedPullbackHom Λ a)

end AlgebraicGeometry.ProEtale
