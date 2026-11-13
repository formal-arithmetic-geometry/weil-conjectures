/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationTransportSummandProjection
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverComponentIdentity
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationComponent

/-! # Evaluation components with a fixed normalized tensor comparison

## References

* Stacks Project, Tag 0A8X, ordinary tensor totalization.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] ordinaryComponentIdentityOverPreadditive

attribute [local instance] ordinaryComponentIdentitySchemePreadditive

attribute [local irreducible] homComplexFunctor Scheme.Modules.overEquiv
  schemeOrdinaryEvaluationComponent
  Scheme.Modules.overEquivFunctorObjUnitIso HomologicalComplex.singleMapHomologicalComplex

private theorem ordinaryTransport_congrMiddle
    {C : Type*} [Category C] {A B D E G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : E ⟶ G) {f g : D ⟶ E} (h : f = g) :
    a ≫ b ≫ f ≫ c = a ≫ b ≫ g ≫ c := by
  subst g
  rfl

-- These two forall hypotheses are used after `intro` in the proof below.
set_option linter.unusedVariables false in
/-- A fixed normalized tensor comparison transports all ordinary evaluation components
(Stacks, Tags 0A8X, 08DQ and 08DL). -/
theorem ordinaryEvaluation_component_over_transport (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∀ (e : ∀ A B : localEvaluationModules X U,
      L.obj
          (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf)
          (L.obj A)
          (L.obj B))
    (he : ∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map
          (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫
          (e A' B').hom =
        (e A B).hom ≫ SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          (L.map f)
          (L.map g))
    (b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
      T.obj
          (homComplex (R := X.sheaf.over U) P M) ≅
        homComplex (R := U.toScheme.sheaf)
          (T.obj P)
          (T.obj M))
    (hπ : ∀ (M : CochainComplex (localEvaluationModules X U) ℤ)
          (n r s : ℤ) (h : r + n = s),
        (b M).hom.f n ≫
            (Classical.choose (homComplex_projections_exists (R := U.toScheme.sheaf)))
              (T.obj P)
              (T.obj M)
              n r s h =
          L.map
            (localEvaluationProjection X U P M n r s h) ≫
            (e (P.X r) (M.X s)).hom),
    let a : T.obj (localEvaluationUnit X U) ≅
        (HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) :=
      (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso
          (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
    let d := b (localEvaluationUnit X U) ≪≫
      ((homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))).mapIso a
    ∀ (m : L.CoreMonoidal)
      (_hunit : m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U)
      (_hsymm : ∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom)
      (F : CochainComplex (localEvaluationModules X U) ℤ)
      (c : T.obj (localEvaluationTensor X U P F) ≅
        pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)))
      (_hc : ∀ (p q n : ℤ) (h : p + q = n),
        L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
            (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
          (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
            HomologicalComplex.ιMapBifunctor (T.obj F) (T.obj (localEvaluationDual X U P))
              (curriedTensor _) (.up ℤ) p q n h)
      (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F),
      IsLocalOrdinaryEvaluation X U P F f →
        IsSchemeOrdinaryEvaluation U.toScheme (T.obj P) (T.obj F)
          ((c ≪≫ (((curriedTensor (SheafOfModules.{u}
            (moduleRings U.toScheme.toRingedSpace))).map₂CochainComplex).obj
              (T.obj F)).mapIso d).inv ≫ T.map f ≫ (b F).hom) := by
  set_option backward.isDefEq.respectTransparency.types true in
  set_option backward.isDefEq.respectTransparency true in
    intro L T e he b hπ a d m hunit hsymm F c hc f hf
    apply schemeOrdinaryEvaluation_of_components
    intro O D π p q n r hpq
    have ht := ordinaryEvaluation_transport_summand_projection X U P e b hπ
      d m F c hc f p q n r hpq
    have hv := ordinaryEvaluation_over_component_identity X U P e he b hπ
      m hunit hsymm F p q n r hpq
    have hl := congrArg (fun k =>
      (Scheme.Modules.overEquiv U).functor.map k) (hf p q n r hpq)
    have htotal := ht.trans
      ((ordinaryTransport_congrMiddle _ _ _ hl).trans hv)
    exact htotal

end AlgebraicGeometry
