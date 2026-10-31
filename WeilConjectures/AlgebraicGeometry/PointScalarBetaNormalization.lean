/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructiblePointComparisonData
public import WeilConjectures.AlgebraicGeometry.PointRealizationStandardCohomology

/-! # Normalization of the finite point scalar component

Source: the point coefficient convention, blueprint order 1509
(blueprint: lem-a1-point-scalar-beta-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC vC uB vB uD vD uA vA
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem full_subcategory_scalar_beta
    {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
    {D : Type uD} [Category.{vD} D] {A : Type uA} [Category.{vA} A]
    (P : ObjectProperty D) (Q : ObjectProperty A)
    (F : C ⥤ P.FullSubcategory) (G : B ⥤ Q.FullSubcategory) (T : D ⥤ A)
    (h : ∀ K, Q ((P.ι ⋙ T).obj K)) (S S' : C ⥤ B)
    (α : S ⋙ G ≅ F ⋙ Q.lift (P.ι ⋙ T) h) (γ : S' ≅ S) :
    Functor.associator F P.ι T ≪≫
        Functor.isoWhiskerLeft F (Q.liftCompιIso (P.ι ⋙ T) h).symm ≪≫
        (Functor.associator F (Q.lift (P.ι ⋙ T) h) Q.ι).symm ≪≫
        Functor.isoWhiskerRight α.symm Q.ι ≪≫
        Functor.associator S G Q.ι ≪≫ Functor.isoWhiskerRight γ.symm (G ⋙ Q.ι) =
      ((Functor.associator S G Q.ι).symm ≪≫
        Functor.isoWhiskerRight α Q.ι ≪≫
        Functor.associator F (Q.lift (P.ι ⋙ T) h) Q.ι).symm ≪≫
        Functor.isoWhiskerRight γ.symm (G ⋙ Q.ι) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp [ObjectProperty.liftCompιIso]

attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

/-- The full-subcategory inclusions in the given finite beta are identity components;
thus it is exactly the inverse point scalar map followed by the transition map.
Source: point coefficient convention, blueprint order 1509
(blueprint: lem-a1-point-scalar-beta-normalization).
Proof: evaluate the associators and the full-subcategory lift comparison at an object.
Their components are identities; cancel them on both sides of the specified scalar map. -/
theorem pointFiniteScalarBeta_normalization (E L : Index l Ω) (a : E ≤ L) :
    constructiblePointFiniteScalarBeta D l hl Ω E L a =
      (pointRealizationScalarIso D l hl (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a)).symm ≪≫
      Functor.isoWhiskerRight (operationStageTransitionIso l Ω (Spec (.of D.k)) E L a).symm
        (pointRealizationAmbient D l hl (Coefficient.{u} l Ω L)) := by
  exact full_subcategory_scalar_beta _ _ _ _ _ _ _ _
    (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a))
    (operationStageTransitionIso l Ω (Spec (.of D.k)) E L a)

end WeilConjectures
