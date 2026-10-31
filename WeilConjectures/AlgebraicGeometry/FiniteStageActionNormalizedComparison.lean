/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! The normalized natural comparison at one raw rational coefficient stage. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient)
open ConstructibleExceptionalCoefficients

private def iso_cast
    {A B : Type*} [Category A] [Category B]
    {F F' H : A ⥤ B} (h : F = F') (e : F' ≅ H) : F ≅ H :=
  h.symm ▸ e

private def stageIso
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (E : Index l Ω)
    (F H : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (h : HEq (S.Φ E) F) (e : F ≅ H) :
    GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E ⋙ S.functor ≅
      H ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E := by
  let H' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E := H
  let e' : S.Φ E ≅ H' := by
    have hh := h
    dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
      GeneralAlgebraicallyClosedCoefficients.stageCategory] at hh ⊢
    exact iso_cast (eq_of_heq hh) e
  exact S.ιCompFunctorIso E ≪≫ Functor.isoWhiskerRight e'
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι E)

private theorem map_iso_cast_heq
    {C D' T : Type*} [Category C] [Category D'] [Category T]
    {F F' H : C ⥤ D'} (h : F = F') (e : F' ≅ H) (J : D' ⥤ T) (A : C) :
    HEq (J.map ((iso_cast h e).hom.app A)) (J.map (e.hom.app A)) := by
  subst F'
  rfl

private theorem stageIso_map_heq
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (E : Index l Ω)
    (F H : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (h : HEq (S.Φ E) F) (e : F ≅ H)
    {T : Type*} [Category T]
    (J : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y ⥤ T)
    (A : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) :
    HEq (J.map ((stageIso l Ω X Y S E F H h e).hom.app A))
      (J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E).map
        (e.hom.app A))) := by
  have hh := h
  dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory] at hh
  change HEq (J.map (𝟙 _ ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E).map
      ((iso_cast (eq_of_heq hh) e).hom.app A))) _
  rw [Category.id_comp]
  exact map_iso_cast_heq (eq_of_heq hh) e
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E ⋙ J) A

/-- Match a descended stage action with its specified rational operation.
Source: the common-stage construction of Bhatt--Scholze, Proposition 6.8.14,
and the finite-stage normalization in Remark 6.8.15.
Proof: the stage-system inclusion commutes with descent by an identity-component
natural isomorphism. Transport the given rational comparison along the equality
of its left functor with the stage action, and include it in the pair category.
Equality transport preserves the heterogeneous component formula; applying J
preserves that formula as well. This construction works for every stage and object.
(blueprint: lem-sf-finite-stage-action-normalized-comparison). -/
theorem finiteStageAction_normalizedComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [IsAlgClosure (Padic l) (ULift.{u} Ω)]
    (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (O : ∀ E : Index l Ω, Operation l (ULift.{u} Ω) X Y
      (.rational ({ carrier := Coefficient.{u} l Ω E } : FieldStage.{u} l)))
    (H : ∀ E : Index l Ω, sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (e : ∀ E, (O E).F ≅ H E)
    (hf : ∀ E, HEq (S.Φ E) (O E).F) (E : Index l Ω)
    {T : Type*} [Category T]
    (J : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y ⥤ T) :
    ∃ q : GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E ⋙ S.functor ≅
        H E ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E,
      ∀ A : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
        ∃ (B B' : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
          (r : B ⟶ B'), HEq r ((e E).hom.app A) ∧
          HEq (J.map (q.hom.app A))
            (J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E).map r)) := by
  have hh := hf E
  let ee := e E
  dsimp only [C, category] at hh ee ⊢
  refine ⟨stageIso l Ω X Y S E (O E).F (H E) hh ee, fun A ↦ ?_⟩
  refine ⟨(O E).F.obj A, (H E).obj A, ee.hom.app A, HEq.rfl, ?_⟩
  exact stageIso_map_heq l Ω X Y S E (O E).F (H E) hh ee J A

end WeilConjectures.LocallyFiniteAdicCompactSupport
