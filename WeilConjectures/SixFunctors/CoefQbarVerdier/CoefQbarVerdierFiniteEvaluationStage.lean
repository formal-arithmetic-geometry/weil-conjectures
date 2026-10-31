/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence

/-! The normalized finite evaluation square in the named coefficient stage system. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u v w u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem evaluation_scalar_of_eq
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) (F G : C ⥤ D) (h : F = G)
    (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D) (w : C) (z : D)
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, U.obj (K, e.obj (op K)) ⟶ z)
    (t : T ⋙ G ≅ G.prod G ⋙ U) (β : d ⋙ G ≅ G.op ⋙ e) (ω : G.obj w ≅ z)
    (he : ∀ K, U.map (Prod.mkHom (𝟙 (G.obj K)) (β.hom.app (op K))) ≫ ew (G.obj K) =
      t.inv.app (K, d.obj (op K)) ≫ G.map (ev K) ≫ ω.hom) (K : C) :
    U.map (Prod.mkHom (𝟙 (F.obj K))
      ((eqToIso h).hom.app (d.obj (op K)) ≫ β.hom.app (op K) ≫
        e.map ((eqToIso h).hom.app K).op)) ≫ ew (F.obj K) =
    (Functor.isoWhiskerLeft T (eqToIso h) ≪≫ t ≪≫
      Functor.isoWhiskerRight (NatIso.prod (eqToIso h).symm (eqToIso h).symm) U).inv.app
        (K, d.obj (op K)) ≫ F.map (ev K) ≫ (eqToIso h).hom.app w ≫ ω.hom := by
  subst G
  simpa [NatTrans.prod] using he K

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageSystem stageSystem_existsUnique)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedTensor sfRationalScalarExtension rationalTensorScalarComparison
attribute [local implicit_reducible] Stage
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.uniformProd
  GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- The finite evaluation square transported to the named stage-system transition.
Source: blueprint thm-coef-qbar-verdier, the finite-extension evaluation square in step 5.
(blueprint: lem-coef-qbar-finite-evaluation-stage-square).
Proof: the stage transition equals the prescribed rational scalar functor. Transport
its normalized evaluation square along that equality. The dual comparison acquires
the transition equality on the dual object and its contravariant inverse on K;
the tensor comparison acquires the same equality in both factors. Equality induction
reduces this assertion to the original normalized finite evaluation square. Finally
betaNormalized identifies the recorded beta with that square's comparison. The
argument includes identity extensions and does not assume scalar extension faithful. -/
theorem finite_evaluation_scalar_of_stages (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) (K : Stage l Ω X E) :
    let := RationalVerdier.units D l hl X
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L)).map
      (Prod.mkHom (𝟙 (((stageSystem l Ω X).T h).obj K))
        ((operationStageTransitionIso l Ω X E L h).hom.app
            ((F.datum E).dual.obj (op K)) ≫ (F.beta E L h).hom.app (op K) ≫
          (F.datum L).dual.map ((operationStageTransitionIso l Ω X E L h).hom.app K).op)) ≫
        (F.datum L).evaluation (((stageSystem l Ω X).T h).obj K) =
      (rationalTensorStageComparison l Ω X h).inv.app (K, (F.datum E).dual.obj (op K)) ≫
        ((stageSystem l Ω X).T h).map ((F.datum E).evaluation K) ≫
          (operationStageTransitionIso l Ω X E L h).hom.app
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
              (F.omega E).omega) ≫ (F.scalar E L h).omega.hom := by
  let := RationalVerdier.units D l hl X
  have hβ := eq_of_heq (F.betaNormalized E L h)
  have he := evaluation_scalar_of_eq (C := Stage l Ω X E) (D := Stage l Ω X L)
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E))
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L))
    ((stageSystem l Ω X).T h) (GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h)
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h)
    (F.datum E).dual (F.datum L).dual _ _ (F.datum E).evaluation (F.datum L).evaluation
    (rationalTensorScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X)
    (F.scalar E L h).comparison (F.scalar E L h).omega
    (F.normalized E L h).2.2.1 K
  simpa only [Iso.trans_hom, Iso.app, Category.assoc, operationStageTransitionIso,
    rationalTensorStageComparison, hβ] using he

end WeilConjectures.CoefQbarVerdier
