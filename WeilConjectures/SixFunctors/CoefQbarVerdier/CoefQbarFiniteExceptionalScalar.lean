/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarFiniteExceptionalCore
public import WeilConjectures.SixFunctors.RationalOperations.RationalDualFormulaAdjunction
import WeilConjectures.SixFunctors.RationalOperations.RationalDualFormulaScalarCounit
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarDualFormulaInclusionScalar

/-! Scalar compatibility for finite exceptional comparison data.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

private theorem scalar_paste
    {C₀ C₁ B : Type*} [Category C₀] [Category C₁] [Category B]
    {T : C₀ ⥤ C₁} {I₀ : C₀ ⥤ B} {I₁ : C₁ ⥤ B} (a : T ⋙ I₁ ≅ I₀)
    {A₀ D₀ : C₀} {A₁ D₁ : C₁} {Z₀ Z₁ : B}
    {p₀ : A₀ ⟶ D₀} {p₁ : A₁ ⟶ D₁}
    {b : T.obj A₀ ⟶ A₁} {d : T.obj D₀ ⟶ D₁}
    {r₀ : I₀.obj D₀ ⟶ Z₀} {r₁ : I₁.obj D₁ ⟶ Z₁}
    {q₀ : I₀.obj A₀ ⟶ Z₀} {q₁ : I₁.obj A₁ ⟶ Z₁} {z : Z₀ ⟶ Z₁}
    (n₀ : I₀.map p₀ ≫ r₀ = q₀) (n₁ : I₁.map p₁ ≫ r₁ = q₁)
    (hs : T.map p₀ ≫ d = b ≫ p₁)
    (hd : I₁.map d ≫ r₁ = a.hom.app D₀ ≫ r₀ ≫ z) :
    I₁.map b ≫ q₁ = a.hom.app A₀ ≫ q₀ ≫ z := by
  rw [← n₀, ← n₁, ← I₁.map_comp_assoc, ← hs, I₁.map_comp, Category.assoc, hd]
  have hn := a.hom.naturality p₀
  change I₁.map (T.map p₀) ≫ a.hom.app D₀ = a.hom.app A₀ ≫ I₀.map p₀ at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]

private theorem comparison_scalar
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L₁ : C ⥤ D} {R₁ V₁ : D ⥤ C} {L₂ : E ⥤ H} {R₂ V₂ : H ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (v₁ : L₁ ⊣ V₁) (v₂ : L₂ ⊣ V₂)
    (e₁ : R₁ ≅ V₁) (e₂ : R₂ ≅ V₂)
    (he₁ : ∀ M, L₁.map (e₁.hom.app M) ≫ v₁.counit.app M = a₁.counit.app M)
    (he₂ : ∀ M, L₂.map (e₂.hom.app M) ≫ v₂.counit.app M = a₂.counit.app M)
    (TX : C ⥤ E) (TY : D ⥤ H) (alpha : L₁ ⋙ TY ≅ TX ⋙ L₂)
    (beta : R₁ ⋙ TX ⟶ TY ⋙ R₂)
    (hbeta : ∀ M, L₂.map (beta.app M) ≫ a₂.counit.app (TY.obj M) =
      alpha.inv.app (R₁.obj M) ≫ TY.map (a₁.counit.app M))
    (M : D) (delta : TX.obj (V₁.obj M) ⟶ V₂.obj (TY.obj M))
    (hdelta : L₂.map delta ≫ v₂.counit.app (TY.obj M) =
      alpha.inv.app (V₁.obj M) ≫ TY.map (v₁.counit.app M)) :
    TX.map (e₁.hom.app M) ≫ delta = beta.app M ≫ e₂.hom.app (TY.obj M) := by
  apply (v₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hdelta, he₂]
  rw [← Category.assoc]
  have h := alpha.inv.naturality (e₁.hom.app M)
  change L₂.map (TX.map _) ≫ alpha.inv.app _ =
    alpha.inv.app _ ≫ TY.map (L₁.map _) at h
  rw [h, Category.assoc, ← TY.map_comp, he₁, hbeta]

private theorem transported_scalar_counit
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L₁ P₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ P₂ : E ⥤ H} {R₂ : H ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ P₁) (e₂ : L₂ ≅ P₂)
    (TX : C ⥤ E) (TY : D ⥤ H) (alpha : L₁ ⋙ TY ≅ TX ⋙ L₂)
    (beta : R₁ ⋙ TX ⟶ TY ⋙ R₂)
    (hbeta : ∀ M, alpha.hom.app (R₁.obj M) ≫ L₂.map (beta.app M) ≫
      a₂.counit.app (TY.obj M) = TY.map (a₁.counit.app M)) (M : D) :
    P₂.map (beta.app M) ≫ (a₂.ofNatIsoLeft e₂).counit.app (TY.obj M) =
      (Functor.isoWhiskerRight e₁.symm TY ≪≫ alpha ≪≫
        Functor.isoWhiskerLeft TX e₂).inv.app (R₁.obj M) ≫
          TY.map ((a₁.ofNatIsoLeft e₁).counit.app M) := by
  have hb : L₂.map (beta.app M) ≫ a₂.counit.app (TY.obj M) =
      alpha.inv.app (R₁.obj M) ≫ TY.map (a₁.counit.app M) := by
    rw [← hbeta M]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  have he := e₂.inv.naturality (beta.app M)
  change P₂.map (beta.app M) ≫ e₂.inv.app (R₂.obj (TY.obj M)) =
    e₂.inv.app (TX.obj (R₁.obj M)) ≫ L₂.map (beta.app M) at he
  rw [← Category.assoc, he, Category.assoc, hb]
  simp only [← TY.map_comp, Iso.hom_inv_id_app_assoc]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

private theorem finite_comparison_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (t : FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S)
    (ht : ∀ E : Index l Ω,
      RationalOperations.DualFormulaAdjunctionNormalized D l hl X c (fieldStage l Ω E)
        (BX.finite.omega E) (BY.finite.omega E) (BX.finite.datum E) (BY.finite.datum E)
        (t.finite E).adjunction)
    (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E) :
    let I : RationalOperations.Identification l X D hl (AuxiliaryClosure.{u} l) c S
        (fieldStage l Ω E) :=
      ⟨BX.finite.omega E, BY.finite.omega E, BX.finite.datum E, BY.finite.datum E,
        BX.finite.hom E, BY.finite.hom E, t.finite E⟩
    let J : RationalOperations.Identification l X D hl (AuxiliaryClosure.{u} l) c S
        (fieldStage l Ω L) :=
      ⟨BX.finite.omega L, BY.finite.omega L, BX.finite.datum L, BY.finite.datum L,
        BX.finite.hom L, BY.finite.hom L, t.finite L⟩
    (RationalVerdier.scalar l X (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)).map
          ((t.finite E).comparison.hom.app M) ≫
      RationalOperations.dualScalar l X D hl (AuxiliaryClosure.{u} l) c S
        (fieldStage l Ω E) (fieldStage l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) I J
        (BX.finite.scalar E L h) (BY.finite.scalar E L h) M =
    (finiteRightScalar D l hl Ω X f c S E L h).hom.app M ≫
      (t.finite L).comparison.hom.app ((transition l Ω Y E L h).obj M) := by
  dsimp only
  let F := fieldStage l Ω E
  let G := fieldStage l Ω L
  let i := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h
  let field := S.fields.rationalComparison c F G i
  let := field.shiftX
  let := field.shiftY
  let TX := RationalVerdier.scalar l X F.carrier G.carrier i
  let TY := RationalVerdier.scalar l Y F.carrier G.carrier i
  let aF := (S.ring.operation c (.rational F)).adjunction.ofNatIsoLeft
    (S.ring.rationalLeft c F)
  let aG := (S.ring.operation c (.rational G)).adjunction.ofNatIsoLeft
    (S.ring.rationalLeft c G)
  apply comparison_scalar aF aG (t.finite E).adjunction (t.finite L).adjunction
    (t.finite E).comparison (t.finite L).comparison
  · intro N
    dsimp only [F]
    rw [(t.finite E).counit]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  · intro N
    dsimp only [G]
    rw [(t.finite L).counit]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  · exact fun N ↦ transported_scalar_counit
      (S.ring.operation c (.rational F)).adjunction
      (S.ring.operation c (.rational G)).adjunction
      (S.ring.rationalLeft c F) (S.ring.rationalLeft c G) TX TY field.q field.b.hom
      field.comparison.counit N
  · exact RationalOperations.rationalDualFormulaScalarCounit D l hl X
      (AuxiliaryClosure.{u} l) c S F G i
      (BX.finite.omega E) (BY.finite.omega E) (BX.finite.omega L) (BY.finite.omega L)
      (BX.finite.datum E) (BY.finite.datum E) (BX.finite.datum L) (BY.finite.datum L)
      (t.finite E).adjunction (t.finite L).adjunction (ht E) (ht L)
      (BX.finite.scalar E L h) (BY.finite.scalar E L h)
      (BX.finite.normalized E L h) (BY.finite.normalized E L h) M

/-- Scalar compatibility for normalized finite exceptional comparisons.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-scalar)

The hypothesis ht pins each finite adjunction to the trace-normalized dual-formula
adjunction; without it the finite comparisons could be rescaled independently at each field.

Proof: for the supplied trace-normalized adjunctions, rationalDualFormulaScalarCounit gives
the counit square of the dual formula. Transport the system's scalar counit identity along
rationalLeft. Transposing under the target adjunction, the source and target counit
equations of the finite identifications show that scalar extension of the finite comparison
followed by dualScalar equals finiteRightScalar followed by the target comparison. Expand
t.normalized at E and L; map this finite square through inclusion at L, apply
dual_formula_inclusion_scalar to the duality-pullback-duality factors, and use naturality of
inclusionTransition on X. Identity extensions and zero objects need no separate case. -/
theorem finite_exceptional_formula_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (t : FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S)
    (ht : ∀ E : Index l Ω,
      RationalOperations.DualFormulaAdjunctionNormalized D l hl X c (fieldStage l Ω E)
        (BX.finite.omega E) (BY.finite.omega E) (BX.finite.datum E) (BY.finite.datum E)
        (t.finite E).adjunction) :
    ∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
      (inclusion L).map ((finiteRightScalar D l hl Ω X f c S E L h).hom.app M) ≫
        (t.comparison L).hom.app ((transition l Ω Y E L h).obj M) =
      (inclusionTransition l Ω X E L h).hom.app
          ((finiteRight D l hl Ω X f c S E).obj M) ≫
        (t.comparison E).hom.app M ≫
        (specifiedExceptionalFormulaCore D l hl Ω X f BX BY).map
          ((inclusionTransition l Ω Y E L h).inv.app M) := by
  intro E L h M
  have hs := finite_comparison_scalar D l hl Ω X f BX BY c S t ht E L h M
  have hd := dual_formula_inclusion_scalar D l hl Ω X f BX BY E L h M
  dsimp only [RationalOperations.dualScalar] at hs
  refine scalar_paste
    (C₀ := Stage l Ω X E) (C₁ := Stage l Ω X L)
    (B := generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (T := transition l Ω X E L h)
    (I₀ := inclusion E) (I₁ := inclusion L) (inclusionTransition l Ω X E L h)
    (d := (BX.finite.scalar E L h).comparison.hom.app
      (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
        (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
          ((BY.finite.datum E).dual.obj (op M)))) ≫
      (BX.finite.datum L).dual.map
        (((@rationalDerivedPullback l _ (Coefficient.{u} l Ω L) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).map
            ((BY.finite.scalar E L h).comparison.inv.app (op M)) ≫
          (@rationalPullbackScalarComparison l _ (Coefficient.{u} l Ω E) _ _ _
            (Coefficient.{u} l Ω L) _ _ _
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X Y f
            (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).inv.app
              ((BY.finite.datum E).dual.obj (op M))).op))
    (p₀ := (t.finite E).comparison.hom.app M)
    (p₁ := (t.finite L).comparison.hom.app ((transition l Ω Y E L h).obj M))
    (t.normalized E M) (t.normalized L ((transition l Ω Y E L h).obj M)) ?_ ?_
  · exact hs
  · simpa only [specifiedExceptionalFormulaCore, RationalOperations.dualFormula,
      GeneralAlgebraicallyClosedCoefficients.transition, RationalVerdier.scalar,
      Functor.comp_obj, Functor.comp_map, Functor.rightOp_obj, Functor.rightOp_map,
      Functor.op_obj, Functor.op_map, unop_op, Category.assoc] using hd

end WeilConjectures.CoefQbarVerdier
