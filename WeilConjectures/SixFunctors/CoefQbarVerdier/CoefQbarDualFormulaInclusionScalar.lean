/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! Scalar compatibility of duality-pullback-duality inclusion components.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-dual-formula-inclusion-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback
  HasDerivedCategory.standard rationalPullbackScalarComparison
  ObjectProperty.FullSubcategory.category CoefQbarPullback
  inclusionTransition pullbackInclusion

private theorem stage_inclusion_eq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C H : I → Type*} [∀ i, Category (C i)] [∀ i, Category (H i)]
    {S : StageSystem C} {T : StageSystem H} (F : S.Morphism T) (i : I) :
    F.Φ i ⋙ T.ι i = S.ι i ⋙ F.functor := by
  refine Functor.hext (F := F.Φ i ⋙ T.ι i) (G := S.ι i ⋙ F.functor)
    (fun _ ↦ rfl) ?_
  intro A B a
  exact HEq.symm (heq_of_eq (F.functor_map_ι a))

private theorem stage_scalar_square
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C H : I → Type*} [∀ i, Category* (C i)] [∀ i, Category* (H i)]
    {S : StageSystem C} {T : StageSystem H} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) (x : C i) :
    (T.ι j).map ((F.β h).hom.app x) =
      (T.transIso h).hom.app ((F.Φ i).obj x) ≫
        F.functor.map ((S.transIso h).inv.app x) := by
  apply (cancel_mono (F.functor.map ((S.transIso h).hom.app x))).mp
  erw [Category.assoc, ← F.functor.map_comp, Iso.inv_hom_id_app, F.functor.map_id,
    Category.comp_id]
  erw [StageSystem.transIso_hom_app_eq, F.functor_map_mkHom,
    StageSystem.transIso_hom_app_eq, StageSystem.ι_map_eq le_rfl,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom j le_rfl h)
  dsimp only [StageSystem.Morphism.mapAt, StageSystem.PairCategory.toStage,
    StageSystem.Morphism.functor]
  have H := congrArg (fun t ↦ t ≫ (F.β h).inv.app x) (F.coh h le_rfl x)
  delta StageSystem.ι
  simpa only [Functor.comp_obj, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id] using H

private theorem adjusted_pullback_square
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C H : I → Type*} [∀ i, Category* (C i)] [∀ i, Category* (H i)]
    {S : StageSystem C} {T : StageSystem H} (F : S.Morphism T)
    (P : S.PairCategory ⥤ T.PairCategory) (eP : P = F.functor)
    {i j : I} (h : i ≤ j) {U : C i ⥤ C j} {V : H i ⥤ H j}
    (eU : S.T h = U) (eV : T.T h = V)
    (b : F.Φ i ⋙ V ≅ U ⋙ F.Φ j)
    (hb : F.β h = Functor.isoWhiskerLeft _ (eqToIso eV) ≪≫ b ≪≫
      Functor.isoWhiskerRight (eqToIso eU.symm) _) (x : C i) :
    (T.ι j).map (b.hom.app x) ≫
      (eqToIso ((stage_inclusion_eq F j).trans (congrArg (S.ι j ⋙ ·) eP.symm))).hom.app (U.obj x) =
      (eqToIso (congrArg (fun W ↦ W ⋙ T.ι j) eV.symm) ≪≫ T.transIso h).hom.app
        ((F.Φ i).obj x) ≫
      (eqToIso ((stage_inclusion_eq F i).trans (congrArg (S.ι i ⋙ ·) eP.symm))).hom.app x ≫ P.map
        ((eqToIso (congrArg (fun W ↦ W ⋙ S.ι j) eU.symm) ≪≫ S.transIso h).inv.app x) := by
  subst P
  subst U V
  have hb' : F.β h = b := by
    ext z
    simpa using congrArg (fun e ↦ e.hom.app z) hb
  simp only [eqToIso_refl, Iso.refl_trans, eqToIso.hom, eqToHom_app, eqToHom_refl]
  erw [Category.comp_id, Category.id_comp]
  simpa only [hb'] using stage_scalar_square F h x

private theorem paste_scalar_duals
    {C₀ C₁ H₀ H₁ C H : Type*}
    [Category C₀] [Category C₁] [Category H₀] [Category H₁] [Category C] [Category H]
    (IY₀ : C₀ ⥤ C) (IY₁ : C₁ ⥤ C) (IX₀ : H₀ ⥤ H) (IX₁ : H₁ ⥤ H)
    (TY : C₀ ⥤ C₁) (TX : H₀ ⥤ H₁)
    (ty : TY ⋙ IY₁ ≅ IY₀) (tx : TX ⋙ IX₁ ≅ IX₀)
    (dy₀ : C₀ᵒᵖ ⥤ C₀) (dy₁ : C₁ᵒᵖ ⥤ C₁)
    (dx₀ : H₀ᵒᵖ ⥤ H₀) (dx₁ : H₁ᵒᵖ ⥤ H₁)
    (DY : Cᵒᵖ ⥤ C) (DX : Hᵒᵖ ⥤ H)
    (by₀ : dy₀ ⋙ IY₀ ≅ IY₀.op ⋙ DY) (by₁ : dy₁ ⋙ IY₁ ≅ IY₁.op ⋙ DY)
    (bx₀ : dx₀ ⋙ IX₀ ≅ IX₀.op ⋙ DX) (bx₁ : dx₁ ⋙ IX₁ ≅ IX₁.op ⋙ DX)
    (βy : dy₀ ⋙ TY ≅ TY.op ⋙ dy₁) (βx : dx₀ ⋙ TX ≅ TX.op ⋙ dx₁)
    (R₀ : C₀ ⥤ H₀) (R₁ : C₁ ⥤ H₁) (P : C ⥤ H)
    (pb₀ : R₀ ⋙ IX₀ ≅ IY₀ ⋙ P) (pb₁ : R₁ ⋙ IX₁ ≅ IY₁ ⋙ P)
    (βp : R₀ ⋙ TX ≅ TY ⋙ R₁)
    (hx : ∀ K, IX₁.map (βx.hom.app (op K)) ≫
      bx₁.hom.app (op (TX.obj K)) ≫ DX.map (tx.inv.app K).op =
        tx.hom.app (dx₀.obj (op K)) ≫ bx₀.hom.app (op K))
    (hy : ∀ M, IY₁.map (βy.hom.app (op M)) ≫
      by₁.hom.app (op (TY.obj M)) ≫ DY.map (ty.inv.app M).op =
        ty.hom.app (dy₀.obj (op M)) ≫ by₀.hom.app (op M))
    (hp : ∀ N, IX₁.map (βp.hom.app N) ≫ pb₁.hom.app (TY.obj N) =
      tx.hom.app (R₀.obj N) ≫ pb₀.hom.app N ≫ P.map (ty.inv.app N))
    (M : C₀) :
    IX₁.map (βx.hom.app (op (R₀.obj (dy₀.obj (op M)))) ≫
      dx₁.map (R₁.map (βy.inv.app (op M)) ≫ βp.inv.app (dy₀.obj (op M))).op) ≫
      bx₁.hom.app (op (R₁.obj (dy₁.obj (op (TY.obj M))))) ≫
      DX.map (P.map (by₁.inv.app (op (TY.obj M))) ≫
        pb₁.inv.app (dy₁.obj (op (TY.obj M)))).op =
    tx.hom.app (dx₀.obj (op (R₀.obj (dy₀.obj (op M))))) ≫
      bx₀.hom.app (op (R₀.obj (dy₀.obj (op M)))) ≫
      DX.map (P.map (by₀.inv.app (op M)) ≫ pb₀.inv.app (dy₀.obj (op M))).op ≫
      (DY.rightOp ⋙ P.op ⋙ DX).map (ty.inv.app M) := by
  let N := dy₀.obj (op M)
  let K := R₀.obj N
  let g := R₁.map (βy.inv.app (op M)) ≫ βp.inv.app N
  have hx' : IX₁.map (βx.hom.app (op K)) ≫ bx₁.hom.app (op (TX.obj K)) =
      tx.hom.app (dx₀.obj (op K)) ≫ bx₀.hom.app (op K) ≫
        DX.map (tx.hom.app K).op := by
    apply (cancel_mono (DX.map (tx.inv.app K).op)).mp
    simp only [Category.assoc, ← DX.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id]
    simpa using hx K
  have hy' : by₁.inv.app (op (TY.obj M)) ≫ IY₁.map (βy.inv.app (op M)) ≫
      ty.hom.app N = DY.map (ty.inv.app M).op ≫ by₀.inv.app (op M) := by
    apply (cancel_epi (IY₁.map (βy.hom.app (op M)) ≫
      by₁.hom.app (op (TY.obj M)))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← IY₁.map_comp_assoc,
      Iso.hom_inv_id_app]
    simpa [Category.assoc] using
      (congrArg (fun a ↦ a ≫ by₀.inv.app (op M)) (hy M)).symm
  have hp' : pb₁.inv.app (TY.obj N) ≫ IX₁.map (βp.inv.app N) ≫
      tx.hom.app K = P.map (ty.hom.app N) ≫ pb₀.inv.app N := by
    apply (cancel_epi (IX₁.map (βp.hom.app N) ≫ pb₁.hom.app (TY.obj N))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← IX₁.map_comp_assoc,
      Iso.hom_inv_id_app]
    rw [← Category.assoc, hp N]
    simp only [Category.assoc, ← P.map_comp_assoc, Iso.inv_hom_id_app]
    simp
    rfl
  have hn := pb₁.inv.naturality (βy.inv.app (op M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.op_obj] at hn
  have hq : (P.map (by₁.inv.app (op (TY.obj M))) ≫
      pb₁.inv.app (dy₁.obj (op (TY.obj M)))) ≫ IX₁.map g ≫ tx.hom.app K =
      P.map (DY.map (ty.inv.app M).op) ≫
        P.map (by₀.inv.app (op M)) ≫ pb₀.inv.app N := by
    dsimp only [g]
    rw [IX₁.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hn, hp']
    simp only [← P.map_comp_assoc]
    rw [hy']
  have hxnat := bx₁.hom.naturality g.op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hxnat
  simp only [IX₁.map_comp, Functor.comp_map, Functor.rightOp_map, Functor.op_map,
    Quiver.Hom.unop_op]
  rw [Category.assoc, ← Category.assoc (IX₁.map (dx₁.map g.op)), hxnat]
  simp only [← Category.assoc]
  simp only [Functor.comp_obj] at *
  rw [hx']
  simp only [Category.assoc]
  congr 2
  simp only [← DX.map_comp, ← op_comp]
  simpa only [Category.assoc] using congrArg (fun a ↦ DX.map a.op) hq

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

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1200000 in
-- The normalized descent and composite comparison require a larger elaboration budget.
/-- Transporting the dual-formula scalar map through the finite-origin duality
comparisons gives the common-stage scalar square. No exceptional functor or exceptional
comparison occurs in this statement.
Source: thm-coef-qbar-verdier, retained proof step 9, substitution of the BX, BY and
pullback scalar squares. (blueprint: lem-coef-qbar-dual-formula-inclusion-scalar)

Proof: write K = pullback_E(DY_E M). Expand the displayed scalar map as beta_X(K)
followed by DX_L of the opposite of pullback_L(beta_Y inverse) followed by the inverse
pullback scalar comparison. Naturality of BX.comparison moves the latter factor through
the BX comparison at L. The scalar equation in BX.properties, with betaNormalized,
replaces the resulting beta_X and BX comparison by inclusionTransition_X followed by
the BX comparison at E; its remaining factor is BX.dual applied to the opposite inverse
inclusionTransition_X at K. In the remaining contravariant argument, naturality and the
scalar square for pullbackInclusion move the inverse pullback scalar comparison through
the two pullback inclusions. The scalar equation in BY.properties, inverted and using
betaNormalized, replaces beta_Y inverse and the BY comparisons by BY.dual of inverse
inclusionTransition_Y. Functoriality of pullback and the contravariant dual combines these
factors; the adjacent inclusionTransition_X inverse and forward factors cancel. The
result is exactly the right side. All comparisons are isomorphisms, so cancellation is
valid on zero objects and for identity or repeated coefficient fields as well. -/
theorem dual_formula_inclusion_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E) :
    (inclusion L).map
      ((BX.finite.scalar E L h).comparison.hom.app
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
                ((BY.finite.datum E).dual.obj (op M))).op)) ≫
      (BX.comparison L).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω L) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum L).dual.obj (op ((transition l Ω Y E L h).obj M))))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map
          ((BY.comparison L).inv.app (op ((transition l Ω Y E L h).obj M))) ≫
          (pullbackInclusion D l hl Ω X f L
            ((BY.finite.datum L).dual.obj (op ((transition l Ω Y E L h).obj M)))).inv).op =
    (inclusionTransition l Ω X E L h).hom.app
      ((BX.finite.datum E).dual.obj
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M))))) ≫
      (BX.comparison E).hom.app
        (op ((@rationalDerivedPullback l _ (Coefficient.{u} l Ω E) _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).obj
            ((BY.finite.datum E).dual.obj (op M)))) ≫
      BX.duality.dual.map
        ((CoefQbarPullback D l hl Ω f).map ((BY.comparison E).inv.app (op M)) ≫
          (pullbackInclusion D l hl Ω X f E
            ((BY.finite.datum E).dual.obj (op M))).inv).op ≫
      (BY.duality.dual.rightOp ⋙ (CoefQbarPullback D l hl Ω f).op ⋙ BX.duality.dual).map
        ((inclusionTransition l Ω Y E L h).inv.app M) := by
  letI := RationalVerdier.units D l hl X
  letI := RationalVerdier.units D l hl Y
  obtain ⟨hcoh, hP⟩ := commonStagePullbackNormalizedDescent l Ω f
  let F : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X) :=
    ⟨fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f,
      commonStagePullbackTransition l Ω f, hcoh⟩
  have hF : CoefQbarPullback D l hl Ω f = F.functor := by
    delta CoefQbarPullback
    exact hP
  have hp (A : Index l Ω) :
      rationalDerivedPullback l (Coefficient.{u} l Ω A) f ⋙ inclusion A =
        inclusion A ⋙ CoefQbarPullback D l hl Ω f := by
    rw [hF]
    exact stage_inclusion_eq F A
  have hc (A : Index l Ω) (N : Stage l Ω Y A) :
      (eqToIso (hp A)).app N = pullbackInclusion D l hl Ω X f A N := by
    apply Iso.ext
    rw [Iso.app_hom, eqToIso.hom, eqToHom_app]
    unfold pullbackInclusion
    erw [eqToIso.hom]
  have hpb (N : Stage l Ω Y E) :
      (inclusion L).map
          ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) f).hom.app N) ≫
        (eqToIso (hp L)).hom.app ((transition l Ω Y E L h).obj N) =
      (inclusionTransition l Ω X E L h).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj N) ≫
        (eqToIso (hp E)).hom.app N ≫
        (CoefQbarPullback D l hl Ω f).map
          ((inclusionTransition l Ω Y E L h).inv.app N) := by
    have hs := adjusted_pullback_square F (CoefQbarPullback D l hl Ω f) hF h
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).exists.choose_spec.1
        E L h)
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists.choose_spec.1
        E L h)
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) f)
      (by rfl) N
    delta inclusionTransition
    exact hs
  have hx := BX.properties.2.2.2.2.2.2.1 E L h
  have hy := BY.properties.2.2.2.2.2.2.1 E L h
  have ex := eq_of_heq (BX.finite.betaNormalized E L h)
  have ey := eq_of_heq (BY.finite.betaNormalized E L h)
  rw [ex] at hx
  rw [ey] at hy
  have ht := paste_scalar_duals
    (inclusion (Y := Y) E) (inclusion (Y := Y) L)
    (inclusion (Y := X) E) (inclusion (Y := X) L)
    (transition l Ω Y E L h) (transition l Ω X E L h)
    (inclusionTransition l Ω Y E L h) (inclusionTransition l Ω X E L h)
    (BY.finite.datum E).dual (BY.finite.datum L).dual
    (BX.finite.datum E).dual (BX.finite.datum L).dual
    BY.duality.dual BX.duality.dual
    (BY.comparison E) (BY.comparison L) (BX.comparison E) (BX.comparison L)
    (BY.finite.scalar E L h).comparison (BX.finite.scalar E L h).comparison
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f)
    (CoefQbarPullback D l hl Ω f) (eqToIso (hp E)) (eqToIso (hp L))
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) f)
    hx hy hpb M
  simpa only [← Iso.app_inv, hc] using ht

end WeilConjectures.CoefQbarVerdier
