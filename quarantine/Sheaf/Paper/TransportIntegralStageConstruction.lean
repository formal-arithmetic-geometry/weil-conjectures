/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.TransportIntegralCounitData

/-! # Integral stages and scalar comparisons

Source: purity-transport, the existing integral realization argument.
(blueprint: lem-pur-integral-stage-construction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private theorem transported_fixed_counit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G J H : D ⥤ C} (adj : F ⊣ G) (g : J ≅ G) (a : F ⊣ H) (K : D) :
    (adj.ofNatIsoRight g.symm).counit.app K =
      F.map (g.hom.app K ≫ (adj.rightAdjointUniq a).hom.app K) ≫ a.counit.app K := by
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv, Functor.map_comp, Category.assoc,
    Adjunction.rightAdjointUniq_hom_app_counit]

private theorem transported_unit_reduction
    {C D T : Type*} [Category C] [Category D] [Category T]
    {F : C ⥤ D} {G J : D ⥤ C} (adj : F ⊣ G) (g : J ≅ G) (R : C ⥤ T) (M : C)
    {U V : T} (a : R.obj M ⟶ U) (b : U ⟶ V) (c : V ⟶ R.obj (G.obj (F.obj M)))
    (h : R.map (adj.unit.app M) = a ≫ b ≫ c) :
    R.map ((adj.ofNatIsoRight g.symm).unit.app M) =
      a ≫ b ≫ c ≫ R.map (g.inv.app (F.obj M)) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp, h, Category.assoc]

private theorem transported_counit_reduction
    {C D T : Type*} [Category C] [Category D] [Category T]
    {F : C ⥤ D} {G J : D ⥤ C} (adj : F ⊣ G) (g : J ≅ G) (R : D ⥤ T) (K : D)
    {U V : T} (a : R.obj (F.obj (G.obj K)) ⟶ U) (b : U ⟶ V) (c : V ⟶ R.obj K)
    (h : R.map (adj.counit.app K) = a ≫ b ≫ c) :
    R.map ((adj.ofNatIsoRight g.symm).counit.app K) =
      R.map (F.map (g.hom.app K)) ≫ a ≫ b ≫ c := by
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv, Functor.map_comp, h]

private theorem transported_right_eq
    {A B C D : Type w} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {J G : B ⥤ A} {J' G' : D ⥤ C} (SX : A ⥤ C) (SY : B ⥤ D)
    (g : J ≅ G) (g' : J' ≅ G') (c : G ⋙ SX ≅ SY ⋙ G') (a : J ⋙ SX ≅ SY ⋙ J')
    (h : ∀ K, SX.map (g.hom.app K) ≫ c.hom.app K =
      a.hom.app K ≫ g'.hom.app (SY.obj K)) :
    Functor.isoWhiskerRight g SX ≪≫ c ≪≫ Functor.isoWhiskerLeft SY g'.symm = a := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem conjugated_purity_square
    {A B C D : Type w} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {J G H : B ⥤ A} {J' G' H' : D ⥤ C} (SX : A ⥤ C) (SY : B ⥤ D)
    (g : J ≅ G) (g' : J' ≅ G') (c : G ⋙ SX ≅ SY ⋙ G') (a : J ⋙ SX ≅ SY ⋙ J')
    (h : ∀ K, SX.map (g.hom.app K) ≫ c.hom.app K =
      a.hom.app K ≫ g'.hom.app (SY.obj K))
    (delta : G ≅ H) (delta' : G' ≅ H') (K : B) :
    SX.map (g.hom.app K ≫ delta.hom.app K) ≫
        (Functor.isoWhiskerRight delta.symm SX ≪≫ c ≪≫
          Functor.isoWhiskerLeft SY delta').hom.app K =
      a.hom.app K ≫ g'.hom.app (SY.obj K) ≫ delta'.hom.app (SY.obj K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  erw [(delta.app K).map_hom_inv_id_assoc SX]
  rw [← Category.assoc, h, Category.assoc]

private def transportScalarComparison
    {A B C D : Type w} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {F : A ⥤ B} {G H : B ⥤ A} {F' : C ⥤ D} {G' H' : D ⥤ C}
    {SX : A ⥤ C} {SY : B ⥤ D} {adj : F ⊣ G} {adj' : F' ⊣ G'}
    (c : FieldScalarAdjunctionComparison adj adj' SX SY) (g : H ≅ G) (g' : H' ≅ G') :
    FieldScalarAdjunctionComparison (adj.ofNatIsoRight g.symm)
      (adj'.ofNatIsoRight g'.symm) SX SY where
  left := c.left
  right := Functor.isoWhiskerRight g SX ≪≫ c.right ≪≫ Functor.isoWhiskerLeft SY g'.symm
  unit M := by
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.symm_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.map_comp,
      Category.assoc]
    erw [(g.app (F.obj M)).map_inv_hom_id_assoc SX]
    rw [← g'.inv.naturality]
    simpa only [Category.assoc, Functor.comp_obj] using
      congrArg (fun f ↦ f ≫ g'.inv.app (F'.obj (SX.obj M))) (c.unit M)
  counit K := by
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerRight_app, Iso.symm_inv, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    erw [(g'.app (SY.obj K)).map_inv_hom_id_assoc F']
    rw [c.counit]
    exact c.left.inv.naturality_assoc (g.hom.app K) (SY.map (adj.counit.app K))

private theorem comparison_adjunction_eq
    {A B C D : Type w} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    {SX : A ⥤ C} {SY : B ⥤ D} {adj : F ⊣ G} {adj' : F' ⊣ G'}
    (c : FieldScalarAdjunctionComparison adj adj' SX SY)
    (a : F ⊣ G) (a' : F' ⊣ G') (h : adj = a) (h' : adj' = a') :
    ∃ c' : FieldScalarAdjunctionComparison a a' SX SY,
      c'.left = c.left ∧ c'.right = c.right := by
  subst a a'
  exact ⟨c, rfl, rfl⟩

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

section IntegralStage

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

omit [CompactSpace X] [QuasiSeparatedSpace Y] in
private theorem gamma_natural (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d)
    {K K' : FieldExtensionTowers.Integral P E Y} (v : K ⟶ K') :
    (FieldExtensionTowers.puritySource P D j p d m).map v ≫
        FieldExtensionTowers.gamma P D j p d m K' =
      FieldExtensionTowers.gamma P D j p d m K ≫
        (FieldExtensionTowers.exceptional P D j p d m).map v := by
  let : CompactSpace X := FieldExtensionTowers.compactSpace P X
  let : QuasiSeparatedSpace Y := FieldExtensionTowers.quasiSeparatedSpace P Y
  let := m.realization.noetherianX
  let := m.realization.noetherianY
  let src := SpTwistedPullback.source P.coefficients.l E.val (j ≫ p)
    (d : ℤ) (2 * (d : ℤ))
  let red := FieldExtensionTowers.reduceY P D j p d m
  let ex := SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
    ((D.coordinates E).abelian X)
  let L := SpIntegralAdjunction.limit P.coefficients.l E.val X
    ((D.coordinates E).abelian X) m.reductionX m.normalizationX
  let gamma :
      red ⋙ SpTowerGamma.source P.coefficients.l E.val (D.base E) (D.operations E)
        (D.coordinates E) (j ≫ p) m.twists d ⟶
      red ⋙ SpTowerGamma.exceptional P.coefficients.l E.val (D.base E)
        (D.coordinates E) m.exceptional :=
    { app K := SpTowerGamma.gamma P.coefficients.l E.val (D.base E) (D.operations E)
        (D.coordinates E) (SpTowerGamma.factorization j p) m.twists d
        m.realization.purity.tensorX m.realization.purity.tensorY m.supportClosed
        m.exceptional m.adjunction m.realization.purity.unit_mem
        m.realization.purity.orientation (red.obj K)
        (m.realization.purity.tensor_mem _) (m.realization.purity.projection_iso _)
      naturality _ _ v := m.realization.purity.naturality _ _ (red.map v) }
  let t := m.realization.sourceComparison.hom ≫ gamma
  let F := src ⋙ spCompletedReduction P.coefficients.l E.val X
    ((D.coordinates E).abelian X) m.reductionX
  let G := red ⋙ m.exceptional ⋙
    SpTowerCalculus.inclusion P.coefficients.l E.val (D.base E) (D.coordinates E) X
  let z : F ⟶ G := Functor.whiskerLeft F ex.unitIso.hom ≫
    Functor.whiskerRight t ex.inverse ≫ Functor.whiskerLeft G ex.unitIso.inv
  let a : src ⟶ FieldExtensionTowers.exceptional P D j p d m ⋙
      (sfIntegralConstructible P.coefficients.l E.val X).ι :=
    Functor.whiskerLeft src m.normalizationX.adjunction.unit ≫ Functor.whiskerRight z L
  apply ObjectProperty.hom_ext
  exact a.naturality v

-- Retain the existing public instance binders for downstream compatibility.
set_option linter.unusedSectionVars false in
/-- Transport of the specified entire-tower Hom adjunction, with its normalized gamma.
Source: latest blueprint, purity-transport Steps 2--3.
(blueprint: lem-pur-integral-stage-construction).

Proof: the source comparison, reconstruction unit and total inverse limit make the
actual tower gamma natural. Its invertibility is purity_realization in
 det-sp-integral-adjunction-bijection. Full-subcategory faithfulness assembles these
components into gammaH. Transport the recorded adjunction by gammaH inverse.
The two Hom formulas are the three recorded Hom comparisons followed by gammaH
inverse, and their inverse is epsilon^H F(a gammaH). Evaluation at identities gives
the displayed unit and counit. For any specified right adjoint use
 det-sp-unique-right-adjoint: its comparison delta satisfies F(delta) epsilon =
epsilon^H. Functoriality gives the fixed_counit equation with gammaT = gammaH delta.
No uniqueness from finite derived evaluations is used. -/
theorem integral_stage (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d) :
    Nonempty (Stage P D j p d E m) := by
  let := m.realization.noetherianX
  let := m.realization.noetherianY
  have (K : FieldExtensionTowers.Integral P E Y) :
      IsIso (FieldExtensionTowers.gamma P D j p d m K) := by
    have : IsIso ((sfIntegralConstructible P.coefficients.l E.val X).ι.map
        (FieldExtensionTowers.gamma P D j p d m K)) :=
      m.realization.purity_realization m.realization.sourceComparison K
    exact isIso_of_reflects_iso _ (sfIntegralConstructible P.coefficients.l E.val X).ι
  let g : FieldExtensionTowers.puritySource P D j p d m ≅
      FieldExtensionTowers.exceptional P D j p d m :=
    NatIso.ofComponents (fun K ↦ asIso (FieldExtensionTowers.gamma P D j p d m K))
      (fun v ↦ gamma_natural P D j p d E m v)
  refine ⟨{
    gammaH := g
    gammaH_eq := fun _ ↦ rfl
    adjunction := m.realization.adjunction.ofNatIsoRight g.symm
    transported := rfl
    hom := fun _ _ h ↦ Adjunction.homEquiv_ofNatIsoRight_apply _ _ h
    inverse := ?_
    unit := fun _ ↦ rfl
    counit := fun _ ↦ rfl
    fixed_counit := ?_
    unit_reduction := ?_
    counit_reduction := ?_ }⟩
  · intro M K a
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.homEquiv_counit]
    rfl
  · intro G a K
    exact transported_fixed_counit m.realization.adjunction g a K
  · intro M
    exact transported_unit_reduction m.realization.adjunction g
      (FieldExtensionTowers.reduceX P D j p d m) M
      _ _ _ (m.realization.unit_reduction M)
  · intro K
    exact transported_counit_reduction m.realization.adjunction g
      (FieldExtensionTowers.reduceY P D j p d m) K
      _ _ _ (m.realization.counit_reduction K)


-- Retain the existing public instance binders for downstream compatibility.
set_option linter.unusedSectionVars false in
/-- Completed scalar extension transports the actual smooth adjunction. Its left
comparison is the compact-support comparison and its right comparison is the
twisted-pullback comparison, including their prescribed normalized reductions.
Consequently its unit and counit equations are equations of actual integral maps.
Source: purity-transport Step 4 and field-extension-towers clause (2).
(blueprint: lem-pur-integral-stage-construction).

Proof: use the normalized completed scalar comparisons in R.integral. Their purity
square intertwines gammaH. Substitute that square into the displayed unit and counit
of integral_stage and use naturality of the left comparison. Cancellation of gammaH
and its inverse gives the two adjunction comparison equations. The comparisons are
exactly the left and source comparisons of R.integral, so R.composition.left and
R.composition.source give their transitivity for E ⊆ F ⊆ L, including identities.
The right-adjoint comparison to any specified exceptional adjoint is obtained by
conjugating R.integral.comparison.right by the counit-preserving uniqueness maps;
its purity square follows by substitution and its cocycle by cancellation. -/
theorem coefficient_stage (R : FieldExtensionTowers.Result P D j p d)
    (A : ∀ E : FieldShriekSystem.Index P, Stage P D j p d E (R.model E))
    (E F : FieldShriekSystem.Index P) (h : E ≤ F) :
    ∃ c : CategoryTheory.FieldScalarAdjunctionComparison
      (A E).adjunction (A F).adjunction
      (FieldExtensionTowers.scalar P h X) (FieldExtensionTowers.scalar P h Y),
      c.left = (R.integral E F h).comparison.left ∧
      c.right = (R.integral E F h).sourceComparison := by
  let c := transportScalarComparison (R.integral E F h).comparison
    (A E).gammaH (A F).gammaH
  have hp := (R.integral E F h).purity
  unfold FieldExtensionTowers.integralPuritySquare at hp
  have hs (K : FieldExtensionTowers.Integral P E Y) :
      (FieldExtensionTowers.scalar P h X).map ((A E).gammaH.hom.app K) ≫
          (R.integral E F h).comparison.right.hom.app K =
        (R.integral E F h).sourceComparison.hom.app K ≫
          (A F).gammaH.hom.app ((FieldExtensionTowers.scalar P h Y).obj K) := by
    simpa only [(A E).gammaH_eq, (A F).gammaH_eq] using hp K
  have hr : c.right = (R.integral E F h).sourceComparison :=
    transported_right_eq _ _ _ _ _ _ hs
  obtain ⟨c', hl, hr'⟩ := comparison_adjunction_eq c (A E).adjunction
    (A F).adjunction (A E).transported.symm (A F).transported.symm
  exact ⟨c', hl, hr'.trans hr⟩


-- Retain the existing public instance binders for downstream compatibility.
set_option linter.unusedSectionVars false in
/-- Scalar transport for gammaT with any specified exceptional adjunctions.
The right comparison is exactly the conjugate of the realized exceptional comparison
by the two counit-preserving uniqueness maps; it is not a chosen exceptional exchange.
Source: purity-transport Step 4, coefficient-mate conjugation.
(blueprint: lem-pur-integral-stage-construction).

Proof: let deltaE and deltaF be rightAdjointUniq for the realized and specified
adjunctions. Conjugate the right comparison of R.integral by deltaE inverse and
deltaF. Counit preservation gives its scalar-adjunction comparison equations with
the same left comparison. Substitute gammaH delta for gammaT in the displayed square,
use R.integral.purity and cancel deltaE inverse followed by deltaE. Conjugation
preserves the cocycle equations since the intermediate delta and its inverse cancel;
R.composition supplies the original cocycles, including identity inclusions. -/
theorem fixed_coefficient_stage (R : FieldExtensionTowers.Result P D j p d)
    (A : ∀ E : FieldShriekSystem.Index P, Stage P D j p d E (R.model E))
    (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (GE : FieldExtensionTowers.Integral P E Y ⥤ FieldExtensionTowers.Integral P E X)
    (GF : FieldExtensionTowers.Integral P F Y ⥤ FieldExtensionTowers.Integral P F X)
    (aE : FieldExtensionTowers.support P D j p d (R.model E) ⊣ GE)
    (aF : FieldExtensionTowers.support P D j p d (R.model F) ⊣ GF) :
    ∃ c : CategoryTheory.FieldScalarAdjunctionComparison aE aF
      (FieldExtensionTowers.scalar P h X) (FieldExtensionTowers.scalar P h Y),
      c.left = (R.integral E F h).comparison.left ∧
      c.right =
        Functor.isoWhiskerRight ((R.model E).realization.adjunction.rightAdjointUniq aE).symm
            (FieldExtensionTowers.scalar P h X) ≪≫
          (R.integral E F h).comparison.right ≪≫
          Functor.isoWhiskerLeft (FieldExtensionTowers.scalar P h Y)
            ((R.model F).realization.adjunction.rightAdjointUniq aF) ∧
      ∀ K : FieldExtensionTowers.Integral P E Y,
        (FieldExtensionTowers.scalar P h X).map
            ((A E).gammaH.hom.app K ≫
              ((R.model E).realization.adjunction.rightAdjointUniq aE).hom.app K) ≫
            c.right.hom.app K =
          (R.integral E F h).sourceComparison.hom.app K ≫
            (A F).gammaH.hom.app ((FieldExtensionTowers.scalar P h Y).obj K) ≫
            ((R.model F).realization.adjunction.rightAdjointUniq aF).hom.app
              ((FieldExtensionTowers.scalar P h Y).obj K) := by
  let deltaE := (R.model E).realization.adjunction.rightAdjointUniq aE
  let deltaF := (R.model F).realization.adjunction.rightAdjointUniq aF
  let c := transportScalarComparison (R.integral E F h).comparison deltaE.symm deltaF.symm
  have hE : (R.model E).realization.adjunction.ofNatIsoRight deltaE = aE := by
    apply Adjunction.ext
    exact (R.model E).realization.adjunction.unit_rightAdjointUniq_hom aE
  have hF : (R.model F).realization.adjunction.ofNatIsoRight deltaF = aF := by
    apply Adjunction.ext
    exact (R.model F).realization.adjunction.unit_rightAdjointUniq_hom aF
  obtain ⟨c', hl, hr⟩ := comparison_adjunction_eq c aE aF hE hF
  refine ⟨c', hl, hr, ?_⟩
  intro K
  rw [hr]
  have hp := (R.integral E F h).purity
  unfold FieldExtensionTowers.integralPuritySquare at hp
  have hs (L : FieldExtensionTowers.Integral P E Y) :
      (FieldExtensionTowers.scalar P h X).map ((A E).gammaH.hom.app L) ≫
          (R.integral E F h).comparison.right.hom.app L =
        (R.integral E F h).sourceComparison.hom.app L ≫
          (A F).gammaH.hom.app ((FieldExtensionTowers.scalar P h Y).obj L) := by
    simpa only [(A E).gammaH_eq, (A F).gammaH_eq] using hp L
  exact conjugated_purity_square _ _ _ _ _ _ hs deltaE deltaF K


end IntegralStage
end AlgebraicGeometry.ProEtale.TransportIntegralCounit
