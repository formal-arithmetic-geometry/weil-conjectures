/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitFoundations
import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportStrictReductionComparison

/-! # The morphism underlying the support realization

Source: Stacks Tags 0A07, 0GL1 and 0941; the strict augmentation construction
in Steps 5--6 of the scalar projection identification.
(blueprint: lem-pur-compact-support-projection-realization-lift).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurScalarProjection
open PurCompactSupport

private theorem reduction_comparison_evaluation
    {C T V : Type*} [Category C] [Category T] [Category V]
    {F F' : C ⥤ T} {G : T ⥤ C} (a : F ⊣ G) (a' : F' ⊣ G)
    {R : C ⥤ V} {U : V ⥤ C} (b : R ⊣ U)
    (ev : T ⥤ V) (π : G ⟶ ev ⋙ U)
    (e : F ⋙ ev ≅ R) (e' : F' ⋙ ev ≅ R)
    (hu : ∀ P, a.unit.app P ≫ π.app (F.obj P) =
      b.unit.app P ≫ U.map (e.inv.app P))
    (hu' : ∀ P, a'.unit.app P ≫ π.app (F'.obj P) =
      b.unit.app P ≫ U.map (e'.inv.app P)) (P : C) :
    e.inv.app P ≫ ev.map ((a.leftAdjointUniq a').hom.app P) = e'.inv.app P := by
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := π.naturality ((a.leftAdjointUniq a').hom.app P)
  simp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, a.unit_leftAdjointUniq_hom_app a', hu']

private theorem adjunct_change
    {C V : Type*} [Category C] [Category V]
    {F F' : C ⥤ V} {U : V ⥤ C} (a : F ⊣ U) (b : F' ⊣ U)
    {P : C} {Q : V} (f : P ⟶ U.obj Q) :
    (a.leftAdjointUniq b).inv.app P ≫ (a.homEquiv _ _).symm f =
      (b.homEquiv _ _).symm f := by
  apply (b.homEquiv _ _).injective
  rw [b.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  change (b.unit.app P ≫ U.map ((b.leftAdjointUniq a).hom.app P)) ≫ _ = _
  rw [b.unit_leftAdjointUniq_hom_app a]
  exact (a.homEquiv_unit _ _ _).symm.trans
    ((Equiv.apply_symm_apply _ _).trans (Equiv.apply_symm_apply _ _).symm)

private theorem projection_adjunct
    {C T V : Type*} [Category C] [Category T] [Category V]
    {F : C ⥤ T} {G : T ⥤ C} (a : F ⊣ G)
    {R : C ⥤ V} {U : V ⥤ C} (b : R ⊣ U)
    (ev : T ⥤ V) (π : G ⟶ ev ⋙ U) (e : F ⋙ ev ≅ R)
    (hu : ∀ P, a.unit.app P ≫ π.app (F.obj P) =
      b.unit.app P ≫ U.map (e.inv.app P))
    {P : C} {N : T} {Q : V} (β : F.obj P ⟶ N) (ε : ev.obj N ⟶ Q) :
    R.map ((a.homEquiv _ _) β) ≫
        (b.homEquiv _ _).symm (π.app N ≫ U.map ε) =
      e.inv.app P ≫ ev.map β ≫ ε := by
  apply (b.homEquiv _ _).injective
  rw [b.homEquiv_naturality_left, Equiv.apply_symm_apply]
  rw [a.homEquiv_unit]
  simp only [Category.assoc]
  have hn := π.naturality β
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, reassoc_of% hu]
  simp only [Functor.map_comp, Adjunction.homEquiv_unit]

/-- The actual proper/open finite mates lift to a morphism into the native total limit.
This asserts neither invertibility nor uniqueness of the lift.

Source: Stacks Tags 0A07, 0GL1 and 0941; scalar projection identification,
Steps 5--6 (blueprint: lem-pur-compact-support-projection-realization-lift).

Proof: obtain SX, SY and the normalized whole-system morphism beta from the
strict reduction comparison. Transport SX.reduction to S.reduction by uniqueness
of left adjoints to the same total-limit functor. Their unit_projection equations
identify every finite evaluation of this transport. Compose beta with its native
proper/open image and transpose under the SY reduction/limit adjunction. Projection
naturality and the SY unit equation identify each finite adjunct with evaluation
of beta. Its normalized equation cancels the finite coordinate isomorphisms.
Uniqueness of left adjoints identifies this finite adjunct with the specified
pbc scalar adjunct. No invertibility, constructibility or uniqueness is assumed.
Zero objects and empty opens use the same adjunction identities. -/
theorem compactSupportProjectionRealization_lift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    ∃ ρ : (image (completed l E) c).obj M ⟶
        (PurStrictScalar.scalarSupport l E c S).obj M,
      ∀ n : ℕ,
        (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map
            ρ ≫ PurStrictScalar.scalarSupportCounit l E c S n M =
          (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M := by
  obtain ⟨SX, SY, β, _, hβ, _⟩ :=
    qcqsCompactSupport_strictReductionComparison l E D.k (coefficientPrimeUnit l D hl) c
  let V := ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g
  let θ := SX.adjunction.leftAdjointUniq S.adjunction
  let α := β.app M ≫ V.map (θ.hom.app M)
  let ρ := (SY.adjunction.homEquiv _ _) α
  refine ⟨ρ, ?_⟩
  intro n
  have hθ := reduction_comparison_evaluation SX.adjunction S.adjunction
    (coefficientFiniteAdjunction l E X n) (coefficientSequenceDerivedEvaluation l E X n)
    (coefficientSequenceProjection l E X n) (SX.reductionEvaluation n)
    (S.reductionEvaluation n) (SX.unit_projection · n) (S.unit_projection · n) M
  have hθ' : (coefficientSequenceDerivedEvaluation l E X n).map (θ.hom.app M) ≫
      (S.reductionEvaluation n).hom.app M = (SX.reductionEvaluation n).hom.app M := by
    apply (cancel_epi ((SX.reductionEvaluation n).inv.app M)).1
    rw [← Category.assoc, hθ, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  have hV : (coefficientSequenceDerivedEvaluation l E Y n).map
        (V.map (θ.hom.app M)) ≫
      (PurStrictScalar.scalarSupportEvaluation l E c S n).hom.app M =
        (PurStrictScalar.scalarSupportEvaluation l E c SX n).hom.app M := by
    have hn := (compactSupportSystemEvaluation l E c n).hom.naturality (θ.hom.app M)
    dsimp only [PurStrictScalar.scalarSupportEvaluation, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
    try simp only [Category.assoc]
    erw [reassoc_of% hn]
    erw [← Functor.map_comp_assoc, hθ']
  have hα := projection_adjunct SY.adjunction (coefficientFiniteAdjunction l E Y n)
    (coefficientSequenceDerivedEvaluation l E Y n) (coefficientSequenceProjection l E Y n)
    (SY.reductionEvaluation n) (SY.unit_projection · n) α
    ((PurStrictScalar.scalarSupportEvaluation l E c S n).hom.app M)
  change (coefficientFiniteDerivedExtension l E Y n).map ρ ≫
      ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).symm
        ((coefficientSequenceProjection l E Y n).app
            ((PurStrictScalar.scalarSupportNative l E c S).obj M) ≫
          (coefficientFiniteDerivedRestriction l E Y n).map
            ((PurStrictScalar.scalarSupportEvaluation l E c S n).hom.app M)) = _ at hα
  have hβ' := hβ M n
  have heval : (SY.reductionEvaluation n).inv.app
        ((image (completed l E) c).obj M) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map α ≫
        (PurStrictScalar.scalarSupportEvaluation l E c S n).hom.app M =
      (finiteReductionIso l E Y n).inv.app ((image (completed l E) c).obj M) ≫
        (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M := by
    dsimp only [α]
    with_unfolding_all simp only [Functor.map_comp, Category.assoc]
    erw [hV]
    dsimp only [PurStrictScalar.scalarSupportEvaluation, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hβ'
    try simp only [Category.assoc] at hβ'
    try simp only [Category.assoc]
    erw [reassoc_of% hβ']
    erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  apply (cancel_epi ((finiteReductionIso l E Y n).inv.app
    ((image (completed l E) c).obj M))).1
  have hn := (finiteReductionIso l E Y n).inv.naturality ρ
  erw [← Category.assoc, ← hn, Category.assoc]
  have hc := adjunct_change
    (pbcDerivedScalarAdjunction (projection l E (n + 1) (Nat.le_add_left 1 n) Y))
    (coefficientFiniteAdjunction l E Y n)
    (PurStrictScalar.scalarSupportProjection l E c S n M)
  change (finiteReductionIso l E Y n).inv.app
      ((PurStrictScalar.scalarSupport l E c S).obj M) ≫
      PurStrictScalar.scalarSupportCounit l E c S n M = _ at hc
  erw [hc]
  exact hα.trans heval

end WeilConjectures.PurScalarProjection
