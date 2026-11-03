/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData

/-! # Normalized coefficient comparisons: one component of the coherence argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem left_of_action
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Fj : B ⥤ D) (FΩ : E ⥤ H)
    (TX : A ⥤ B) (TY : C ⥤ D) (IXi : A ⥤ E) (IXj : B ⥤ E)
    (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY ≅ TX ⋙ Fj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi)
    (h : representativeAction Fi Fj FΩ TX TY IXi IXj IYi IYj q qi qj tauX tauY)
    (K : A) :
    IYj.map (q.hom.app K) ≫ qj.hom.app (TX.obj K) =
      tauY.hom.app (Fi.obj K) ≫ qi.hom.app K ≫ FΩ.map (tauX.inv.app K) := by
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at *
  have hh := h K (TX.obj K) (𝟙 _)
  change FΩ.map (tauX.inv.app K ≫ IXj.map (𝟙 (TX.obj K))) =
    qi.inv.app K ≫ tauY.inv.app (Fi.obj K) ≫ IYj.map (q.hom.app K) ≫
      IYj.map (Fj.map (𝟙 (TX.obj K))) ≫ qj.hom.app (TX.obj K) at hh
  rw [IXj.map_id, Fj.map_id] at hh
  dsimp only [Functor.comp_obj] at hh
  rw [IYj.map_id] at hh
  simp only [Category.comp_id, Category.id_comp] at hh
  rw [hh]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem right_of_left
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Gi : C ⥤ A) (Fj : B ⥤ D) (Gj : D ⥤ B)
    (FΩ : E ⥤ H) (GΩ : H ⥤ E)
    (ai : Fi ⊣ Gi) (aj : Fj ⊣ Gj) (ao : FΩ ⊣ GΩ)
    (TX : A ⥤ B) (TY : C ⥤ D) (IXi : A ⥤ E) (IXj : B ⥤ E)
    (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY ≅ TX ⋙ Fj) (b : Gi ⋙ TX ≅ TY ⋙ Gj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (bi : Gi ⋙ IXi ≅ IYi ⋙ GΩ) (bj : Gj ⋙ IXj ≅ IYj ⋙ GΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi)
    (hc : ∀ L, q.hom.app (Gi.obj L) ≫ Fj.map (b.hom.app L) ≫
      aj.counit.app (TY.obj L) = TY.map (ai.counit.app L))
    (hi : ∀ L, qi.hom.app (Gi.obj L) ≫ FΩ.map (bi.hom.app L) ≫
      ao.counit.app (IYi.obj L) = IYi.map (ai.counit.app L))
    (hj : ∀ L, qj.hom.app (Gj.obj L) ≫ FΩ.map (bj.hom.app L) ≫
      ao.counit.app (IYj.obj L) = IYj.map (aj.counit.app L))
    (hact : representativeAction Fi Fj FΩ TX TY IXi IXj IYi IYj q qi qj tauX tauY) (L : C) :
    IXj.map (b.hom.app L) ≫ bj.hom.app (TY.obj L) =
      tauX.hom.app (Gi.obj L) ≫ bi.hom.app L ≫ GΩ.map (tauY.inv.app L) := by
  have hl := left_of_action Fi Fj FΩ TX TY IXi IXj IYi IYj q qi qj tauX tauY hact
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at *
  apply (ao.homEquiv _ _).symm.injective
  change FΩ.map _ ≫ ao.counit.app _ = FΩ.map _ ≫ ao.counit.app _
  let Q := IYj.mapIso (q.app (Gi.obj L)) ≪≫ qj.app (TX.obj (Gi.obj L))
  apply (cancel_epi Q.hom).1
  dsimp only [Q, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  have hn := qj.hom.naturality (b.hom.app L)
  dsimp only [Functor.comp_map] at hn
  have ht := tauY.hom.naturality (ai.counit.app L)
  dsimp only [Functor.comp_map] at ht
  calc
    _ = IYj.map (q.hom.app (Gi.obj L)) ≫ IYj.map (Fj.map (b.hom.app L)) ≫
        qj.hom.app (Gj.obj (TY.obj L)) ≫ FΩ.map (bj.hom.app (TY.obj L)) ≫
        ao.counit.app (IYj.obj (TY.obj L)) := by rw [reassoc_of% hn]
    _ = IYj.map (q.hom.app (Gi.obj L)) ≫ IYj.map (Fj.map (b.hom.app L)) ≫
        IYj.map (aj.counit.app (TY.obj L)) := by rw [hj (TY.obj L)]
    _ = IYj.map (TY.map (ai.counit.app L)) := by
      rw [← IYj.map_comp, ← IYj.map_comp, hc L]
    _ = tauY.hom.app (Fi.obj (Gi.obj L)) ≫ IYi.map (ai.counit.app L) ≫
        tauY.inv.app L := by
      rw [← reassoc_of% ht]
      simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
    _ = tauY.hom.app (Fi.obj (Gi.obj L)) ≫ qi.hom.app (Gi.obj L) ≫
        FΩ.map (bi.hom.app L) ≫ ao.counit.app (IYi.obj L) ≫ tauY.inv.app L := by
      simpa only [Category.assoc, Functor.comp_obj] using
        congrArg (fun z => tauY.hom.app (Fi.obj (Gi.obj L)) ≫ z ≫ tauY.inv.app L)
          (hi L).symm
    _ = tauY.hom.app (Fi.obj (Gi.obj L)) ≫ qi.hom.app (Gi.obj L) ≫
        FΩ.map (bi.hom.app L) ≫ FΩ.map (GΩ.map (tauY.inv.app L)) ≫
        ao.counit.app (IYj.obj (TY.obj L)) := by
      simpa only [Category.assoc, Functor.comp_obj] using
        congrArg (fun z => tauY.hom.app (Fi.obj (Gi.obj L)) ≫ qi.hom.app (Gi.obj L) ≫
          FΩ.map (bi.hom.app L) ≫ z) (ao.counit_naturality (tauY.inv.app L)).symm
    _ = _ := by
      rw [reassoc_of% (hl (Gi.obj L))]
      dsimp only [Functor.comp_obj]
      have htau := (FΩ.mapIso (tauX.app (Gi.obj L))).inv_hom_id
      change FΩ.map (tauX.inv.app (Gi.obj L)) ≫
        FΩ.map (tauX.hom.app (Gi.obj L)) = 𝟙 _ at htau
      rw [reassoc_of% htau]

private theorem field_counit
    {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t}
    {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY) (L : C.{u, v} l Ω Y s) :
    d.q.hom.app (A.G.obj L) ≫ B.F.map (d.b.hom.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L) := by
  let := d.shiftX
  let := d.shiftY
  exact d.comparison.counit L

/-- The left common-stage equation, retaining the literal equality transports.
Source: common-stage coefficient compatibility
(blueprint: lem-sf-normalized-common-coefficient-laws). -/
def normalizedCommonLeft (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) : Prop :=
    ∀ (c : Compactification f) (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))),
    HEq ((commonInclusion.{u, v} l Ω Y j).map
      ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app K) ≫
      (M.commonComparison c j).q.hom.app
        ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X i j h).obj K))
      ((commonTransition.{u, v} l Ω Y i j h).hom.app
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K) ≫
      (M.commonComparison c i).q.hom.app K ≫ (R.operation c .closed).F.map
        ((commonTransition.{u, v} l Ω X i j h).inv.app K))

/-- The right common-stage equation, retaining the literal equality transports.
Source: common-stage coefficient compatibility
(blueprint: lem-sf-normalized-common-coefficient-laws). -/
def normalizedCommonRight (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl R F) : Prop :=
    ∀ (c : Compactification f) (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (L : C.{u, v} l Ω Y (.rational (commonField.{u, v} l Ω i))),
    HEq ((commonInclusion.{u, v} l Ω X j).map
      ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).b.hom.app L) ≫
      (M.commonComparison c j).b.hom.app
        ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y i j h).obj L))
      ((commonTransition.{u, v} l Ω X i j h).hom.app
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).G.obj L) ≫
      (M.commonComparison c i).b.hom.app L ≫ (R.operation c .closed).G.map
        ((commonTransition.{u, v} l Ω Y i j h).inv.app L))

/-- The common representative formula transports the finite-field coefficient mates.
Source: exceptional inverse image, common-stage construction, Steps 6--7
(blueprint: lem-sf-normalized-common-coefficient-laws).
-/
theorem normalized_common_coefficient_laws (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    (M : CoefficientConstructionCommon.{u, v} l Ω D hl (X := X) (Y := Y) R F) :
    normalizedCommonLeft.{u, v} l Ω D hl (f := f) R F M ∧
      normalizedCommonRight.{u, v} l Ω D hl (f := f) R F M := by
  have left (c : Compactification f) (i j : AlgebraicallyClosedCoefficients.Index l Ω)
      (h : i ≤ j) (K : C.{u, v} l Ω X (.rational (commonField l Ω i))) :=
    left_of_action _ _ _ _ _ _ _ _ _ _ _ _ _ _ (M.common_morphism_normalized c i j h) K
  constructor
  · intro c i j h K
    exact heq_of_eq (left c i j h K)
  · intro c i j h L
    let a := F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
    let := a.shiftX
    let := a.shiftY
    let := (M.commonComparison c i).shiftX
    let := (M.commonComparison c i).shiftY
    let := (M.commonComparison c j).shiftX
    let := (M.commonComparison c j).shiftY
    let Fi := (R.operation c (.rational (commonField l Ω i))).F
    let Gi := (R.operation c (.rational (commonField l Ω i))).G
    let Fj := (R.operation c (.rational (commonField l Ω j))).F
    let Gj := (R.operation c (.rational (commonField l Ω j))).G
    let Fo := (R.operation c .closed).F
    let Go := (R.operation c .closed).G
    let TX := rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X
    let TY := rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y
    have hr := right_of_left
      (A := C.{u, v} l Ω X (.rational (commonField l Ω i)))
      (B := C.{u, v} l Ω X (.rational (commonField l Ω j)))
      (C := C.{u, v} l Ω Y (.rational (commonField l Ω i)))
      (D := C.{u, v} l Ω Y (.rational (commonField l Ω j)))
      (E := C.{u, v} l Ω X .closed) (H := C.{u, v} l Ω Y .closed)
      Fi Gi Fj Gj Fo Go
      (R.operation c (.rational (commonField l Ω i))).adjunction
      (R.operation c (.rational (commonField l Ω j))).adjunction
      (R.operation c .closed).adjunction TX TY
      (commonInclusion l Ω X i) (commonInclusion l Ω X j)
      (commonInclusion l Ω Y i) (commonInclusion l Ω Y j)
      a.q a.b (M.commonComparison c i).q (M.commonComparison c j).q
      (M.commonComparison c i).b (M.commonComparison c j).b
      (commonTransition l Ω X i j h) (commonTransition l Ω Y i j h)
      (field_counit l Ω a) (field_counit l Ω (M.commonComparison c i))
      (field_counit l Ω (M.commonComparison c j))
      (M.common_morphism_normalized c i j h) L
    exact heq_of_eq hr

end WeilConjectures.ConstructibleExceptionalCoefficients
