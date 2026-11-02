/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Positive.FinitePositiveRootCharts
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonPureSections

/-! # The integral root tensor of a chart unit

Source: finite reduction of purity, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Functor.LaxMonoidal
namespace WeilConjectures.PurityFiniteSetting

set_option maxHeartbeats 2000000 in
-- Comparing the two native derived-unit constructions requires substantial kernel reduction.
private theorem first_chart_formula (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteTensorFirstSheafChart T ζ hζ =
      (P.finiteTensorFirstSiteLine T).symm ≪≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapIso
          (P.finiteReductionRootTrivialization T ζ hζ).symm ≪≫
        (Functor.Monoidal.εIso (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T)).symm := by
  have he : Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) T =
      _root_.DerivedCategory.singleFunctorObjUnitIso
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) := by
    apply Iso.ext
    simp only [Etale.singleFunctorObjUnitIso, Etale.singleFunctorObjIsoQh,
      _root_.DerivedCategory.singleFunctorObjUnitIso, Iso.trans_hom, Category.assoc]
  apply (P.existsUnique_finiteTensorFirstSheafChart T ζ hζ).unique
  · exact (P.existsUnique_finiteTensorFirstSheafChart T ζ hζ).exists.choose_spec
  · apply heq_of_eq
    unfold finiteTensorSingleUnitChart finiteTensorFirstChart
    ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp]
    let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
    let σ := _root_.DerivedCategory.singleFunctor
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0
    let α := F.mapDerivedCategorySingleFunctor 0
    let s := P.finiteTensorFirstSiteLine T
    let r := P.finiteReductionRootTrivialization T ζ hζ
    let η := Functor.OplaxMonoidal.η F
    let e := _root_.DerivedCategory.singleFunctorObjUnitIso
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
    suffices h : σ.map s.inv ≫ σ.map (F.map r.inv) ≫ σ.map η ≫ e.hom =
      σ.map s.inv ≫ σ.map (F.map r.inv) ≫
        α.inv.app (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) ≫
        α.hom.app (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) ≫
        σ.map η ≫ e.hom by
      simp only [Functor.Monoidal.εIso_inv, Category.assoc, Functor.comp_obj,
        Iso.app_hom, Iso.symm_hom, finiteReductionComparisonUnitChart,
        smoothPurityUnitIso, he, finiteReductionDerivedUnitGeneric, Functor.mapIso_symm,
        Iso.self_symm_id_assoc, Iso.trans_hom, Functor.mapIso_inv]
      exact h
    rw [Iso.inv_hom_id_app_assoc]

private theorem root_section_value (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (W : T.Etaleᵒᵖ) :
    (finiteTateEtaleRootValue T P.diagonalExponent W
      (P.finiteReductionRootSection T ζ hζ W) : Γ(W.unop.left, ⊤)) =
      ((ΓSpecIso (.of P.field.k)).inv ≫
        (W.unop.hom ≫ (T ↘ Spec (.of P.field.k))).appTop).hom ζ := by
  classical
  let f := T ↘ Spec (.of P.field.k)
  let ρ : P.field.k →+* Γ(T, ⊤) := ((ΓSpecIso (.of P.field.k)).inv ≫ f.appTop).hom
  let hu := (hζ.isUnit (NeZero.ne P.diagonalExponent)).map ρ
  have hp : hu.unit ^ P.diagonalExponent = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hζ.pow_eq_one,
      map_one, Units.val_one])
  have hh := kernel.lift_ι (P.diagonalExponent • 𝟙 T.gmSheaf)
    (T.constantZModToGmSheaf P.diagonalExponent hu.unit hp)
    (T.constantZModToGmSheaf_comp_nsmul P.diagonalExponent hu.unit hp)
  have hfac : toSheafify _ _ ≫
      (T.constantZModToRootsOfUnitySheaf P.diagonalExponent hu.unit hp).hom ≫
      (kernel.ι (P.diagonalExponent • 𝟙 T.gmSheaf)).hom =
      T.zmodToGmPresheaf P.diagonalExponent hu.unit hp := by
    have hh' : T.constantZModToRootsOfUnitySheaf P.diagonalExponent hu.unit hp ≫
        kernel.ι (P.diagonalExponent • 𝟙 T.gmSheaf) =
        T.constantZModToGmSheaf P.diagonalExponent hu.unit hp := hh
    exact (congrArg (fun g ↦ toSheafify _ _ ≫ g.hom) hh').trans
      (T.toSheafify_constantZModToGmSheaf P.diagonalExponent hu.unit hp)
  have hv := ConcreteCategory.congr_hom (NatTrans.congr_app hfac W)
    (ULift.up (1 : ZMod P.diagonalExponent))
  have he := congrArg (fun z ↦ ((Additive.toMul z.down : Γ(W.unop.left, ⊤)ˣ) :
    Γ(W.unop.left, ⊤))) hv
  change (finiteTateEtaleRootValue T P.diagonalExponent W
    (P.finiteReductionRootSection T ζ hζ W) : Γ(W.unop.left, ⊤)) = _ at he
  calc
    _ = _ := he
    _ = W.unop.hom.appTop (hu.unit : Γ(T, ⊤)) := by
      have hval := T.zmodToGmPresheaf_app_natCast P.diagonalExponent hu.unit hp W 1
      simp only [Nat.cast_one, pow_one] at hval
      exact hval
    _ = _ := by rw [IsUnit.unit_spec]; rfl

private theorem comparison_unit_section (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop)
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (q : (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) ⟶ L) (a : A) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj L).obj.map f.op
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app L).hom.app U
        (q.hom.app U ((ε (sheafToPresheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} A))).app U a))) =
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).map q).hom.app W
      ((ε (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)).hom.app W
        ((ε (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A))).app W a)) := by
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let adj := ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T
  have hu := (comparison_pure_sections A T).2 U W f a
  have hi := congrArg (fun g ↦ g.hom.app W) (Functor.Monoidal.η_ε F)
  have hu' : (F.obj (𝟙_ _)).obj.map f.op
      ((adj.unit.app (𝟙_ _)).hom.app U
        ((ε (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).app U a)) =
      (ε F).hom.app W
        ((ε (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A))).app W a) := by
    have hv := ConcreteCategory.congr_hom hi
      ((F.obj (𝟙_ _)).obj.map f.op
        ((adj.unit.app (𝟙_ _)).hom.app U
          ((ε (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).app U a)))
    change (ε F).hom.app W ((Functor.OplaxMonoidal.η F).hom.app W _) = _ at hv
    exact hv.symm.trans (congrArg ((ε F).hom.app W) hu)
  have hn := congrArg (fun g ↦ g.hom.app U
      ((ε (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).app U a))
    (adj.unit.naturality q)
  change (adj.unit.app L).hom.app U (q.hom.app U _) =
    (F.map q).hom.app ((toProEt T).op.obj U) ((adj.unit.app _).hom.app U _) at hn
  rw [hn]
  have hnq := ConcreteCategory.congr_hom ((F.map q).hom.naturality f.op)
    ((adj.unit.app (𝟙_ _)).hom.app U
      ((ε (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).app U a))
  simp only [ModuleCat.comp_apply] at hnq
  exact hnq.symm.trans (congrArg ((F.map q).hom.app W) hu')

set_option maxHeartbeats 2000000 in
-- The finite-level realization and scalar-extension encodings are compared definitionally.
/-- A root lift identifies a first-chart unit section with its integral pure tensor.
Source: finite reduction of purity, Step 2; the finite Tate site comparison in Step 8.
(blueprint: lem-pur-finite-tensor-first-sheaf-chart-unit-root-tensor)
Proof: first write the positive level as its predecessor plus one. The defining
normalization of the first site line identifies it with finite_tate_site_descent
followed by the inverse fixed-root realization. The normalized first sheaf chart
is the ordinary lift of exactly this single-complex chart; full faithfulness of
the single functor cancels its derived unit and comparison-single isomorphisms.
The primitive-root trivialization takes coefficient one to its prescribed root
section. The finite Tate site comparison takes this section to the pure tensor
of any root-tower lift having that underlying unit, by its generator formula.
The fixed-root counit formula identifies the result with finiteTensorSection.
Finally the tensor defining finiteTateProGenerator is precisely the scalar
extension of purTwistIntegralTensor with both scalar factors one. Transport only
the equality (level-1)+1=level; this is the displayed heterogeneous equality.
The same normalization and separatedness apply to empty tests and the zero ring. -/
theorem finiteTensorFirstSheafChart_unit_root_tensor
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (V : T.ProEt)
    (t : (purTwistZlOne T P.coefficients.l).obj.obj (Opposite.op V))
    (ht : (finiteTateLimitRootValue P.coefficients.l T (P.level - 1)
        (Opposite.op V) t : Γ(V.left, ⊤)) =
      ((ΓSpecIso (.of P.field.k)).inv ≫
        (V.hom ≫ (T ↘ Spec (.of P.field.k))).appTop).hom ζ)
    (x : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
    (hx : (P.finiteTensorFirstSheafChart T ζ hζ).hom.hom.app (Opposite.op V) x =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)) :
    HEq (P.finiteTensorSection T 1 V x)
      (SheafOfModules.scalarExtensionSection (P.finiteTensorIntegralMap T)
        (purTwistIntegralOne T P.coefficients.l P.extension) (Opposite.op V) 1
        (purTwistIntegralTensor T P.coefficients.l P.extension (Opposite.op V) 1 t)) := by
  classical
  cases P with
  | mk F C E level hlevel =>
    cases level with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hlevel)
    | succ n =>
      let P : PurityFiniteSetting.{u} := ⟨F, C, E, n + 1, hlevel⟩
      let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
      let e := P.finiteTensorFirstSheafChart T ζ hζ
      let s := P.finiteTensorFirstSiteLine T
      let r := P.finiteReductionRootTrivialization T ζ hζ
      let u₁ := (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient)
      have hxe : x = e.inv.hom.app (Opposite.op V) u₁ := by
        have h := congrArg (fun f ↦ f.hom.app (Opposite.op V)) e.hom_inv_id
        have hv := ConcreteCategory.congr_hom h x
        change e.inv.hom.app (Opposite.op V)
          (e.hom.hom.app (Opposite.op V) x) = x at hv
        exact hv.symm.trans (congrArg (e.inv.hom.app (Opposite.op V)) hx)
      have hchart := first_chart_formula P T ζ hζ
      have hxi : e.inv.hom.app (Opposite.op V) u₁ =
          s.hom.hom.app (Opposite.op V)
            ((ν.map r.hom).hom.app (Opposite.op V)
              ((Functor.LaxMonoidal.ε ν).hom.app (Opposite.op V) u₁)) := by
        change (P.finiteTensorFirstSheafChart T ζ hζ).inv.hom.app _ _ = _
        rw [hchart]
        rfl
      let U : T.Etale := Etale.mk (𝟙 T)
      let f : V ⟶ (toProEt T).obj U :=
        MorphismProperty.Over.homMk V.hom (Category.comp_id _)
      have hr := (P.existsUnique_finiteReductionRootTrivialization T ζ hζ).choose_spec.1
        (Opposite.op U) (1 : P.Coefficient)
      have hcomparison := comparison_unit_section P.Coefficient T (Opposite.op U)
        (Opposite.op V) f _ r.hom (1 : P.Coefficient)
      have hroot : finiteTateLimitRootValue P.coefficients.l T n (Opposite.op V) t =
          Units.map f.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T P.diagonalExponent (Opposite.op U)
              (P.finiteReductionRootSection T ζ hζ (Opposite.op U))) := by
        apply Units.ext
        have he := root_section_value P T ζ hζ (Opposite.op U)
        change _ = f.left.appTop.hom _
        rw [he]
        exact ht
      have hdescent := (finite_tate_site_descent P.coefficients.l P.extension n).choose_spec.1
        T (P.finiteTensorPrimeIsUnit T) n P.diagonalExponent_annihilates 1
        (Opposite.op U) (Opposite.op V) f (1 : P.Coefficient)
        (fun _ ↦ P.finiteReductionRootSection T ζ hζ (Opposite.op U)) (fun _ ↦ t)
        (fun _ ↦ hroot)
      have hsite : P.finiteTensorFirstSiteLine T =
          (finite_tate_site_descent P.coefficients.l P.extension n).choose T
            (P.finiteTensorPrimeIsUnit T) n P.diagonalExponent_annihilates 1 ≪≫
              (sfOrientationFixedRootSheaf_existsUnique
                P.coefficients.l P.extension T n 1).exists.choose.symm :=
        eq_of_heq ((P.existsUnique_finiteTensorFirstSiteLine T).exists.choose_spec n rfl)
      rw [hxe, hxi]
      have hcs : (ν.map r.hom).hom.app (Opposite.op V)
          ((Functor.LaxMonoidal.ε ν).hom.app (Opposite.op V) u₁) =
          ((ν.obj (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
            P.diagonalExponent_annihilates)).obj.map f.op
              (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
                (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
                  P.diagonalExponent_annihilates)).hom.app (Opposite.op U)
                (finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
                  P.diagonalExponent_annihilates (Opposite.op U) 1
                  (P.finiteReductionRootSection T ζ hζ (Opposite.op U))))) := by
        refine hcomparison.symm.trans ?_
        exact congrArg (fun z ↦
          (ν.obj (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
            P.diagonalExponent_annihilates)).obj.map f.op
              (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
                (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
                  P.diagonalExponent_annihilates)).hom.app (Opposite.op U) z)) hr
      rw [hcs]
      let k := (sfOrientationFixedRootSheaf_existsUnique
        P.coefficients.l P.extension T n 1).exists.choose
      have hgenerator : s.hom.hom.app (Opposite.op V)
          ((ν.obj (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
            P.diagonalExponent_annihilates)).obj.map f.op
              (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
                (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
                  P.diagonalExponent_annihilates)).hom.app (Opposite.op U)
                (finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
                  P.diagonalExponent_annihilates (Opposite.op U) 1
                  (P.finiteReductionRootSection T ζ hζ (Opposite.op U))))) =
          k.inv.hom.app (Opposite.op V)
            (finiteTateProGenerator P.coefficients.l P.extension n T (Opposite.op V) 1 t) := by
        have hs := congrArg (fun q : P.FiniteTensorFirstSiteLineType T ↦
          q.hom.hom.app (Opposite.op V)
            ((ν.obj (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates)).obj.map f.op
                (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
                  (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
                    P.diagonalExponent_annihilates)).hom.app (Opposite.op U)
                  (finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
                    P.diagonalExponent_annihilates (Opposite.op U) 1
                    (P.finiteReductionRootSection T ζ hζ (Opposite.op U)))))) hsite
        exact hs.trans (congrArg (k.inv.hom.app (Opposite.op V)) hdescent)
      rw [hgenerator]
      have hk := (sfOrientationFixedRootSheaf_existsUnique
        P.coefficients.l P.extension T n 1).exists.choose_spec (Opposite.op V)
          (finiteTateProGenerator P.coefficients.l P.extension n T (Opposite.op V) 1 t)
      refine (heq_of_eq hk).trans ?_
      apply heq_of_eq
      unfold finiteTateProGenerator SheafOfModules.scalarExtensionSection
      simp only [map_one]
      rfl

end WeilConjectures.PurityFiniteSetting
