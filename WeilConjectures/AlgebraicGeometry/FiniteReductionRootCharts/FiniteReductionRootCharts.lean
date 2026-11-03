/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePositiveReduction.FiniteReductionPositiveLineComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteReductionCharts.FiniteReductionChartCalculus
import all WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots

/-! # Root-chart interface for finite reduction

The section-normalized root chart is extended by the shared ordered derived
chart calculus. The source chart retains the specified reassociation, shifted
power chart and tensor-unit comparison in that order.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteReductionRootCharts

variable (ell : ℕ) [Fact ell.Prime]
variable (E : Type u) [Field E] [Algebra (Padic ell) E]
  [FiniteDimensional (Padic ell) E]

/-- The power map on root sheaves, with exponent relation
`ell^(n+1) = ell^(n-m) * ell^(m+1)`. -/
def rootPower (m n : ℕ) (hmn : m ≤ n) (X : Scheme.{u}) :
    rootsOfUnitySheaf X (ell ^ (n + 1)) ⟶ rootsOfUnitySheaf X (ell ^ (m + 1)) :=
  FinitePositiveReduction.roots ell X m n hmn

/-- The canonical intrinsic realization comparison of the two root presentations. -/
def intrinsicRootComparison (X : Scheme.{u}) (N : ℕ) :=
  PurityTransport.rootComparison X N

/-- Primitive-root chart on the actual roots-of-unity sheaf.  The section formula
is the canonical map `a ↦ ζ^a`, so the chart is generator-normalized. -/
def primitiveRootChart {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero N] {ζ : k}
    (hζ : IsPrimitiveRoot ζ N) :
    X.constantZMod N ≅ X.rootsOfUnitySheaf N :=
  Scheme.constantZModIsoRootsOfUnitySheaf X N f hζ

/-- The chosen primitive root, restricted to a pro-etale test scheme and then
mapped into the existing sheafification of the roots presheaf. Source: Step 2,
`a ↦ a ⊗ ζ` (blueprint: def-pur-finite-reduction-root-charts). -/
def rootSection {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) {ζ : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1))) (U : X.ProEtᵒᵖ) :=
  let q := (Scheme.ΓSpecIso (.of k)).inv ≫ (U.unop.hom ≫ f).appTop
  let hu := (hζ.isUnit (pow_ne_zero _ (Fact.out : ell.Prime).ne_zero)).map q.hom
  let z : rootsOfUnity (ell ^ (n + 1)) Γ(U.unop.left, ⊤) :=
    ⟨hu.unit, (mem_rootsOfUnity _ _).2 (by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
      change q.hom ζ ^ (ell ^ (n + 1)) = 1
      rw [← map_pow, hζ.pow_eq_one, map_one])⟩
  (toSheafify (Scheme.ProEt.topology X)
    (rootsOfUnityPresheaf X (ell ^ (n + 1)))).app U (ULift.up (Additive.ofMul z))

/-- The actual local pure tensor, formed with the sheaf tensorator. Source:
Step 2, coefficient-root chart (blueprint: def-pur-finite-reduction-root-charts). -/
def pure {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) {ζ : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1))) (U : X.ProEtᵒᵖ)
    (a : (condensedRingObj (twistFiniteRing ell E n) X).obj.obj U) :=
  (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (twistFiniteRing ell E n) X)
    (rootsOfUnitySheaf X (ell ^ (n + 1)))).app U
      (a ⊗ₜ[ℤ] rootSection ell f n hζ U)

/-- A primitive root gives the unique section-normalized coefficient-line chart.
Source: Step 2 (blueprint: def-pur-finite-reduction-root-charts).
Proof: the primitive-root isomorphism identifies the roots sheaf with constant
Z/ell^(n+1). Tensor with the quotient coefficient ring; the annihilator makes
this the regular coefficient module. The map sends a to a tensor ζ; the inverse
sends a tensor ζ^j to aj. Balancing proves both inverse identities and uniqueness
on pure tensors, including the empty scheme. -/
theorem chart_existsUnique {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) {ζ : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1))) :
    ∃! t : (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing ell E n) X))) ≅
      coefficientFiniteTwistOne ell E X n,
      ∀ (U : X.ProEtᵒᵖ)
        (a : (condensedRingObj (twistFiniteRing ell E n) X).obj.obj U),
        t.hom.hom.hom.app U a = pure ell E f n hζ U a := by
  let N := ell ^ (n + 1)
  let R := condensedRingObj (twistFiniteRing ell E n) X
  let q := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let hu := (hζ.isUnit (pow_ne_zero _ (Fact.out : ell.Prime).ne_zero)).map q.hom
  let z : Γ(X, ⊤)ˣ := hu.unit
  have hz : z ^ N = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    change hu.unit.val ^ N = 1
    rw [IsUnit.unit_spec, ← map_pow, hζ.pow_eq_one, map_one]
  have hd : ∀ i < N, ∀ j < N, i ≠ j →
      IsUnit ((z : Γ(X, ⊤)) ^ i - (z : Γ(X, ⊤)) ^ j) := by
    intro i hi j hj hij
    have h : IsUnit (ζ ^ i - ζ ^ j) :=
      isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h ↦ hij (hζ.pow_inj hi hj h)))
    change IsUnit (hu.unit.val ^ i - hu.unit.val ^ j)
    rw [hu.unit_spec, ← map_pow, ← map_pow, ← map_sub]
    exact h.map q.hom
  let b := constantRootsIso (X := X) N z hz hd
  let e : (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) ≅
      coefficientFiniteTwistOne ell E X n :=
    (freeConstantResidueIso R N (finiteRing_nsmul ell E X n)).symm ≪≫
      (Mod.freeFunctor R).mapIso b
  have he : ∀ (U : X.ProEtᵒᵖ) (a : R.obj.obj U),
      e.hom.hom.hom.app U a = pure ell E f n hζ U a := by
    intro U a
    let s : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ rootsOfUnitySheaf X N :=
      Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
        (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.intResidue.{u} N) ≫ b.hom
    have hem : e.hom.hom = (ρ_ R).inv ≫ R ◁ s := by
      change (ρ_ R).inv ≫
        R ◁ (Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1})) ≫
        R ◁ (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.intResidue.{u} N) ≫ R ◁ b.hom = _
      simp only [← whiskerLeft_comp]
      rfl
    have hs : (Functor.LaxMonoidal.ε
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
          (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map s).app U
        (ULift.up.{u + 1} (1 : ℤ)) = rootSection ell f n hζ U := by
      have hh : Functor.LaxMonoidal.ε
          (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
            (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map s =
          (Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.intResidue.{u} N) ≫
            (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).unit.app
              ((Functor.const X.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))) ≫ b.hom.hom := by
        let J := Scheme.ProEt.topology X
        let F := sheafToPresheaf J Ab.{u + 1}
        let L := presheafToSheaf J Ab.{u + 1}
        let c := constantSheaf J Ab.{u + 1}
        let K : Ab.{u + 1} ⥤ X.ProEtᵒᵖ ⥤ Ab.{u + 1} := Functor.const X.ProEtᵒᵖ
        have hc : Functor.LaxMonoidal.ε c = Functor.LaxMonoidal.ε L := by
          have hK : Functor.LaxMonoidal.ε K = 𝟙 _ := by
            ext
            rfl
          change Functor.LaxMonoidal.ε L ≫ L.map (Functor.LaxMonoidal.ε K) = _
          rw [hK, CategoryTheory.Functor.map_id, Category.comp_id]
        have hε : Functor.LaxMonoidal.ε F ≫
            F.map (Functor.LaxMonoidal.ε L) =
              (sheafificationAdjunction J Ab.{u + 1}).unit.app (𝟙_ _) := by
          rw [← (sheafificationAdjunction J Ab.{u + 1}).unit_app_unit_comp_map_η,
            Category.assoc, Functor.Monoidal.map_η_ε]
          exact Category.comp_id _
        change Functor.LaxMonoidal.ε F ≫
          F.map (Functor.LaxMonoidal.ε c ≫ c.map (AddCommGrpCat.intResidue.{u} N) ≫
            b.hom) = _
        rw [hc, Functor.map_comp, Functor.map_comp, ← Category.assoc, hε]
        change _ ≫ _ ≫ b.hom.hom = _
        rw [← Category.assoc]
        exact congrArg (fun t ↦ t ≫ b.hom.hom)
          ((sheafificationAdjunction J Ab.{u + 1}).unit.naturality
            (K.map (AddCommGrpCat.intResidue.{u} N))).symm
      erw [hh]
      have h1 : (AddCommGrpCat.intResidue.{u} N) (ULift.up.{u + 1} (1 : ℤ)) =
          ULift.up.{u + 1} (1 : ZMod N) := by
        apply ULift.ext
        change ((1 : ℤ) : ZMod N) = 1
        exact Int.cast_one
      change b.hom.hom.app U
        (((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).unit.app
          _).app U ((AddCommGrpCat.intResidue.{u} N) (ULift.up.{u + 1} (1 : ℤ)))) = _
      rw [h1]
      have hn := (sheafificationAdjunction (Scheme.ProEt.topology X)
        Ab.{u + 1}).unit.naturality (zmodToRootsPresheaf X N z hz)
      have hn' := congrArg (fun t ↦ t.app U (ULift.up.{u + 1} (1 : ZMod N))) hn.symm
      change b.hom.hom.app U _ = _ at hn'
      erw [hn']
      change (toSheafify (Scheme.ProEt.topology X) (rootsOfUnityPresheaf X N)).app U
        ((zmodToRootsPresheaf X N z hz).app U (ULift.up.{u + 1} (1 : ZMod N))) = _
      congr 1
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      have hzv := zmodToRootsPresheaf_app_natCast (X := X) N z hz U 1
      change ((zmodToRootsPresheaf X N z hz).app U
        (ULift.up (1 : ZMod N))).down.toMul.val.val = _
      have hzv' : ((zmodToRootsPresheaf X N z hz).app U
          (ULift.up (1 : ZMod N))).down.toMul.val.val =
          U.unop.hom.appTop (z : Γ(X, ⊤)) := by
        simpa only [Nat.cast_one, pow_one] using hzv
      exact hzv'.trans (by
        let qU := (Scheme.ΓSpecIso (.of k)).inv ≫ (U.unop.hom ≫ f).appTop
        let huU := (hζ.isUnit (pow_ne_zero _ (Fact.out : ell.Prime).ne_zero)).map qU.hom
        change U.unop.hom.appTop.hom hu.unit.val = huU.unit.val
        rw [hu.unit_spec, huU.unit_spec]
        simp only [qU, q, Scheme.Hom.comp_appTop]
        rfl)
    change ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map e.hom.hom).app U a = _
    erw [hem, (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map_comp,
      ← Functor.LaxMonoidal.right_unitality_inv
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R]
    simp only [Category.assoc]
    erw [← Functor.LaxMonoidal.μ_natural_right, ← whiskerLeft_comp_assoc]
    change (Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
        (rootsOfUnitySheaf X N)).app U
      (a ⊗ₜ[ℤ] ((Functor.LaxMonoidal.ε
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
          (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map s).app U
            (ULift.up.{u + 1} (1 : ℤ)))) = _
    rw [hs]
    rfl
  refine ⟨e, he, ?_⟩
  intro t ht
  apply Iso.ext
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  ext U a
  exact (ht U a).trans (he U a).symm

/-- The unique chart, with inverse given by the primitive-root coordinate.
Source: Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def chart {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) {ζ : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1))) :=
  (chart_existsUnique ell E f n hζ).exists.choose

/-- The canonical single-object tensor comparison when the second factor is a
root-trivialized line. Transport the single-object unit comparison through the
line chart on both sides; the chart and its inverse cancel by naturality.
Source: Step 2, ordinary/derived tensor comparison for the finite root line
(blueprint: def-pur-finite-reduction-root-charts). -/
def singleTensorViaUnit (X : Scheme.{u}) (n : ℕ)
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing ell E n) X)) (e : B ≅ 𝟙_ _) :
    (DerivedCategory.singleFunctor _ 0).obj (A ⊗ B) ≅
      (DerivedCategory.singleFunctor _ 0).obj A ⊗
        (DerivedCategory.singleFunctor _ 0).obj B :=
  (DerivedCategory.singleFunctor _ 0).mapIso (tensorIso (Iso.refl A) e ≪≫ ρ_ A) ≪≫
    (ρ_ ((DerivedCategory.singleFunctor _ 0).obj A)).symm ≪≫
      tensorIso (Iso.refl _) ( (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e.symm)

/-- The shifted positive power chart is the shared chart-calculus recursion with
B(r)=A_n(r)[2r] and L=A_n(1)[2]. Its successor presentation is the canonical
single-object tensor comparison followed by the inverse tensor-shift comparison.
Source: Step 2, the ordered tensor/shift factors
(blueprint: def-pur-finite-reduction-root-charts). -/
def shiftedPowerChart {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) {ζ : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1))) (d : ℕ) :
    (FinitePositiveReduction.single ell E X n d 0)⟦2 * (d : ℤ)⟧ ≅
      (𝟙_ _)⟦2 * (d : ℤ)⟧ :=
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (twistFiniteRing ell E n) X)
  let e : FinitePositiveReduction.line ell E X n 1 ≅ 𝟙_ C :=
    λ_ (coefficientFiniteTwistOne ell E X n) ≪≫ (chart ell E f n hζ).symm
  CondensedRing.FiniteReductionCharts.powerChart (twistFiniteRing ell E n) X
    (fun r ↦ (FinitePositiveReduction.single ell E X n r 0)⟦2 * (r : ℤ)⟧)
    ((FinitePositiveReduction.single ell E X n 1 0)⟦(2 : ℤ)⟧)
    ((shiftFunctor _ (2 * ((0 : ℕ) : ℤ))).mapIso
      (DerivedCategory.singleFunctorObjUnitIso C))
    ((shiftFunctor _ (2 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor C 0).mapIso e ≪≫
        DerivedCategory.singleFunctorObjUnitIso C))
    (fun r ↦
      (eqToIso (congrArg (shiftFunctor (DerivedCategory C))
        (by simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] :
          2 * ((r + 1 : ℕ) : ℤ) = 2 * (r : ℤ) + 2))).app _ ≪≫
      (shiftFunctor _ (2 * (r : ℤ) + 2)).mapIso
        ((DerivedCategory.singleFunctor C 0).mapIso
          (tensorIso (Iso.refl (FinitePositiveReduction.line ell E X n r))
            (λ_ (coefficientFiniteTwistOne ell E X n)).symm) ≪≫
          singleTensorViaUnit ell E X n _ _ e) ≪≫
      (DerivedCategory.shiftTensorShiftIso C
        (FinitePositiveReduction.single ell E X n r 0)
        (FinitePositiveReduction.single ell E X n 1 0) (2 * (r : ℤ)) 2).symm)
    d

/-- The specified three-factor source chart: reassociate K(d)[2d] as
K tensor A_n(d)[2d], tensor the ordered shifted power chart, then apply the
shared tensor-unit shift comparison. Only roots, tensor and shifts are used.
Source: Step 2, exact source reassociation
(blueprint: def-pur-finite-reduction-root-charts). -/
def sourceChart {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) {ζ : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing ell E n) X))) (d : ℕ) :
    ((coefficientFiniteTwistFunctor ell E X n (d : ℤ)).obj M)⟦2 * (d : ℤ)⟧ ≅
      M⟦2 * (d : ℤ)⟧ :=
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (twistFiniteRing ell E n) X)
  letI := DerivedCategory.commShiftTensorLeft C M
  ((((curriedTensor (DerivedCategory C)).obj M).commShiftIso
      (2 * (d : ℤ))).app (FinitePositiveReduction.single ell E X n d 0)).symm ≪≫
    ((CondensedRing.derivedTensor (twistFiniteRing ell E n) X).obj M).mapIso
      (shiftedPowerChart ell E f n hζ d) ≪≫
    CondensedRing.FiniteReductionCharts.tensorUnit (twistFiniteRing ell E n) X M
      (2 * (d : ℤ))

end AlgebraicGeometry.ProEtale.FiniteReductionRootCharts
