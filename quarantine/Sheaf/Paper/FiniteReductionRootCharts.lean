/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionChartCalculus
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
def-pur-finite-reduction-root-charts (blueprint: def-pur-finite-reduction-root-charts).

## Main definitions

- `finiteReduction`: the actual quotient scalar extension.
- `finiteReductionRootTrivialization`: the section-normalized root-line chart.
- `finiteReductionSourceTrivialization`: the shifted purity-source chart.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
private theorem existsUnique_heq {α β : Type v} (e : α = β) (b : β) :
    ∃! a : α, HEq a b := by
  subst β
  exact ⟨b, HEq.rfl, fun a h ↦ eq_of_heq h⟩

/-- The ordered composite of the reassociation, root, and tensor-unit factors.
Source: blueprint finite-reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionChartComposite (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M B : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) (r : ℤ)
    (b : B ≅ (𝟙_ (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))))⟦r⟧) :=
  smoothPurityTensorShift A X r M B ≪≫
    ((smoothPurityTensor A X).obj M).mapIso b ≪≫
      finiteReductionTensorUnit (ModuleCat.{u + 1} A) X M r

private theorem finiteReductionChartComposite_normalized
    {C : Type v} [Category.{w} C] (F : C ⥤ C) {U V B D : C}
    (f : U ≅ F.obj B) (b : B ≅ D) (g : F.obj D ≅ V) (a : U ≅ V) :
    (∃ i₀ : U ≅ F.obj B, ∃ i₁ : F.obj B ≅ F.obj D, ∃ i₂ : F.obj D ≅ V,
      HEq i₀ f ∧ (∃ c : B ≅ D, HEq c b ∧ HEq i₁ (F.mapIso c)) ∧
      HEq i₂ g ∧ HEq a (i₀ ≪≫ i₁ ≪≫ i₂)) ↔ HEq a (f ≪≫ F.mapIso b ≪≫ g) := by
  constructor
  · rintro ⟨i₀, i₁, i₂, h₀, ⟨c, hc, h₁⟩, h₂, ha⟩
    have e₀ := eq_of_heq h₀
    have ec := eq_of_heq hc
    have e₁ := eq_of_heq h₁
    have e₂ := eq_of_heq h₂
    subst i₀ c i₁ i₂
    exact ha
  · intro h
    exact ⟨_, _, _, HEq.rfl, ⟨b, HEq.rfl, HEq.rfl⟩, HEq.rfl, h⟩

private theorem rootTrivializationOfConstantIso (A : Type (u + 1)) [CommRing A] (N : ℕ) [NeZero N]
    (hA : (N : A) = 0) (T : Scheme.{u})
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A)]
    (θ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N) :
    ∃! t : Etale.ordinaryFiniteConstant A T ≅ Scheme.finiteEtaleTateLine T N A hA,
      ∀ (W : T.Etaleᵒᵖ) (a : A),
        t.hom.hom.app W ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a) =
        Scheme.finiteEtaleTateOneGenerator A N T hA W a
          (θ.hom.hom.app W ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1))) := by
  let J := T.smallEtaleTopology
  let C := Etale.ordinaryFiniteConstant A T
  let L := Scheme.finiteEtaleTateLine T N A hA
  let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  let F := sheafCompose J U
  let Z := (Functor.const T.Etaleᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))
  let η := toSheafify J Z
  let v := Etale.ordinaryFiniteRootMap A N hA T
  let s (W : T.Etaleᵒᵖ) : L.obj.obj W :=
    v.hom.app W (θ.hom.hom.app W (η.app W (ULift.up 1)))
  have hs {W V : T.Etaleᵒᵖ} (f : W ⟶ V) : L.obj.map f (s W) = s V := by
    exact (NatTrans.naturality_apply (η ≫ θ.hom.hom ≫ v.hom) f (ULift.up 1)).symm
  let α₀ : (Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A) ⟶ L.obj :=
    { app := fun W ↦ ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight (s W))
      naturality := by
        intro W V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change a • s V = L.obj.map f (a • s W)
        rw [map_smul, hs] }
  let α : C ⟶ L := ⟨sheafifyLift J α₀ L.property⟩
  have hα (W : T.Etaleᵒᵖ) (a : A) :
      α.hom.app W ((toSheafify J
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a) = a • s W := by
    exact congrArg (fun f ↦ f.app W a) (toSheafify_sheafifyLift J α₀ L.property)
  let r := Scheme.finiteEtaleTwistScalar N A hA
  let j₀ : Z ⟶ (F.obj C).obj :=
    { app := fun W ↦ AddCommGrpCat.ofHom
        (((U.map ((toSheafify J
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W)).hom).comp
          (r.toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom))
      naturality := by
        intro W V f
        ext z
        exact NatTrans.naturality_apply (toSheafify J
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))) f (r z.down) }
  let j : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj Z ⟶ F.obj C :=
    ⟨sheafifyLift J j₀ (F.obj C).property⟩
  let ρ := θ.inv ≫ j
  have hρ (W : T.Etaleᵒᵖ) (z : ULift.{u + 1} (ZMod N)) :
      ρ.hom.app W (θ.hom.hom.app W (η.app W z)) =
        (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W
          (r z.down) := by
    have hθ := ConcreteCategory.congr_hom
      (Iso.hom_inv_id_app ((sheafToPresheaf J _).mapIso θ) W) (η.app W z)
    change j.hom.app W (θ.inv.hom.app W (θ.hom.hom.app W (η.app W z))) = _
    change θ.inv.hom.app W (θ.hom.hom.app W (η.app W z)) = η.app W z at hθ
    rw [hθ]
    exact congrArg (fun f ↦ f.app W z)
      (toSheafify_sheafifyLift J j₀ (F.obj C).property)
  let R := Scheme.finiteEtaleMuModulePresheaf T N
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r
  let g (W : T.Etaleᵒᵖ) : R.obj W ⟶ (ModuleCat.restrictScalars r).obj (C.obj.obj W) :=
    letI := AddCommGroup.zmodModule (Scheme.finiteEtaleMu_annihilated T N W)
    ModuleCat.ofHom (X := R.obj W) (Y := (ModuleCat.restrictScalars r).obj (C.obj.obj W))
      ((ρ.hom.app W).hom.toZModLinearMap N
        (M := R.obj W) (M₁ := (ModuleCat.restrictScalars r).obj (C.obj.obj W)))
  let q (W : T.Etaleᵒᵖ) : (ModuleCat.extendScalars r).obj (R.obj W) ⟶ C.obj.obj W :=
    (adj.homEquiv _ _).symm (g W)
  have hq (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
      q W (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) z) =
        ρ.hom.app W z := by
    change (adj.homEquiv _ _ (q W)) z = (g W) z
    exact congrArg (fun f ↦ f z) ((adj.homEquiv _ _).apply_symm_apply (g W))
  let β₀ : R ⋙ ModuleCat.extendScalars r ⟶ C.obj :=
    { app := q
      naturality := by
        intro W V f
        apply ModuleCat.ExtendScalars.hom_ext
        intro z
        change q V ((ModuleCat.extendScalars r).map (R.map f)
          (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) z)) =
            C.obj.map f (q W
              (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) z))
        rw [ModuleCat.ExtendScalars.map_tmul, hq, hq]
        exact NatTrans.naturality_apply ρ.hom f z }
  let β : L ⟶ C := ⟨sheafifyLift J β₀ C.property⟩
  have hβ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
      β.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T
        hA W a z) = a • (show C.obj.obj W from ρ.hom.app W z) := by
    have hh := congrArg (fun f ↦ f.app W
      (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ a z))
      (toSheafify_sheafifyLift J β₀ C.property)
    refine hh.trans ?_
    change q W _ = _
    conv_lhs => rw [← mul_one a,
      ← ModuleCat.ExtendScalars.smul_tmul r a 1 (show R.obj W from z)]
    rw [map_smul, hq]
  have hnorm (W : T.Etaleᵒᵖ) (a : A) :
      α.hom.app W ((toSheafify J
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a) =
      Scheme.finiteEtaleTateOneGenerator A N T hA W a
        (θ.hom.hom.app W (η.app W (ULift.up 1))) := by
    rw [hα]
    change a • ((toSheafify J (R ⋙ ModuleCat.extendScalars r)).app W
      (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) _)) = _
    rw [← map_smul]
    congr 1
    simpa only [mul_one] using
      ModuleCat.ExtendScalars.smul_tmul r a 1 (show R.obj W from
        θ.hom.hom.app W (η.app W (ULift.up 1)))
  have hαβ : α ≫ β = 𝟙 C := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ C.property
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change A at a
    change β.hom.app W (α.hom.app W ((toSheafify J
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a)) =
        (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a
    rw [hnorm, hβ]
    rw [hρ]
    change a • (toSheafify J
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W (r 1) = _
    rw [map_one, ← map_smul]
    change (toSheafify J
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W (a * 1) = _
    rw [mul_one]
  have hρα : ρ ≫ F.map α = v := by
    apply (cancel_epi θ.hom).mp
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (F.obj L).property
    ext W z
    change α.hom.app W (ρ.hom.app W (θ.hom.hom.app W (η.app W z))) =
      v.hom.app W (θ.hom.hom.app W (η.app W z))
    have hone : α.hom.app W
        (ρ.hom.app W (θ.hom.hom.app W (η.app W (ULift.up 1)))) =
        v.hom.app W (θ.hom.hom.app W (η.app W (ULift.up 1))) := by
      rw [hρ, hα]
      change (r 1) • s W = s W
      rw [map_one, one_smul]
    have hz : z = z.down.val • (ULift.up (1 : ZMod N)) := by
      apply ULift.ext
      change z.down = z.down.val • (1 : ZMod N)
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [hz]
    simp only [map_nsmul, hone]
  have hβα : β ≫ α = 𝟙 L := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ L.property
    ext W x
    change α.hom.app W (β.hom.app W ((toSheafify J
      (R ⋙ ModuleCat.extendScalars r)).app W x)) =
        (toSheafify J (R ⋙ ModuleCat.extendScalars r)).app W x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a z =>
      change α.hom.app W (β.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T
        hA W a z)) = _
      rw [hβ, map_smul]
      have hh := congrArg (fun f ↦ f.hom.app W z) hρα
      change α.hom.app W (ρ.hom.app W z) = v.hom.app W z at hh
      rw [hh]
      change a • ((toSheafify J (R ⋙ ModuleCat.extendScalars r)).app W
        (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) z)) = _
      rw [← map_smul]
      congr 1
      simpa only [mul_one] using ModuleCat.ExtendScalars.smul_tmul r a 1 z
  refine ⟨⟨α, β, hαβ, hβα⟩, hnorm, ?_⟩
  intro t ht
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ L.property
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (ht W a).trans (hnorm W a).symm

/-- Change only the positive coefficient level, retaining the fixed field and extension.
Source: blueprint finite-reduction statement
(blueprint: def-pur-finite-reduction-root-charts). -/
abbrev finiteReductionSetting (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) :
    PurityFiniteSetting.{u} :=
  { P with level := m, level_pos := hm }



/-- The actual quotient homomorphism O_E/(varpi^n) → O_E/(varpi^m).
Source: blueprint finite-reduction statement
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionRingHom (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) : P.Ring →+* (P.finiteReductionSetting m hm).Ring :=
  Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level)
    (T := Padic.coefficientExtensionIdeal P.coefficients.l P.extension m)
    (Ideal.pow_le_pow_right hmn)



/-- Derived tensor with the smaller quotient, with its target scalar action retained.
Source: blueprint finite-reduction statement; Stacks 06YY
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReduction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T P.Ring ⥤
      Scheme.proEtaleDerivedCategory T (P.finiteReductionSetting m hm).Ring :=
  Scheme.proEtaleRingDerivedExtension
    (Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))



/-- Finite reduction has the stated finite-Tor constructible domain and codomain.
Source: blueprint proof Step 1 (blueprint: def-pur-finite-reduction-root-charts).
Proof: take a bounded flat model in the Tor interval by lem-sf-flat-model and reduce
it termwise using lem-sf-reduction-flat-model. Scalar tensor associativity preserves
that Tor interval without flatness of the quotient. On a finite constructible
stratification, the resulting cohomology is locally constant and finite; this is
scalarExtensionFunctor_preserves_constructible_tor. The boundedness and
constructibility clauses together give the recorded finiteTorConstructible predicate. -/
theorem finiteReduction_preserves_ctf (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    (K : Scheme.proEtaleDerivedCategory T P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension m hm T
      ((P.finiteReduction m hm hmn T).obj K) := by
  let Q := P.finiteReductionSetting m hm
  let := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level
    P.level_pos
  let := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension m hm
  obtain ⟨⟨hb, hc⟩, a, b, ht⟩ := hK
  have hA : ∃ n : ℕ, ∀ x : P.Ring, (P.coefficients.l ^ n) • x = 0 := by
    refine ⟨P.level, fun x ↦ ?_⟩
    have h := congrArg ULift.down P.diagonalExponent_annihilates
    change ((P.coefficients.l ^ P.level : ℕ) : P.Ring) = 0 at h
    rw [nsmul_eq_mul, h, zero_mul]
  have hB : ∃ n : ℕ, ∀ x : Q.Ring, (P.coefficients.l ^ n) • x = 0 := by
    refine ⟨m, fun x ↦ ?_⟩
    have h := congrArg ULift.down Q.diagonalExponent_annihilates
    change ((P.coefficients.l ^ m : ℕ) : Q.Ring) = 0 at h
    rw [nsmul_eq_mul, h, zero_mul]
  obtain ⟨hb', hc', ht'⟩ := ProEtale.scalarExtensionFunctor_preserves_constructible_tor
    P.coefficients.l hA hB (P.finiteReductionRingHom m hm hmn) T K hb hc a b ht
  exact ⟨⟨hb', hc'⟩, a, b, ht'⟩



/-- The canonical scalar-extension/restriction adjunction, including its tensor unit.
Source: Stacks 06YY, 07A6; blueprint Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionAdjunction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    P.finiteReduction m hm hmn T ⊣
      (Scheme.proEtaleCoefficientRestrictScalars T
        (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory :=
  Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))



/-- The fixed annihilating exponent is positive.
Source: purity coefficient conventions
(blueprint: def-pur-finite-reduction-root-charts). -/
instance finiteReductionExponentNeZero (P : PurityFiniteSetting.{u}) :
    NeZero P.diagonalExponent :=
  ⟨ne_of_gt (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)⟩



/-- The section represented by a primitive base-field root, with no root chosen.
Source: Stacks 03PK, constantZModIsoRootsOfUnitySheaf
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionRootSection (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf P.diagonalExponent).obj.obj W :=
  (T.constantZModIsoRootsOfUnitySheaf P.diagonalExponent
    (T ↘ Spec (.of P.field.k)) hζ).hom.hom.app W
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod P.diagonalExponent))))).app W
            (ULift.up (1 : ZMod P.diagonalExponent)))



/-- The coefficient-root trivialization is uniquely fixed on constant scalar sections.
Source: Stacks 03PK and blueprint Step 1
(blueprint: def-pur-finite-reduction-root-charts).
Proof: tensor the primitive-root isomorphism Z/N ≅ mu_N with the coefficient ring,
then sheafify. The map sends a to a tensor ζ, which gives the displayed formula.
The constant-sheaf generators determine a sheaf morphism uniquely. Primitive-root
trivialization and scalar extension make it an isomorphism, also on the empty scheme. -/
theorem existsUnique_finiteReductionRootTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    ∃! t : Etale.ordinaryFiniteConstant P.Coefficient T ≅
        Scheme.finiteEtaleTateLine T P.diagonalExponent P.Coefficient
          P.diagonalExponent_annihilates,
      ∀ (W : T.Etaleᵒᵖ) (a : P.Coefficient),
        t.hom.hom.app W
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app
                W a) =
          Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent T
            P.diagonalExponent_annihilates W a (P.finiteReductionRootSection T ζ hζ W) := by
  exact rootTrivializationOfConstantIso P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T
    (T.constantZModIsoRootsOfUnitySheaf P.diagonalExponent
      (T ↘ Spec (.of P.field.k)) hζ)

/-- The primitive-root trivialization used only to characterize coefficient comparisons.
Its data are uniquely determined by the preceding section formula.
Source: Stacks 03PK (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionRootTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    Etale.ordinaryFiniteConstant P.Coefficient T ≅
      Scheme.finiteEtaleTateLine T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates :=
  (P.existsUnique_finiteReductionRootTrivialization T ζ hζ).choose



/-- The root chart of the shifted degree-one coefficient.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionShiftedLineChart (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧ ≅
        (Etale.ordinaryFiniteUnit P.Coefficient T)⟦(2 : ℤ)⟧ :=
  (shiftFunctor _ (2 : ℤ)).mapIso
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (P.finiteReductionRootTrivialization T ζ hζ).symm)


/-- The ordered root-power chart is the actual zero/successor tensor recursion
applied to the section-normalized degree-one root chart.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionEtalePowerTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (d : ℕ) :=
  finiteReductionEtaleRootPowerChart P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T (P.finiteReductionShiftedLineChart T ζ hζ) d

/-- Root trivialization of the actual pro-etale shifted coefficient line.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionPowerTrivialization (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (d : ℕ) :
    P.diagonalTwist T d ≅
      ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient T))⟦2 * (d : ℤ)⟧ :=
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T
  F.mapDerivedCategory.mapIso (P.finiteReductionEtalePowerTrivialization T ζ hζ d) ≪≫
    (F.mapDerivedCategory.commShiftIso (2 * (d : ℤ))).app _



/-- Untwisted inverse image in the very same realization coordinates as gamma.
Source: blueprint Step 1 (blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse ⋙ P.smoothPurityPullback f ⋙
    (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor



/-- Intermediate objects of the root chart in the existing fixed-scalar presentation.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def FiniteReductionFixedChartStage (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (d : ℕ) (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    Fin 4 → _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  fun i ↦ match i with
  | 0 => (P.compositionTwistShift X d).obj M
  | 1 => ((smoothPurityTensor P.Coefficient X).obj M).obj (P.diagonalTwist X d)
  | 2 => ((smoothPurityTensor P.Coefficient X).obj M).obj
      ((𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))))⟦2 * (d : ℤ)⟧)
  | 3 => M⟦2 * (d : ℤ)⟧

/-- The three fixed-scalar factors are the actual reassociation, root chart and
native tensor-unit shift comparison, in this order.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def FiniteReductionFixedChartNormalized (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (a : (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧) : Prop :=
  HEq a (finiteReductionChartComposite P.Coefficient X M (P.diagonalTwist X d) (2 * (d : ℤ))
    (P.finiteReductionPowerTrivialization X ζ hζ d ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        (finiteReductionComparisonUnitChart P.Coefficient X)))

/-- The independent root chart has precisely the three specified fixed-scalar factors.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts).
Proof: expand the four intermediate objects. The first factor is the existing
Tate reassociation. The root-power chart and the coefficient-unit chart give the
second factor. The third is the native tensor-unit shift map in its published
presentation. These three isomorphisms have exactly the displayed endpoints;
their composite gives existence. Each heterogeneous equality fixes its factor,
so every chart satisfying the normalization equals that same composite. -/
theorem existsUnique_finiteReductionFixedChart (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    ∃! a : (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧,
      P.FiniteReductionFixedChartNormalized X d ζ hζ M a := by
  exact existsUnique_heq (by rfl)
    (finiteReductionChartComposite P.Coefficient X M (P.diagonalTwist X d) (2 * (d : ℤ))
      (P.finiteReductionPowerTrivialization X ζ hζ d ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          (finiteReductionComparisonUnitChart P.Coefficient X)))

/-- The unique fixed-scalar root chart, before intrinsic realization.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionFixedChart (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧ :=
  (P.existsUnique_finiteReductionFixedChart X d ζ hζ M).choose

/-- The canonical source chart, transported through the actual realization and its shift.
Source: blueprint reduction Step 1
(blueprint: def-pur-finite-reduction-root-charts). -/
def finiteReductionSourceTrivialization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (d : ℕ) (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.compositionShiftedPullback f d).obj K ≅
      ((P.finiteReductionPullback f).obj K)⟦2 * (d : ℤ)⟧ :=
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let M := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  let E := (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory
  E.mapIso (P.finiteReductionFixedChart X d ζ hζ M) ≪≫
    (E.commShiftIso (2 * (d : ℤ))).app M

end WeilConjectures.PurityFiniteSetting
