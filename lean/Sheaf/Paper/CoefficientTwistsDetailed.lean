/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24, Q25
-/
module

public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.CategoryTheory.StageSystemFunctorDescent
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralConstructibleLinear
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Paper.RationalizationKaroubi
public import Sheaf.Paper.AlgebraicallyClosedCoefficients
public import Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Homology.SignedLinePowerFlat
import Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison
import Sheaf.Paper.CompletedLineDerived
import Sheaf.Paper.FiniteLocallyFreeLineModels
import Sheaf.Paper.ConstructibleSingleSupport

import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import all Sheaf.Paper.SignedLineScalarTensorTower
import all Sheaf.Paper.ScalarExtensionComposition
import Sheaf.Paper.ScalarExtensionBinaryCoherence

/-! # Coefficient Tate twists

Source: blueprint `sec-smooth-purity/sk-def-sf-admissible/def-coefficient-twists-detailed.md`,
order 1505; current main-20261015 source: `sec-proetale-coefficients/sk-def-sp-tate-twist/`,
order 1864 (blueprint: def-coefficient-twists-detailed).

The intrinsic rational and common-stage functors are provided by
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`; this module supplies their
shared signed lines and ordinary tensor/scalar comparison.

## Main definitions and statements

- `WeilConjectures.coefficientTateTwists`
- `WeilConjectures.coefficientTwistPower`
- `WeilConjectures.coefficientTwistLine`
- `WeilConjectures.coefficientTwistLine_exact`
- `WeilConjectures.IsCanonicalTwistScalarMaps`
- `WeilConjectures.twistSheafScalarComparison`

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

universe d u v c
set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
attribute [-instance] integralOperationsCommHasDerivedCategory
attribute [-instance] scalarSiteSmall scalarSiteCompose scalarSiteSheafify
  scalarSiteLocallyBijective

/-- Transport the binary tensor comparison to a specified ordinary scalar functor.
The section formula also supplies uniqueness by local tensor generation. -/
private theorem tensorLineScalarComparison
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v} RingCat.{max c v})]
    [HasSheafify J AddCommGrpCat.{max c v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v}]
    {R T : Sheaf J CommRingCat.{max c v}} (α : R ⟶ T)
    (F : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings α M)
    (hmF : ∀ {M M'} (f : M ⟶ M'), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom α M f ≫ eqToHom (hF M').symm)
    (N : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (P : SheafOfModules.{max c v} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (B : F.obj N ≅ P)
    (c : ∀ U : Cᵒᵖ, N.val.obj U → P.val.obj U)
    (hc : ∀ U y, B.hom.val.app U (tensorSection α F hF N U 1 y) = c U y) :
    ∃! b : SheafOfModules.siteSheafTensorRight N ⋙ F ≅
      F ⋙ SheafOfModules.siteSheafTensorRight P,
      ∀ M U s x y, (b.hom.app M).val.app U
          (tensorSection α F hF _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)) =
        SheafOfModules.siteSheafTensorTmul (F.obj M) P U
          (tensorSection α F hF M U s x)
          (c U y) := by
  classical
  let G := SheafOfModules.ScalarHomOrdinary.extensionFunctor.{c, v, max c v} α
  let e : F ≅ G := NatIso.ofComponents
    (fun M ↦ eqToIso (hF M) ≪≫
      SheafOfModules.ScalarHomOrdinary.extensionIso.{c, v, max c v} α M)
    (by
      intro M M' f
      dsimp only [Iso.trans_hom, eqToIso.hom]
      rw [hmF]
      simp only [Category.assoc]
      rw [← Category.assoc (eqToHom (hF M').symm), eqToHom_trans]
      simp only [eqToHom_refl, Category.id_comp]
      apply (cancel_epi (eqToHom (hF M))).mpr
      change SheafOfModules.changeOfRingsHom α M f ≫
          (SheafOfModules.ScalarHomOrdinary.extensionIso α M').hom =
        (SheafOfModules.ScalarHomOrdinary.extensionIso α M).hom ≫ G.map f
      dsimp only [SheafOfModules.ScalarHomOrdinary.extensionIso, Functor.mapIso_hom,
        G, SheafOfModules.ScalarHomOrdinary.extensionFunctor,
        SheafOfModules.changeOfRingsHom, SheafOfModules.changeOfRingsHomOfUniverses]
      erw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)
  have he (M : SheafOfModules.{max c v} ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) (s : T.obj.obj U)
      (x : M.val.obj U) :
      (e.hom.app M).val.app U (tensorSection α F hF M U s x) =
        SheafOfModules.scalarExtensionSection α M U s x := by
    change (SheafOfModules.ScalarHomOrdinary.extensionIso α M).hom.val.app U
      ((eqToHom (hF M)).val.app U ((eqToHom (hF M).symm).val.app U _)) = _
    have hc {A B : SheafOfModules.{max c v} ((sheafCompose J
        (forget₂ CommRingCat RingCat)).obj T)} (h : A = B) (z : B.val.obj U) :
        (eqToHom h).val.app U ((eqToHom h.symm).val.app U z) = z := by
      cases h
      rfl
    rw [hc]
    let adj := PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T).obj)
    have hn := adj.unit.naturality
      (SheafOfModules.ScalarHomOrdinary.extensionPresheafIso α M).hom
    exact (congrArg (fun f ↦ f.app U
      (s ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] x)) hn).symm
  let B' : G.obj N ≅ P := (e.app N).symm ≪≫ B
  obtain ⟨k⟩ := SheafOfModules.exists_scalarExtensionTensorCore R T α
  let bG : SheafOfModules.siteSheafTensorRight N ⋙ G ≅
      G ⋙ SheafOfModules.siteSheafTensorRight P :=
    NatIso.ofComponents
      (fun M ↦ k.tensorComparison M N ≪≫
        SheafOfModules.tensorSecondIso.{c, v, max c v} (G.obj M) B')
      (by
        intro M M' f
        dsimp only [Iso.trans_hom, SheafOfModules.tensorSecondIso_hom, Functor.comp_map]
        change (SheafOfModules.changeOfRingsHomOfUniverses α _
          ((SheafOfModules.siteSheafTensorRight N).map f) ≫
            (k.tensorComparison M' N).hom ≫ _) = _
        rw [← Category.assoc, k.first_natural f N]
        dsimp only [G, SheafOfModules.ScalarHomOrdinary.extensionFunctor]
        simp only [Category.assoc]
        exact congrArg (fun h ↦ (k.tensorComparison M N).hom ≫ h)
            (SheafOfModules.siteSheafTensorSecondMap_naturality
              (SheafOfModules.changeOfRingsHomOfUniverses α M f) B'.hom))
  let b : SheafOfModules.siteSheafTensorRight N ⋙ F ≅
      F ⋙ SheafOfModules.siteSheafTensorRight P :=
    Functor.isoWhiskerLeft _ e ≪≫ bG ≪≫ Functor.isoWhiskerRight e.symm _
  have hb : ∀ M U s x y, (b.hom.app M).val.app U
          (tensorSection α F hF _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)) =
        SheafOfModules.siteSheafTensorTmul (F.obj M) P U
          (tensorSection α F hF M U s x)
          (c U y) := by
    intro M U s x y
    change ((SheafOfModules.siteSheafTensorRight P).map (e.inv.app M)).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap (G.obj M) B'.hom).val.app U
        ((k.tensorComparison M N).hom.val.app U
          ((e.hom.app _).val.app U _))) = _
    rw [he ((SheafOfModules.siteSheafTensorRight N).obj M) U s
      (SheafOfModules.siteSheafTensorTmul M N U x y)]
    rw [k.tensor_tmul M N U s x y]
    change ((SheafOfModules.siteSheafTensorRight P).map (e.inv.app M)).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap (G.obj M) B'.hom).val.app U
        (SheafOfModules.siteSheafTensorTmul (G.obj M) (G.obj N) U
          (SheafOfModules.scalarExtensionSection α M U s x)
          (SheafOfModules.scalarExtensionSection α N U 1 y))) = _
    rw [SheafOfModules.scalarTensor_second_tmul (G.obj M) B'.hom,
      SheafOfModules.scalarTensor_first_tmul (e.inv.app M) P]
    have hleft := congrArg (fun z ↦ (e.inv.app M).val.app U z) (he M U s x)
    have hinv : (e.inv.app M).val.app U
        ((e.hom.app M).val.app U (tensorSection α F hF M U s x)) =
      tensorSection α F hF M U s x := by
      exact congrArg (fun f ↦ f.val.app U (tensorSection α F hF M U s x))
        (e.app M).hom_inv_id
    rw [← hleft, hinv]
    apply congrArg (fun z ↦ SheafOfModules.siteSheafTensorTmul _ _ U
      (tensorSection α F hF M U s x) z)
    change B.hom.val.app U
      ((e.inv.app N).val.app U (SheafOfModules.scalarExtensionSection α N U 1 y)) = _
    rw [← he N U 1 y]
    have hcancel := congrArg (fun f ↦ f.val.app U (tensorSection α F hF N U 1 y))
      (e.app N).hom_inv_id
    change (e.inv.app N).val.app U ((e.hom.app N).val.app U _) =
      tensorSection α F hF N U 1 y at hcancel
    rw [hcancel]
    exact hc U y
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (e.app ((SheafOfModules.siteSheafTensorRight N).obj M)).inv).mp
  apply SheafOfModules.scalarExtension_tensor_hom_ext α M N
  intro U s x y
  have hey := he ((SheafOfModules.siteSheafTensorRight N).obj M) U s
    (SheafOfModules.siteSheafTensorTmul M N U x y)
  have hcancel := congrArg (fun f ↦ f.val.app U (tensorSection α F hF _ U s
    (SheafOfModules.siteSheafTensorTmul M N U x y)))
      (e.app ((SheafOfModules.siteSheafTensorRight N).obj M)).hom_inv_id
  change (e.inv.app _).val.app U ((e.hom.app _).val.app U _) =
    tensorSection α F hF _ U s (SheafOfModules.siteSheafTensorTmul M N U x y)
      at hcancel
  change (b'.hom.app M).val.app U ((e.inv.app _).val.app U _) =
    (b.hom.app M).val.app U ((e.inv.app _).val.app U _)
  rw [← hey, hcancel, hb', hb]

attribute [local instance 3000] integralTowerHasDerivedCategory

variable (X : Scheme.{u})

/-- Tensor powers of the coefficient line, with the unit at exponent zero.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev coefficientTwistPower {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℕ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
  SheafOfModules.scalarTensorPower R L

/-- Positive powers and internal duals of the coefficient line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientTwistLine {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    ℤ → SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  | Int.ofNat n => coefficientTwistPower X L n
  | Int.negSucc n => SheafOfModules.homObj.{u + 1, u, u + 1, u + 1} (R := R)
      (coefficientTwistPower X L (n + 1)) (SheafOfModules.unit.{u, u + 1, u + 1} _)

/-- Tensor with an integer power or dual of a rank-one line is exact and additive.
Source: blueprint order 1505; Stacks Tags 03EK and 03RV
(blueprint: def-coefficient-twists-detailed).
Proof: on a cover trivializing L, each positive tensor power is the unit module,
and internal Hom into the unit is also the unit. Thus tensor with every integer
power is locally the identity. Exactness can be checked locally; additivity follows
on sectionwise tensor generators and passes through sheafification. -/
theorem coefficientTwistLine_exact
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (L : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    [L.IsFiniteLocallyFreeOfRank 1] (m : ℤ) :
    (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)).Additive ∧
    PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)) ∧
    PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
      (coefficientTwistLine X L m)) := by
  classical
  obtain ⟨I, U, hU, hL⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (R := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (M := L) (r := 1)).mp inferInstance
  have hcharts : ∃ (I : Type (u + 1)) (U : I → X.ProEt),
      (ProEt.topology X).CoversTop U ∧ ∀ i,
        Nonempty (L.over (U i) ≅ SheafOfModules.unit
          (((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (U i))) :=
    ⟨I, U, hU, fun i => ⟨(hL i).some ≪≫ SheafOfModules.freeUniqueIso (ULift.{u + 1} (Fin 1))⟩⟩
  have hflat := SheafOfModules.SignedLineDerivedBaseChange.signed_line_power_flat.{u + 1, u, u + 1}
    R L hcharts m
  have hline : SheafOfModules.signedLinePower.{u + 1, u, u + 1} L m =
      coefficientTwistLine X L m := by
    cases m <;> rfl
  rw [hline] at hflat
  change PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
      (A := R) (coefficientTwistLine X L m)) ∧
    PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
      (A := R) (coefficientTwistLine X L m)) at hflat
  exact ⟨(CategoryTheory.rightExactFunctor_le_additiveFunctor _ _) _ hflat.2, hflat⟩

variable (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E] (S : Scheme.{u})
  [∀ x : S, Invertible (ℓ : S.residueField x)]

/-- The published integral first line has rank one; reuse its recorded theorem.
Source: blueprint order 1505; Stacks 03PK
(blueprint: def-coefficient-twists-detailed). -/
instance coefficientTwistIntegralRank :
    (purTwistIntegralModule S ℓ E).IsFiniteLocallyFreeOfRank 1 :=
  (pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.1

/-- The published ordinary finite reduction has rank one.
Source: blueprint order 1505; Stacks 03PK
(blueprint: def-coefficient-twists-detailed). -/
instance coefficientTwistFiniteRank (n : ℕ) :
    (purTwistFiniteOne S ℓ E n).IsFiniteLocallyFreeOfRank 1 :=
  ((pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.2 n).2.1

/-- The finite coefficient twist at quotient exponent n+1.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev finiteCoefficientTwist (n : ℕ) (m : ℤ) :
    SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S n) :=
  coefficientTwistLine S (purTwistFiniteOne S ℓ E n) m

/-- Derived tensor by the finite twisting line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def finiteComplexTwist (n : ℕ) (m : ℤ) :
    proEtaleDerivedCategory S (Padic.coefficientExtensionRing ℓ E (n + 1)) ⥤
      proEtaleDerivedCategory S (Padic.coefficientExtensionRing ℓ E (n + 1)) := by
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).1
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).2.1
  letI := (coefficientTwistLine_exact S (purTwistFiniteOne S ℓ E n) m).2.2
  exact (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
    (A := integralCoefficientCommRingSheaf ℓ E S n)
    (finiteCoefficientTwist ℓ E S n m)).mapDerivedCategory

/-- Tensor by the completed integral line on module sheaves.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def integralSheafTwist (m : ℤ) : integralTowerModules ℓ E S ⥤ integralTowerModules ℓ E S :=
  SheafOfModules.siteSheafTensorRight
    (A := completedIntegralCommRingSheafUnrestricted ℓ E S)
    (coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m)

/-- Additivity of tensor with the integral line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
instance integralSheafTwist_additive (m : ℤ) : (integralSheafTwist ℓ E S m).Additive :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).1

/-- Tensor with the integral line preserves finite limits.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
instance integralSheafTwist_finiteLimits (m : ℤ) :
    PreservesFiniteLimits (integralSheafTwist ℓ E S m) :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).2.1

/-- Tensor with the integral line preserves finite colimits.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
instance integralSheafTwist_finiteColimits (m : ℤ) :
    PreservesFiniteColimits (integralSheafTwist ℓ E S m) :=
  (coefficientTwistLine_exact S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m).2.2

/-- Derived tensor by the completed integral twisting line. Since the line is flat,
termwise tensor already computes derived tensor for every unbounded complex.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def integralComplexTwist (m : ℤ) :
    completedIntegralDerivedCategory ℓ E S D hℓ ⥤
      completedIntegralDerivedCategory ℓ E S D hℓ :=
  (integralSheafTwist ℓ E S m).mapDerivedCategory

/-- The canonical linear structure on the completed integral derived category.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
noncomputable instance completedIntegralLinear :
    Linear (Padic.coefficientExtensionIntegers ℓ E)
      (completedIntegralDerivedCategory ℓ E S D hℓ) := by
  exact integralCoefficientLinear ℓ E S

/-- The integral twist placed in degree zero.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def integralCoefficientTwist (m : ℤ) :
    completedIntegralDerivedCategory ℓ E S D hℓ :=
  (DerivedCategory.singleFunctor _ 0).obj
    (coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m)

/-- Every integral twist is bounded constructible and derived complete.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: trivialize on a primitive-root pro-etale cover. Powers and duals are again
rank-one lines, and their finite reductions are finite locally constant with common
support interval [0,0]. The compatible finite reductions recover the completed line,
so its canonical derived-completeness comparison is invertible. -/
theorem integralCoefficientTwist_constructible (m : ℤ) :
    boundedConstructibleDerivedCompleteIntegral D ℓ hℓ E S
      (integralCoefficientTwist D ℓ hℓ E S m) := by
  classical
  let L := coefficientTwistLine S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m
  have hL : L.IsFiniteLocallyFreeOfRank 1 := by
    let hroot : (purTwistIntegralModule S ℓ E).IsFiniteLocallyFreeOfRank 1 :=
      (pur_twist_sheaf_locally_free.{u, 0} S ℓ E).2.2.1.2.2.1
    let hsmall : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    let hdc : ∀ R : Sheaf (ProEt.topology S) CommRingCat.{u + 1},
        HasDerivedCategory.{u + 2}
          (SheafOfModules.OrdinaryLineScalar.Modules.{u, u + 1} S R) :=
      fun R ↦ inferInstance
    let data := @SheafOfModules.OrdinaryLineScalar.exists_lineData.{u, u + 1, u + 2}
      S hsmall hdc (completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) hroot
    have h := @SheafOfModules.OrdinaryLineScalar.LineData.rank.{u, u + 1, u + 2}
      S hsmall hdc (completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) data.some m
    cases m <;> exact h
  obtain ⟨hred, hcomplete⟩ := completedLine_derived S ℓ E L hL D hℓ
  refine ⟨hcomplete, 0, 0, le_rfl, ?_⟩
  intro n
  let a := completedIntegralCommRingProjectionUnrestricted ℓ E S n
  let N := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a L
  have hN : N.IsFiniteLocallyFreeOfRank 1 := by
    let := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).mpr hL
    exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one N).mp
      (SheafOfModules.scalarExtensionDual_localIsomorphism.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted ℓ E S)
        (integralCoefficientCommRingSheaf ℓ E S n) a L).1
  let := Padic.finite_coefficientExtensionRing ℓ E (n + 1) (Nat.succ_pos n)
  have hconst := (finiteLocallyFreeLine_models S
    (Padic.coefficientExtensionRing ℓ E (n + 1)) N hN).2.1
  obtain ⟨hfin, hc, hs, _⟩ := constructible_single_support S
    (Padic.coefficientExtensionRing ℓ E (n + 1)) N hconst _ (hred n).some
  refine ⟨⟨hfin, hc⟩, ?_⟩
  intro i hi
  have hi0 : i = 0 := hs hi
  subst i
  exact ⟨le_rfl, le_rfl⟩

/-- The rational twist is the image in the raw scalar localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def rationalCoefficientTwist (m : ℤ) :
    rationalConstructibleCategory D ℓ hℓ E S :=
  (rationalConstructibleLocalization D ℓ hℓ E S).obj
    ⟨integralCoefficientTwist D ℓ hℓ E S m,
      integralCoefficientTwist_constructible D ℓ hℓ E S m⟩

/-- The coefficient line as a module sheaf, for every integer exponent.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev integralTwistLine (m : ℤ) : integralTowerModules ℓ E S :=
  coefficientTwistLine S
    (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m

section ScalarComparison

variable (L : Type u) [Field L] [Algebra (Padic ℓ) L]
  [FiniteDimensional (Padic ℓ) L] (ι : E →ₐ[Padic ℓ] L)

/-- The constant integer inclusion induced by the specified coefficient embedding.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistConstantIntegerMap : purTwistIntegralConstant S ℓ E ⟶
    purTwistIntegralConstant S ℓ L :=
  (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((integralScalarIntegerInclusion ℓ E L ι).comp ULift.ringEquiv.toRingHom)))

/-- Semilinear maps from the E-lines to the L-lines, before scalar extension.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
abbrev TwistScalarMaps := ∀ m : ℤ,
  integralTwistLine ℓ E S m ⟶
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap ℓ E L ι S))).obj (integralTwistLine ℓ L S m)

/-- The roots-of-unity, unit, tensor-power and dual-evaluation normalization.
These equations specify maps, rather than merely coherent isomorphisms.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def IsCanonicalTwistScalarMaps (c : TwistScalarMaps ℓ E S L ι) : Prop :=
  (∀ (U : S.ProEtᵒᵖ) (a : (completedIntegralCommRingSheafUnrestricted ℓ E S).obj.obj U),
    (c 0).val.app U a = (integralCompletedScalarMap ℓ E L ι S).hom.app U a) ∧
  (∀ (U : S.ProEtᵒᵖ) (b : (purTwistIntegralConstant S ℓ E).obj.obj U)
      (x : (purTwistZlModule S ℓ).val.obj U),
    (c 1).val.app U (purTwistIntegralTensor S ℓ E U b x) =
      purTwistIntegralTensor S ℓ L U ((twistConstantIntegerMap ℓ E S L ι).hom.app U b) x) ∧
  (∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) (n + 1)).val.obj U)
      (y : (purTwistIntegralModule S ℓ E).val.obj U),
    (c (Int.ofNat (n + 2))).val.app U
        (SheafOfModules.siteSheafTensorTmul
          (A := completedIntegralCommRingSheafUnrestricted ℓ E S) _ _ U x y) =
      SheafOfModules.siteSheafTensorTmul
        (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U
        ((c (Int.ofNat (n + 1))).val.app U x) ((c 1).val.app U y)) ∧
  ∀ (n : ℕ) (U : S.ProEtᵒᵖ)
      (f : (integralTwistLine ℓ E S (Int.negSucc n)).val.obj U)
      (x : (coefficientTwistPower S
        (R := completedIntegralCommRingSheafUnrestricted ℓ E S)
        (purTwistIntegralModule S ℓ E) (n + 1)).val.obj U),
    (((c (Int.negSucc n)).val.app U f).app (Opposite.op (Over.mk (𝟙 U.unop))))
        ((c (Int.ofNat (n + 1))).val.app U x) =
      (integralCompletedScalarMap ℓ E L ι S).hom.app U
        ((f.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

/-- There is exactly one normalized semilinear family on the signed Tate lines.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: at zero take the completed coefficient inclusion. At one send the root
limit tensor b to the same root limit tensor its integer image. The balanced
relations agree by the finite residue characterizations of the completed actions.
For positive powers tensor these maps recursively. For negative powers use the
unique dual map whose evaluation is the image of the original evaluation.
On a cover trivializing the root line these maps are the coefficient inclusion,
so the positive maps generate the target line and the dual map is unique.
The formulas commute with restrictions and glue; tensor sheafification and the
local generation of each positive line prove uniqueness in every degree. -/
theorem twistScalarMaps_existsUnique :
    ∃! c : TwistScalarMaps ℓ E S L ι, IsCanonicalTwistScalarMaps ℓ E S L ι c := by
  sorry

/-- The signed scalar maps fixed by root tensors, powers and dual evaluation.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistScalarMaps : TwistScalarMaps ℓ E S L ι :=
  (twistScalarMaps_existsUnique ℓ E S L ι).exists.choose

/-- Scalar extension of each line is the target line, with the specified map.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: extend the semilinear map by balancing, sending s tensor x to s times c(x).
On a trivializing cover this is multiplication R_L tensor R_E to R_L and has
inverse z to z tensor one. Glue the local inverses. Pure tensors generate locally,
so the displayed formula uniquely determines the isomorphism, also at zero. -/
theorem twistLineScalarIso_existsUnique (m : ℤ) :
    ∃! c : (integralOrdinaryScalar ℓ E L ι S).obj (integralTwistLine ℓ E S m) ≅
        integralTwistLine ℓ L S m,
      ∀ (U : S.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
        (x : (integralTwistLine ℓ E S m).val.obj U),
        c.hom.val.app U
            (integralOrdinaryTensorSection ℓ E L ι S _ U s x) =
          s • (@id ((integralTwistLine ℓ L S m).val.obj U)
            ((twistScalarMaps ℓ E S L ι m).val.app U x)) := by
  sorry

/-- The canonical scalar-extension isomorphism for the signed line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistLineScalarIso (m : ℤ) :
    (integralOrdinaryScalar ℓ E L ι S).obj (integralTwistLine ℓ E S m) ≅
      integralTwistLine ℓ L S m :=
  (twistLineScalarIso_existsUnique ℓ E S L ι m).exists.choose

/-- Tensor and scalar extension commute by the normalized balanced map.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: send s tensor (x tensor y) to (s tensor x) tensor c(y), with c the
normalized semilinear line map. Its inverse is the ordinary tensor associator
followed by the inverse canonical line comparison. The balanced formulas commute
with restrictions and module maps. They sheafify to a natural isomorphism.
Local pure-tensor generation uniquely determines every component. -/
theorem twistSheafScalarComparison_existsUnique (m : ℤ) :
    ∃! b : integralSheafTwist ℓ E S m ⋙ integralOrdinaryScalar ℓ E L ι S ≅
        integralOrdinaryScalar ℓ E L ι S ⋙ integralSheafTwist ℓ L S m,
      ∀ (N : integralTowerModules ℓ E S) (U : S.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted ℓ L S).obj.obj U)
        (x : N.val.obj U) (y : (integralTwistLine ℓ E S m).val.obj U),
        (b.hom.app N).val.app U
            (integralOrdinaryTensorSection ℓ E L ι S _ U s
              (SheafOfModules.siteSheafTensorTmul
                (A := completedIntegralCommRingSheafUnrestricted ℓ E S) N _ U x y)) =
          SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ U
            (integralOrdinaryTensorSection ℓ E L ι S N U s x)
            ((twistScalarMaps ℓ E S L ι m).val.app U y) := by
  exact tensorLineScalarComparison (integralCompletedScalarMap ℓ E L ι S)
    (integralOrdinaryScalar ℓ E L ι S)
    (integralOrdinaryScalarWitness ℓ E L ι S).choose_spec.choose
    (integralOrdinaryScalarWitness ℓ E L ι S).choose_spec.choose_spec.choose
    (integralTwistLine ℓ E S m) (integralTwistLine ℓ L S m)
    (twistLineScalarIso ℓ E S L ι m)
    (fun U y ↦ @id ((integralTwistLine ℓ L S m).val.obj U)
      ((twistScalarMaps ℓ E S L ι m).val.app U y))
    (fun U y ↦ by
      change (twistLineScalarIso ℓ E S L ι m).hom.val.app U
          (integralOrdinaryTensorSection ℓ E L ι S _ U 1 y) = _
      simpa only [twistLineScalarIso, one_smul] using
        (twistLineScalarIso_existsUnique ℓ E S L ι m).exists.choose_spec U 1 y)

/-- The ordinary natural comparison fixed on local pure tensors.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistSheafScalarComparison (m : ℤ) :
    integralSheafTwist ℓ E S m ⋙ integralOrdinaryScalar ℓ E L ι S ≅
      integralOrdinaryScalar ℓ E L ι S ⋙ integralSheafTwist ℓ L S m :=
  (twistSheafScalarComparison_existsUnique ℓ E S L ι m).exists.choose

/-- Derive the fixed sheaf comparison through the canonical exact-functor calculus.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def twistDerivedScalarComparison (m : ℤ) :
    integralComplexTwist D ℓ hℓ E S m ⋙ integralOrdinaryDerivedScalar ℓ E L ι S ≅
      integralOrdinaryDerivedScalar ℓ E L ι S ⋙ integralComplexTwist D ℓ hℓ L S m :=
  (Functor.mapDerivedCategoryCompIso (integralSheafTwist ℓ E S m)
      (integralOrdinaryScalar ℓ E L ι S)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (twistSheafScalarComparison ℓ E S L ι m) ≪≫
    Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar ℓ E L ι S)
      (integralSheafTwist ℓ L S m)

end ScalarComparison

/-- Identity scalar extension gives the identity on every signed root line.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the identity family satisfies the zero, root-tensor, positive tensor and
negative evaluation normalizations. The unique-family clause identifies it
with twistScalarMaps for the identity coefficient embedding. -/
theorem twistScalarMaps_identity (m : ℤ) (U : S.ProEtᵒᵖ)
    (x : (integralTwistLine ℓ E S m).val.obj U) :
    (twistScalarMaps ℓ E S E (AlgHom.id (Padic ℓ) E) m).val.app U x = x := by
  classical
  have hα : integralCompletedScalarMap ℓ E E (AlgHom.id (Padic ℓ) E) S = 𝟙 _ :=
    completedScalar_id ℓ E S
  have hconst : twistConstantIntegerMap ℓ E S E (AlgHom.id (Padic ℓ) E) = 𝟙 _ := by
    have hi : integralScalarIntegerInclusion ℓ E E (AlgHom.id (Padic ℓ) E) =
        RingHom.id _ := by
      ext a
      rfl
    unfold twistConstantIntegerMap
    rw [hi]
    convert (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map_id
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers ℓ E)))
      using 1
    rfl
  let c : TwistScalarMaps ℓ E S E (AlgHom.id (Padic ℓ) E) := fun k ↦
    { val :=
        { app := fun V ↦ ModuleCat.ofHom
            (X := (integralTwistLine ℓ E S k).val.obj V)
            (Y := ((SheafOfModules.restrictScalars.{u + 1}
              ((sheafCompose (ProEt.topology S)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                  (integralCompletedScalarMap ℓ E E (AlgHom.id (Padic ℓ) E) S))).obj
                    (integralTwistLine ℓ E S k)).val.obj V)
            { toFun := fun z ↦ z
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun a z ↦ by
                change a • z =
                  (integralCompletedScalarMap ℓ E E (AlgHom.id (Padic ℓ) E) S).hom.app V a • z
                rw [hα]
                rfl }
          naturality := fun _ ↦ by rfl } }
  have hc : IsCanonicalTwistScalarMaps ℓ E S E (AlgHom.id (Padic ℓ) E) c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro V a
      change a =
        (integralCompletedScalarMap ℓ E E (AlgHom.id (Padic ℓ) E) S).hom.app V a
      rw [hα]
      rfl
    · intro V a y
      change purTwistIntegralTensor S ℓ E V a y =
        purTwistIntegralTensor S ℓ E V
          ((twistConstantIntegerMap ℓ E S E (AlgHom.id (Padic ℓ) E)).hom.app V a) y
      rw [hconst]
      rfl
    · intro n V y z
      rfl
    · intro n V f y
      change f.app (Opposite.op (Over.mk (𝟙 V.unop))) y =
        (integralCompletedScalarMap ℓ E E (AlgHom.id (Padic ℓ) E) S).hom.app V
          (f.app (Opposite.op (Over.mk (𝟙 V.unop))) y)
      rw [hα]
      rfl
  have h := (twistScalarMaps_existsUnique ℓ E S E (AlgHom.id (Padic ℓ) E)).unique
    (twistScalarMaps_existsUnique ℓ E S E (AlgHom.id (Padic ℓ) E)).exists.choose_spec hc
  exact congrArg (fun a : TwistScalarMaps ℓ E S E (AlgHom.id (Padic ℓ) E) ↦
    (a m).val.app U x) h

/-- The semilinear signed-line maps compose along every coefficient tower.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the completed and constant integer maps compose by their residue formulas.
The composite families therefore have the same zero and root-tensor formulas.
Tensor recursion propagates this to positive powers. Evaluating on the images
of positive-line sections gives the same negative evaluation formula. Uniqueness
of the normalized family identifies the composite with the direct map. -/
theorem twistScalarMaps_composition
    (L : Type u) [Field L] [Algebra (Padic ℓ) L] [FiniteDimensional (Padic ℓ) L]
    (ι : E →ₐ[Padic ℓ] L)
    (M : Type u) [Field M] [Algebra (Padic ℓ) M] [FiniteDimensional (Padic ℓ) M]
    (κ : L →ₐ[Padic ℓ] M) (m : ℤ) (U : S.ProEtᵒᵖ)
    (x : (integralTwistLine ℓ E S m).val.obj U) :
    (@id ((integralTwistLine ℓ M S m).val.obj U)
      ((twistScalarMaps ℓ E S M (κ.comp ι) m).val.app U x)) =
      (@id ((integralTwistLine ℓ M S m).val.obj U)
        ((twistScalarMaps ℓ L S M κ m).val.app U
          (@id ((integralTwistLine ℓ L S m).val.obj U)
            ((twistScalarMaps ℓ E S L ι m).val.app U x)))) := by
  classical
  have hα : integralCompletedScalarMap ℓ E M (κ.comp ι) S =
      integralCompletedScalarMap ℓ E L ι S ≫ integralCompletedScalarMap ℓ L M κ S :=
    (completedScalar_comp ℓ E L ι S M κ).symm
  have hconst : twistConstantIntegerMap ℓ E S M (κ.comp ι) =
      twistConstantIntegerMap ℓ E S L ι ≫ twistConstantIntegerMap ℓ L S M κ := by
    unfold twistConstantIntegerMap
    erw [← Functor.map_comp]
    congr 1
  generalize hELdef : twistScalarMaps ℓ E S L ι = cEL
  generalize hLMdef : twistScalarMaps ℓ L S M κ = cLM
  have hEL : IsCanonicalTwistScalarMaps ℓ E S L ι cEL :=
    hELdef ▸ (twistScalarMaps_existsUnique ℓ E S L ι).exists.choose_spec
  have hLM : IsCanonicalTwistScalarMaps ℓ L S M κ cLM :=
    hLMdef ▸ (twistScalarMaps_existsUnique ℓ L S M κ).exists.choose_spec
  let c : TwistScalarMaps ℓ E S M (κ.comp ι) := fun k ↦
    { val :=
        { app := fun V ↦
            (cEL k).val.app V ≫
              (ModuleCat.restrictScalars
                ((integralCompletedScalarMap ℓ E L ι S).hom.app V).hom).map
                  ((cLM k).val.app V) ≫
              (ModuleCat.restrictScalarsComp'App
                ((integralCompletedScalarMap ℓ E L ι S).hom.app V).hom
                ((integralCompletedScalarMap ℓ L M κ S).hom.app V).hom
                ((integralCompletedScalarMap ℓ E M (κ.comp ι) S).hom.app V).hom
                (congrArg (fun a : completedIntegralCommRingSheafUnrestricted ℓ E S ⟶
                    completedIntegralCommRingSheafUnrestricted ℓ M S ↦
                      (a.hom.app V).hom) hα)
                ((integralTwistLine ℓ M S k).val.obj V)).inv
          naturality := fun {V W} f ↦ by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro z
            exact (congrArg (fun y ↦ (cLM k).val.app W y)
              (PresheafOfModules.naturality_apply (cEL k).val f z)).trans
                (PresheafOfModules.naturality_apply (cLM k).val f ((cEL k).val.app V z)) } }
  have hc : IsCanonicalTwistScalarMaps ℓ E S M (κ.comp ι) c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro V a
      change (cLM 0).val.app V ((cEL 0).val.app V a) = _
      rw [hEL.1, hLM.1, hα]
      rfl
    · intro V a y
      change (cLM 1).val.app V
          ((cEL 1).val.app V (purTwistIntegralTensor S ℓ E V a y)) = _
      rw [hEL.2.1, hLM.2.1, hconst]
      rfl
    · intro n V y z
      change (cLM (Int.ofNat (n + 2))).val.app V
          ((cEL (Int.ofNat (n + 2))).val.app V
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted ℓ E S) _ _ V y z)) = _
      calc
        _ = (cLM (Int.ofNat (n + 2))).val.app V
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted ℓ L S) _ _ V
                ((cEL (Int.ofNat (n + 1))).val.app V y) ((cEL 1).val.app V z)) :=
          congrArg (fun t : (integralTwistLine ℓ L S (Int.ofNat (n + 2))).val.obj V ↦
            (cLM (Int.ofNat (n + 2))).val.app V t) (hEL.2.2.1 n V y z)
        _ = _ := hLM.2.2.1 n V _ _
    · intro n V f y
      change (((cLM (Int.negSucc n)).val.app V
          ((cEL (Int.negSucc n)).val.app V f)).app
            (Opposite.op (Over.mk (𝟙 V.unop))))
          ((cLM (Int.ofNat (n + 1))).val.app V
            ((cEL (Int.ofNat (n + 1))).val.app V y)) = _
      calc
        _ = (integralCompletedScalarMap ℓ L M κ S).hom.app V
            ((((cEL (Int.negSucc n)).val.app V f).app
              (Opposite.op (Over.mk (𝟙 V.unop))))
                ((cEL (Int.ofNat (n + 1))).val.app V y)) := hLM.2.2.2 n V _ _
        _ = (integralCompletedScalarMap ℓ L M κ S).hom.app V
            ((integralCompletedScalarMap ℓ E L ι S).hom.app V
              (f.app (Opposite.op (Over.mk (𝟙 V.unop))) y)) :=
          congrArg (fun z ↦ (integralCompletedScalarMap ℓ L M κ S).hom.app V z)
            (hEL.2.2.2 n V f y)
        _ = _ := (congrArg (fun a : completedIntegralCommRingSheafUnrestricted ℓ E S ⟶
            completedIntegralCommRingSheafUnrestricted ℓ M S ↦
              a.hom.app V (f.app (Opposite.op (Over.mk (𝟙 V.unop))) y)) hα).symm
  have h := (twistScalarMaps_existsUnique ℓ E S M (κ.comp ι)).unique
    (twistScalarMaps_existsUnique ℓ E S M (κ.comp ι)).exists.choose_spec hc
  exact congrArg (fun a : TwistScalarMaps ℓ E S M (κ.comp ι) ↦
    (a m).val.app U x) h

/-- The rational Tate line is compatible with every finite coefficient extension.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed).
Proof: the integer Tate line is the same roots-of-unity limit for both fields.
Associativity of sheafified tensor identifies extension of its O_E tensor with its
O_L tensor, and likewise their tensor powers. Duals commute with scalar extension
because the lines are finite locally free. On the complete rank-one objects the
completed scalar extension is ordinary tensor. Apply rationalization to these
canonical comparisons, including at exponent zero. -/
theorem rationalCoefficientTwist_scalarExtension
    (L : Type u) [Field L] [Algebra (Padic ℓ) L]
    [FiniteDimensional (Padic ℓ) L] (ι : E →ₐ[Padic ℓ] L) (m : ℤ) :
    Nonempty
      ((rationalScalarExtension D ℓ hℓ E S L ι).obj
        (rationalCoefficientTwist D ℓ hℓ E S m) ≅
          rationalCoefficientTwist D ℓ hℓ L S m) := by
  let e : (integralOrdinaryDerivedScalar ℓ E L ι S).obj
        (integralCoefficientTwist D ℓ hℓ E S m) ≅
      integralCoefficientTwist D ℓ hℓ L S m :=
    ((integralOrdinaryScalar ℓ E L ι S).mapDerivedCategorySingleFunctor 0).app
        (integralTwistLine ℓ E S m) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (twistLineScalarIso ℓ E S L ι m)
  let e' : (integralConstructibleScalarExtension D ℓ hℓ E L ι S).obj
        ⟨integralCoefficientTwist D ℓ hℓ E S m,
          integralCoefficientTwist_constructible D ℓ hℓ E S m⟩ ≅
      ⟨integralCoefficientTwist D ℓ hℓ L S m,
        integralCoefficientTwist_constructible D ℓ hℓ L S m⟩ :=
    (boundedConstructibleDerivedCompleteIntegral D ℓ hℓ L S).isoMk e
  exact ⟨((rationalOrdinaryComparison D ℓ hℓ E S L ι).app
      (rationalCoefficientTwist D ℓ hℓ E S m)).symm ≪≫
    (rationalConstructibleLocalization D ℓ hℓ L S).mapIso e'⟩

variable (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω]
  [IsAlgClosure (Padic ℓ) Ω]

/-- The algebraically closed twist at a finite coefficient stage.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def algebraicClosureCoefficientTwist
    (F : Padic.FiniteCoefficientFields ℓ Ω) (m : ℤ) :
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S :=
  ⟨F, rationalCoefficientTwist D ℓ hℓ (AlgebraicallyClosedCoefficients.Coefficient ℓ Ω F) S m⟩

/-- The finite line-family type, named to keep coefficient record checking small.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientFiniteTwistFamily (n : ℕ) : Type (u + 2) :=
  ℤ → SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S (n - 1))

/-- The integral line-family type, retaining the actual completed coefficient sheaf.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientIntegralTwistFamily : Type (u + 2) :=
  ℤ → SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted ℓ E S)

/-- The rational line-family type, retaining the raw scalar localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientRationalTwistFamily : Type (u + 2) :=
  ℤ → rationalConstructibleCategory D ℓ hℓ E S

/-- The algebraic line-family type with its displayed finite coefficient index.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientAlgebraicTwistFamily : Type (max v (u + 2)) :=
  ∀ _F : Padic.FiniteCoefficientFields ℓ Ω, ℤ →
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S

/-- The four coefficient lines for all integer twists.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
structure CoefficientTateTwistData (n : ℕ) where
  finite : coefficientFiniteTwistFamily ℓ E S n
  integral : coefficientIntegralTwistFamily ℓ E S
  rational : coefficientRationalTwistFamily D ℓ hℓ E S
  algebraic : coefficientAlgebraicTwistFamily D ℓ hℓ S Ω

/-- Assemble finite, integral, rational, and common-stage Tate twists.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientTateTwists (n : ℕ) (_hn : 1 ≤ n) :
    CoefficientTateTwistData D ℓ hℓ E S Ω n :=
  { finite := fun m => coefficientTwistLine S (purTwistFiniteOne S ℓ E (n - 1)) m
    integral := fun m => coefficientTwistLine S
      (R := completedIntegralCommRingSheafUnrestricted ℓ E S) (purTwistIntegralModule S ℓ E) m
    rational := fun m => rationalCoefficientTwist D ℓ hℓ E S m
    algebraic := fun F m => algebraicClosureCoefficientTwist D ℓ hℓ S Ω F m }

end WeilConjectures
