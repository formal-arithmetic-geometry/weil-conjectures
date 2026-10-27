/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.SfIntegralConstructibleLinear
import all Sheaf.Paper.IntegralConstructibleLinear
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.LineEvaluationInversePair
import all Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Constant-scalar bilinearity of integral derived internal Hom

Source: Stacks Project, Section 08J7 and Lemma 0A95; the rational internal-Hom
paragraph of blueprint `def-weil-derived-pullback-tensor-hom`.
-/

@[expose] public section
set_option autoImplicit false

universe u a b
open CategoryTheory AlgebraicGeometry Opposite

namespace WeilConjectures

open CategoryTheory.MonoidalCategory

private theorem closedHom_bilinear
    {D : Type a} [Category.{b} D] [Preadditive D]
    (R : Type*) [CommRing R] [Linear R D]
    (H : Dᵒᵖ × D ⥤ D) (S : CoefficientClosedStructure H)
    (hadd : let := S.monoidal; MonoidalPreadditive D)
    (hlin : let := S.monoidal; let := hadd; MonoidalLinear R D)
    (M M' N N' : D) :
    ∃ b : (M' ⟶ M) →ₗ[R] (N ⟶ N') →ₗ[R]
        (H.obj (op M, N) ⟶ H.obj (op M', N')),
      ∀ f g, b f g = H.map (Prod.mkHom f.op g) := by
  let := S.monoidal
  let := hadd
  let := hlin
  let A : (M' ⟶ M) →ₗ[R] (H.obj (op M, N) ⟶ H.obj (op M', N)) :=
    { toFun := fun f ↦ H.map (Prod.mkHom f.op (𝟙 N))
      map_add' := fun f g ↦ by
        apply ((S.adjunction M').homEquiv _ N).symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.map_add, Preadditive.add_comp]
        rw [S.evaluation_naturality, S.evaluation_naturality, S.evaluation_naturality]
        simp only [Functor.map_add, Preadditive.add_comp]
      map_smul' := fun r f ↦ by
        apply ((S.adjunction M').homEquiv _ N).symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]
        rw [S.evaluation_naturality, S.evaluation_naturality]
        simp only [Functor.map_smul, Linear.smul_comp, RingHom.id_apply] }
  let B : (N ⟶ N') →ₗ[R] (H.obj (op M', N) ⟶ H.obj (op M', N')) :=
    { toFun := (Prod.sectR (op M') D ⋙ H).map
      map_add' := by
        let := (S.adjunction M').right_adjoint_additive
        exact fun x y ↦ (Prod.sectR (op M') D ⋙ H).map_add (f := x) (g := y)
      map_smul' := fun r f ↦ by
        apply ((S.adjunction M').homEquiv _ N').symm.injective
        simp only [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]
        change (tensorRight M').map ((Prod.sectR (op M') D ⋙ H).map (r • f)) ≫
            (S.adjunction M').counit.app N' = _
        have hc (g : N ⟶ N') := (S.adjunction M').counit.naturality g
        dsimp only [Functor.comp_map, Functor.id_map] at hc ⊢
        rw [hc, hc]
        simp only [Linear.comp_smul, RingHom.id_apply] }
  refine ⟨
    { toFun := fun f ↦ (Linear.leftComp R _ (A f)).comp B
      map_add' := fun f g ↦ by
        ext k
        exact (congrArg (fun z ↦ z ≫ B k) (A.map_add f g)).trans
          (Preadditive.add_comp _ _ _ _ _ _)
      map_smul' := fun r f ↦ by
        ext k
        exact (congrArg (fun z ↦ z ≫ B k) (A.map_smul r f)).trans
          (Linear.smul_comp _ _ _ _ _ _) }, ?_⟩
  intro f g
  change H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op M')) g) = _
  rw [← H.map_comp]
  congr 1
  ext <;> simp

/-- The ambient integral internal-Hom action is bilinear for the published constant
valuation-ring action. The first arrow is contravariant; the second is covariant.
Source: Stacks Project, Section 08J7 and Lemma 0A95; blueprint
`def-weil-derived-pullback-tensor-hom`, rational internal-Hom paragraph.
(blueprint: lem-sf-integral-derived-hom-bilinear).

Proof: compute the second input with a K-injective resolution. On the sheaf Hom
complex, precomposition and postcomposition are additive in their arrows. For a
constant valuation-ring scalar a, their sectionwise formulas are h ↦ h ∘ (a f)
and h ↦ (a g) ∘ h. Module-linearity of h and of the differentials identifies these
with a times the corresponding maps. These identities hold degreewise in the
products defining the Hom complex, hence also for its differential. Pass to the
derived category. An arbitrary first-variable derived arrow is a roof, and Hom
into a K-injective complex inverts its quasi-isomorphism leg by Lemma 0A95.
Arbitrary second-variable arrows are represented between K-injective complexes;
the equivalence between their homotopy category and the derived category preserves
addition and the constant scalar action. The Hom-complex equations therefore give
separate additivity and linearity for the two derived arrow maps. Conjugating by
the canonical replacement comparisons preserves these equations since composition
is linear for the published constant-section action. Package the simultaneous
arrow action in the two nested linear maps displayed below. No constructibility,
completeness, flatness or boundedness is assumed, and zero objects and torsion
inputs obey the same degreewise formulas. -/
theorem integralDerivedHom_bilinear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u})
    (M M' N N' : DerivedCategory (integralTowerModules l E W)) :
    ∃ b : (M' ⟶ M) →ₗ[Padic.coefficientExtensionIntegers l E]
        (N ⟶ N') →ₗ[Padic.coefficientExtensionIntegers l E]
        ((integralDerivedInternalHom l E W).obj (op M, N) ⟶
          (integralDerivedInternalHom l E W).obj (op M', N')),
      ∀ a b', b a b' = (integralDerivedInternalHom l E W).map (Prod.mkHom a.op b') := by
  let := coefficientModuleLinear l E W
  let standard : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E W)) :=
    Localization.linear _ DerivedCategory.Qh
      (HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ))
  have heq : integralCoefficientLinear l E W = standard := by
    apply coefficientLinear_ext
    intro K K' r f
    rw [(integralCoefficientLinear_existsUnique l E W).exists.choose_spec]
    let := standard
    have hc : integralScalarDerivedAction l E W r =
        Linear.toCatCenter (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory (integralTowerModules l E W)) r := by
      rw [coefficientDerived_eq]
      apply CatCenter.ext_of_localization DerivedCategory.Q
        (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ))
      intro P
      rw [CatCenter.localization_app]
      change DerivedCategory.Q.map (r • 𝟙 P) = r • 𝟙 (DerivedCategory.Q.obj P)
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rw [hc]
    change (r • 𝟙 K) ≫ f = r • f
    simp
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E W)) := integralCoefficientLinear l E W
  let C := completedIntegralCommRingSheafUnrestricted l E W
  let J := AlgebraicGeometry.Scheme.ProEt.topology W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := RingedDerivedNative.moduleMonoidal.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleSymmetric.{u + 1, u, u} J C
  let := RingedDerivedNative.modulePreadditive.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleClosed.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleGrothendieck.{u + 1, u, u} J C
  let := RingedDerivedNative.moduleFlat.{u + 1, u, u} J C
  let : Linear (SheafOfModules.LineEvaluation.scalars.{u + 1, u, u} C)
      (integralTowerModules l E W) :=
    SheafOfModules.LineEvaluation.coefficientLinear.{u + 1, u, u} C
  let : MonoidalLinear (Padic.coefficientExtensionIntegers l E)
      (integralTowerModules l E W) := by
    have hright (P : integralTowerModules l E W) :
        (tensorRight P).Linear (Padic.coefficientExtensionIntegers l E) := by
      constructor
      intro M N f r
      have ht := @SheafOfModules.LineEvaluation.tensor_linear.{u + 1, u, u}
        W.ProEt inferInstance J
        (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
        (inferInstance : J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) C P
      have hh := ht.map_smul f (coefficient_scalarSections l E W r)
      exact hh
    have hleft (P : integralTowerModules l E W) :
        (tensorLeft P).Linear (Padic.coefficientExtensionIntegers l E) := by
      let := hright P
      exact Functor.linear_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight P).symm
    exact
      { whiskerLeft_smul := fun X _ _ r f ↦ (hleft X).map_smul f r
        smul_whiskerRight := fun r _ _ f X ↦ (hright X).map_smul f r }
  obtain ⟨S, hS, _⟩ := RingedDerivedNative.closedAdjunction.{u + 1, u, u} J C
  have hSadd : let := S.monoidal;
      MonoidalPreadditive (DerivedCategory (integralTowerModules l E W)) := by
    rw [hS]
    exact DerivedCategory.monoidalPreadditive
  have hSlin : let := S.monoidal; let := hSadd;
      MonoidalLinear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory (integralTowerModules l E W)) := by
    change @MonoidalLinear (Padic.coefficientExtensionIntegers l E) _
      (DerivedCategory (integralTowerModules l E W)) _ _
      (integralCoefficientLinear l E W) S.monoidal hSadd
    rw [heq]
    revert hSadd
    rw [hS]
    intro hadd
    exact DerivedCategory.monoidalLinear _
  exact closedHom_bilinear _ _ S hSadd hSlin M M' N N'

end WeilConjectures
