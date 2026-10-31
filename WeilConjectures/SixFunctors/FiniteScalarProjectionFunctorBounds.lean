/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
import WeilConjectures.SixFunctors.FiniteScalarProjectionCoproducts
import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exactness and coproducts of finite scalar projection functors

Source: the scalar-generator proof of the finite proper projection formula.
(blueprint: lem-coef-finite-scalar-projection-functor-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem finiteTensor_properties (W : Scheme.{u}) (q : ℕ)
    (C : CoefficientClosedStructure (coefficientFiniteInternalHom l E W q))
    (M : normalizedDVRDerived.{u, u} l E W q) :
    let T := Prod.sectL _ M ⋙ C.tensor
    ∃ s : T.CommShift ℤ, letI := s
      T.IsTriangulated ∧
      (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) T) := by
  let H := RingedHomUniverses.hom.{u + 1, u, u}
    (ProEt.topology W) (integralCoefficientCommRingSheaf l E W q) M
  let : H.CommShift ℤ := RingedHomUniverses.homCommShift _ _ M
  have : H.IsTriangulated := RingedHomUniverses.hom_isTriangulated _ _ M
  let := C.monoidal
  let e : (Prod.sectL _ M ⋙ C.tensor) ≅ MonoidalCategory.tensorRight M :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro N N' f
      simp [CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
        MonoidalCategory.tensorRight, Prod.sectL])
  let adj : (Prod.sectL _ M ⋙ C.tensor) ⊣ H :=
    (C.adjunction M).ofNatIsoLeft e.symm
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have := adj.isTriangulated_leftAdjoint
  let := adj.isLeftAdjoint
  exact ⟨inferInstance, inferInstance, fun _ ↦ inferInstance⟩

include hl in
/-- The two scalar functors joined by finite proper projection are exact and
preserve arbitrary small coproducts. The assertion supplies no projection map.
Source: Stacks 07A4, 0941; lem-amb-proper-coproducts and the truncation argument of
lem-amb-proper-coproducts-projection.
(blueprint: lem-coef-finite-scalar-projection-functor-bounds).

Proof: fixed-source derived internal Hom is exact with its recorded target
shift structure. Transfer this structure across the closed tensor adjunction
to fixed right tensor. It preserves coproducts as a left adjoint. Finite
sections is a composite of exact scalar restriction with right derived
sections, so it is triangulated. The supplied sstar inherits exactness and
shifts across its adjunction. Similarly pstar inherits them from right derived
proper image. Composing gives exact shift structures on the two displayed
functors. The source composite consists of left adjoints, hence preserves
coproducts. The separate finite-scalar coproduct theorem supplies preservation
for the target proper-image composite. -/
theorem finiteScalarProjection_functor_bounds
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (q : ℕ) (F : CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G q)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) :
    let c := finiteDualizingCompactification D X
    let P := proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing l E (q + 1))
    let M := (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory.obj
        ((coefficientFiniteDerivedExtension l E X q).obj K)
    let A := F.sstar ⋙ Prod.sectL _ (P.obj M) ⋙ (G.baseTensors.finiteClosed q).tensor
    let B := F.sstar ⋙ F.pstar ⋙ Prod.sectL _ M ⋙
      (G.compactTensors.finiteClosed q).tensor ⋙ P
    ∃ sA : A.CommShift ℤ, letI := sA
      ∃ sB : B.CommShift ℤ, letI := sB
        A.IsTriangulated ∧ B.IsTriangulated ∧
        (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) A) ∧
        (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) B) := by
  let c := finiteDualizingCompactification D X
  let P := proEtaleConstantDerivedDirectImage c.g
    (Padic.coefficientExtensionRing l E (q + 1))
  let M := (sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory.obj
      ((coefficientFiniteDerivedExtension l E X q).obj K)
  obtain ⟨sC, hC, hcC⟩ := finiteTensor_properties l E _ q
    (G.baseTensors.finiteClosed q) (P.obj M)
  obtain ⟨sZ, hZ, hcZ⟩ := finiteTensor_properties l E _ q
    (G.compactTensors.finiteClosed q) M
  let := sC
  let := sZ
  let := hC
  let := hZ
  have (I : Type (u + 1)) := hcC I
  have (I : Type (u + 1)) := hcZ I
  let W := Spec (.of D.k)
  let R0 := (scalarReductionRestriction l E W q).mapDerivedCategory ⋙
    (coefTraceConstantScalars l E W).mapDerivedCategory ⋙
      ((sheafSections (ProEt.topology W) (ModuleCat.{u + 1} (coefTraceRing l E))).obj
        (op (ProEt.mk (𝟙 W)))).rightDerivedFunctor
  have : R0.IsTriangulated := by
    dsimp only [R0]
    infer_instance
  let sectionsAdj : F.sstar ⊣ R0 := F.sectionsAdjunction
  let := sectionsAdj.leftAdjointCommShift ℤ
  have := sectionsAdj.commShift_of_rightAdjoint ℤ
  have := sectionsAdj.isTriangulated_leftAdjoint
  let := sectionsAdj.isLeftAdjoint
  let := F.properAdjunction.leftAdjointCommShift ℤ
  have := F.properAdjunction.commShift_of_rightAdjoint ℤ
  have := F.properAdjunction.isTriangulated_leftAdjoint
  let := F.properAdjunction.isLeftAdjoint
  let A := F.sstar ⋙ (Prod.sectL _ (P.obj M) ⋙ (G.baseTensors.finiteClosed q).tensor)
  let B := ((F.sstar ⋙ F.pstar) ⋙
    (Prod.sectL _ M ⋙ (G.compactTensors.finiteClosed q).tensor)) ⋙ P
  change ∃ sA : A.CommShift ℤ, letI := sA
    ∃ sB : B.CommShift ℤ, letI := sB
      A.IsTriangulated ∧ B.IsTriangulated ∧
      (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) A) ∧
      (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) B)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    (fun _ ↦ inferInstance), ?_⟩
  exact finiteScalarProjection_preservesCoproducts l E X D hl S G q F K hK

end WeilConjectures
