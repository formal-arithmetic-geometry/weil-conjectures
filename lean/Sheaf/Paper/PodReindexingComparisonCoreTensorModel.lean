module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! Tensor model normalization for the core reindexing comparison.
(blueprint: lem-pod-reindexing-comparison-core-tensor-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

structure ComparisonCoreTensorModelData {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (tensorChain : ∀ P L : K l E Y s,
      (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
        (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
          (podReindexingComplexFunctor l E g s).obj L))
    (tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
      ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
        SX.tensor) where
  tensor_model : ∀ (P L : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L),
    ∃ (hFP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E
        g s).obj P))
      (hFL : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := podReindexingRing l E X s) ((podReindexingComplexFunctor l E
        g s).obj L)),
      (podReindexingDerivedFunctor l E g s).map
        ((@CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} _ _ (ProEt.topology Y)
          _ _ (podReindexingRing l E Y s) (HasDerivedCategory.standard.{u + 1, u + 2} _) SY
            TY).hom.app (⟨P, hP⟩, ⟨L, hL⟩)) ≫
        tensor.hom.app ((podReindexingQ l E Y s).obj P, (podReindexingQ l E Y s).obj L) ≫
        SX.tensor.map (Prod.mkHom ((podReindexingDerivedFactors l E g s).hom.app P)
          ((podReindexingDerivedFactors l E g s).hom.app L)) =
      (podReindexingDerivedFactors l E g s).hom.app ((total l E Y s).obj (P, L)) ≫
        (podReindexingQ l E X s).map (tensorChain P L).hom ≫
        (@CoefficientTensorModels.comparison.{u, u + 1, u, u + 2} _ _ (ProEt.topology X)
          _ _ (podReindexingRing l E X s) (HasDerivedCategory.standard.{u + 1, u + 2} _) SX
            TX).hom.app (⟨_, hFP⟩, ⟨_, hFL⟩)

/-- The tensor model normalization is available for the reindexing data.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 07A4
(blueprint: lem-pod-reindexing-comparison-core-tensor-model).
-/
theorem comparison_core_tensor_model_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (tensorChain : ∀ P L : K l E Y s,
      (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
        (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
          (podReindexingComplexFunctor l E g s).obj L))
    (tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
      ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
        SX.tensor) :
    Nonempty (ComparisonCoreTensorModelData l E g s SX SY TX TY tensorChain tensor) := by
  sorry

end WeilConjectures.PodReindexingCoherence
