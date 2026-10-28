module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! Tensor-side component data for the core reindexing comparison.
(blueprint: lem-pod-reindexing-comparison-core-tensor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

structure ComparisonCoreTensorData {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) where
  tensorChain : ∀ P L : K l E Y s,
    (podReindexingComplexFunctor l E g s).obj ((total l E Y s).obj (P, L)) ≅
      (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj P,
        (podReindexingComplexFunctor l E g s).obj L)
  tensorChain_pure : ∀ (P L : K l E Y s) (p q k : ℤ) (h : p+q=k) (U : X.ProEt)
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (L.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    (((tensorChain P L).hom.f k).val.app (op U))
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
        (podReindexingRing l E Y s) P L p q k h
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X s) ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj L) p q k h (op U) x y
  tensor : SY.tensor ⋙ podReindexingDerivedFunctor l E g s ≅
    ((podReindexingDerivedFunctor l E g s).prod (podReindexingDerivedFunctor l E g s)) ⋙
      SX.tensor


/-- The tensor-side fields can be chosen simultaneously.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 03EL and 07A4
(blueprint: lem-pod-reindexing-comparison-core-tensor-data).
-/
theorem comparison_core_tensor_data_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    Nonempty (ComparisonCoreTensorData l E g s SX SY TX TY) := by
  sorry

end WeilConjectures.PodReindexingCoherence
