module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! Hom-side component data for the core reindexing comparison.
(blueprint: lem-pod-reindexing-comparison-core-hom-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

structure ComparisonCoreHomData {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) where
  chain : ∀ P I : K l E Y s,
    (podReindexingComplexFunctor l E g s).obj (hom l E Y s P I) ≅
      hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I)
  chain_projection : ∀ (P I : K l E Y s) (r p : ℤ) (U V : X.ProEt) (a : V ⟶ U)
    (f : ((hom l E Y s P I).X r).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj V))),
    (((proj l E X s ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) r p (p+r) rfl).val.app (op U)
        (((chain P I).hom.f r).val.app (op U) f)).app (op (Over.mk a))).hom x =
      (((proj l E Y s P I r p (p+r) rfl).val.app
        (op ((proEtaleIsoPostcompose g).obj U)) f).app
          (op (Over.mk ((proEtaleIsoPostcompose g).map a)))).hom x
  derived : podReindexingDerivedHom l E Y s ⋙ podReindexingDerivedFunctor l E g s ≅
    ((podReindexingDerivedFunctor l E g s).op.prod (podReindexingDerivedFunctor l E g s)) ⋙
      podReindexingDerivedHom l E X s
  derived_model : ∀ (P I : K l E Y s) (hI : I.IsKInjective),
    ∃ hFI : CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I),
      derived.hom.app (op ((podReindexingQ l E Y s).obj P),
        (podReindexingQ l E Y s).obj I) =
      (podReindexingDerivedFunctor l E g s).map
        (@podReindexingHomModel l _ E _ _ _ Y s P I hI).hom ≫
      (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s P I) ≫
      (podReindexingQ l E X s).map (chain P I).hom ≫
      (@podReindexingHomModel l _ E _ _ _ X s
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) hFI).inv ≫
      ((podReindexingDerivedHom l E X s).mapIso
        (((podReindexingDerivedFactors l E g s).app P).op.prod
          ((podReindexingDerivedFactors l E g s).app I).symm)).hom

/-- The Hom-side fields can be chosen simultaneously.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX and 0A8X
(blueprint: lem-pod-reindexing-comparison-core-hom-data).
-/
theorem comparison_core_hom_data_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    Nonempty (ComparisonCoreHomData l E g s SX SY TX TY) := by
  sorry

end WeilConjectures.PodReindexingCoherence
