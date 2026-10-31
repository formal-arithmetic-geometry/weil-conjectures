/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapSummand
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapModel
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapSummand
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison

/-! # Signed swap through the explicit native tensor model

Source: Stacks 06YU, 0FPT; blueprint step 3 of
`lem-sf-native-weil-tensor-ringed-derived-square-native-data`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- The explicit localized native model carries the ringed braiding to the signed swap.

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 0FPT; the summand
calculation in step 3 of lem-sf-native-weil-tensor-ringed-unit-symmetry-representatives.
(blueprint: lem-sf-native-weil-tensor-ringed-swap-localization).

Proof: apply the fully faithful native derived equivalence to the braiding of
the transported structure. Its tensor and counit formulas identify this with
the ringed braiding. Apply cB.symmetry_model to the images of the two K-flat
complexes, which are K-flat by A.flat. Replace its simultaneous tensor models by
cB.tensorIso using tensorIso_both, and expand nativeWeilRingedTensorModel.
After cancellation of these models, the equality is a chain comparison.
On a bidegree (p,q) summand, A.summand and hchain identify the two native total
inclusions. The uncurrying equations A.uncurry and he, together with b.hom_square,
identify their underived tensor maps across b.square. The underived symmetry
square b.underived.coherence.symmetry and the signed-swap equation hswap give
the same factor (-1)^(pq) on both sides; additivity preserves this factor.
Balanced tensor extensionality and coproduct extensionality give equality of
chain maps. Localize, use naturality of mapDerivedCategoryFactors, and cancel
the native equivalence and its counits. This gives the displayed identity for
all native K-flat pairs. It uses no chosen ordinary derived tensor model and
asserts no equation for a derived tensor comparison or a unit. -/
-- STATEMENT-DISPUTED: the bridge has no normalization forcing the underived
-- symmetry equation used in the proposed proof; see report.md for the twisting obstruction.
theorem native_weil_tensor_ringed_swap_localization
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (he : ∀ (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I),
      e.inv.app (P, Q) ≫
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
            (((adj.adj P).homEquiv Q I).symm f) =
        ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f)
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (swap : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber Q P)
    (hswap : NativeOrdinarySignedSwap l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber swap)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
    let F := nativeForget k₀ l X
    let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let Pc := (U.mapHomologicalComplex (.up ℤ)).obj P
    let Qc := (U.mapHomologicalComplex (.up ℤ)).obj Q
    F.map ((nativeWeilRingedSymmetric b SB βB).toBraidedCategory.braiding
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        U.mapDerivedCategoryFactors.hom.app (CochainComplex.mapBifunctor P Q T) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      F.map (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).hom ≫
        U.mapDerivedCategoryFactors.hom.app (CochainComplex.mapBifunctor Q P T) ≫
        DerivedCategory.Q.map (chain Q P).hom ≫
        DerivedCategory.Q.map (swap Qc Pc).hom := by
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
