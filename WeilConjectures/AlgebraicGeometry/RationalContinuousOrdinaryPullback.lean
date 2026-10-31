/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRationalRealizationData

/-! # Ordinary normalized rational pullback before completion

Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL and 06YY
(blueprint: lem-per-rational-continuous-ordinary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary coefficient, tensor, and derived-counit data. This record contains
no completed pullback, no restriction to constructible objects, and no comparison of
raw rational realization functors.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL and 06YY
(blueprint: lem-per-rational-continuous-ordinary-pullback). -/
structure OrdinaryPullback {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (αX : pbcAdicCompletion X.scheme (pbcIntegralDatum l E) ⟶
      rationalCoefficientSheaf l X.scheme E)
    (αY : pbcAdicCompletion Y.scheme (pbcIntegralDatum l E) ⟶
      rationalCoefficientSheaf l Y.scheme E) where
  coefficient : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y.scheme E) ⟶
    rationalCoefficientSheaf l X.scheme E
  normalized : rationalCoefficientRestrictionNormalized l E g coefficient
  square : (adicTowerInverseImage g).map αY ≫ coefficient =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ αX
  [ordinaryAdditive : (modulePull g coefficient).Additive]
  counit : DerivedCategory.Q ⋙ derivedPull g coefficient ⟶
    (modulePull g coefficient).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized_counit : IsNormalizedPullCounit g coefficient counit
  universal : (derivedPull g coefficient).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  computes : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E)
      P → IsIso (counit.app P)
  balance : pbcExtend αY ⋙ modulePull g coefficient ≅
    pbcActualModulePull g (pbcIntegralDatum l E) ⋙
      pbcExtend αX
  balance_sections : ∀ (M : pbcModules Y.scheme (pbcAdicCompletion Y.scheme
      (pbcIntegralDatum l E))) (U : Y.scheme.ProEt)
      (a : (rationalCoefficientSheaf l Y.scheme E).obj.obj (op U)) (m : M.val.obj (op U)),
    (balance.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g coefficient ((pbcExtend αY).obj M) U
        (pbcTensorSection αY M (op U) a m)) =
      pbcTensorSection αX
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj U))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ coefficient).hom.app
          (op U) a) (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M U m)
  ambient : pbcDerivedExtend αY ⋙
      derivedPull g coefficient ≅
    pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
      pbcDerivedExtend αX
  balanceComplex :
    (pbcExtend αY).mapHomologicalComplex (.up ℤ) ⋙
        (modulePull g coefficient).mapHomologicalComplex (.up ℤ) ≅
      (pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend αX).mapHomologicalComplex (.up ℤ)
  balanceComplex_components : ∀ P (n : ℤ),
    (balanceComplex.hom.app P).f n = balance.hom.app (P.X n)
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (pbcAdicCompletion Y.scheme (pbcIntegralDatum l E))) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := pbcAdicCompletion Y.scheme (pbcIntegralDatum l E)) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := pbcAdicCompletion Y.scheme (pbcIntegralDatum l E)) (P.X n)) →
    (derivedPull g coefficient).map
        (pbcComplexCounit αY P) ≫
        counit.app (((pbcExtend αY).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ DerivedCategory.Q.map (balanceComplex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend αX).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit αX
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P)

attribute [instance] OrdinaryPullback.ordinaryAdditive

/-- Ordinary pullback admits the multiplication-normalized counit and balanced
integral-to-rational tensor comparison, before applying any completion.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03EL, 06YY and 0G7E
(blueprint: lem-per-rational-continuous-ordinary-pullback).

Proof: take the continuous coefficient structural map, the adjunct of precomposition
by the first pullback projection. The finite quotient comparisons are unique on locally
constant sections, since
they preserve constants. The normalizations of the inverse integral comparison on all
positive quotients then identify the completed integral comparisons with the canonical
ones. Testing coefficient maps on these quotients identifies their integral square;
inclusion in the rational functions then
proves the displayed coefficient square. In each section ring cancel identity scalar
extension by multiplication, with inverse m mapped to 1 tensor m. The inverse-image
scalar-unit normalization theorem proves these are natural sheaf maps with the specified
pure-section formula. Apply this isomorphism termwise to the old inverse-image
computation isomorphism and compose it with the scalar-extension computation counit.
The composite represents left derived ringed pullback, by the K-flat resolving-class
construction and uniqueness of its counit-compatible comparison. Exact geometric
inverse image preserves K-flat complexes, so this counit computes on them. For a K-flat
input without flat terms, first choose a flat-term K-flat resolution. Tensor preserves
its quasi-isomorphism because both complexes are K-flat, so the computation isomorphism
for the resolution transfers to the given input by naturality of the counit.
For the balance map flatten e tensor (b tensor m) to eb tensor m; its inverse inserts
one. The coefficient square makes these formulas balanced. Sheafification extends the
maps and the same formulas prove naturality and inverse identities. Linearity in e
proves balance_sections for arbitrary continuous rational sections. Applying these maps
termwise defines balanceComplex and its component equation. On flat-term K-flat
representatives the ordinary/derived computation isomorphisms identify the balanced
chain map with ambient; the universal property descends it to all derived objects.
The equality on representatives is precisely ambient_normalization. All arguments
are local sheaf tensor arguments and also apply to the empty scheme. -/
theorem rationalContinuousOrdinaryPullback {X Y : Base.{u} l}
    (g : X.scheme ⟶ Y.scheme) (aX : At l E X) (aY : At l E Y) :
    Nonempty (OrdinaryPullback l E g (aX.integralIso.hom ≫ aX.inclusion)
      (aY.integralIso.hom ≫ aY.inclusion)) := by sorry

end AlgebraicGeometry.Scheme.ContinuousRational
