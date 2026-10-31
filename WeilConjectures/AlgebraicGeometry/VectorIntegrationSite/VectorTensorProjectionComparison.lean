/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import all WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CoefficientFirstCompactSupportSiteSquare

/-! # Coefficient-first vector projection comparison
Source: Stacks 099R, 0944, 0GL1 and 0B65.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource Etale.derivedTensorRightDerivedLowerShriek
  Etale.projectionMap Etale.rightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] AlgebraicGeometry.Etale.derivedTensorSymmetry
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

private theorem vector_twisted_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) S K) :
    DerivedCategory.TStructure.t.plus
      (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) := by
  let W := Etale.vectorIntegrationCoefficient A N hA S d F
  let f := VectorBundleZeroSection.π S d F
  let X := VectorBundleZeroSection.scheme S d F
  let B := ModuleCat.{u + 1} A
  let Pe := Etale.ordinaryFinitePullback A f
  obtain ⟨a, b, htor⟩ := hK.2
  have hWb : DerivedCategory.TStructure.t.bounded W :=
    (Etale.purityAtModulus N hN A hA S hS d F).2.1
  have hD : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor B X).obj W).obj (Pe.obj K)) :=
    Etale.plus_derivedTensor_leftDerivedUpperStar f hWb htor
  exact (DerivedCategory.TStructure.t.plus).prop_of_iso
    (((Etale.derivedTensorSymmetry B X).app W).app (Pe.obj K)) hD


/-- The two actual coefficient-first projections are invertible and compare through the
canonical proper/open site comparison. Source: Stacks 099R, 0944 and 0GL1; the projection
calculation in Steps 1--2 of lem-pur-integration-exponent-transpose-transport.
(blueprint: lem-pur-vector-tensor-projection-comparison).

Proof: the finite Tate coefficient is a shifted finite locally free line. Finite Tor
amplitude of K therefore makes its twisted pullback bounded below. The ordinary projection
formula gives pe. The proper counit-mate tensor square, pasted with the exact open-extension
tensor square, compares the actual compact-support projection maps. Conjugate this square
by the canonical signed symmetries to put K first. The ordinary projection is invertible,
and the site and tensor comparisons are isomorphisms, so the pro-etale projection is
invertible as well; take its inverse for pp. The resulting equation is the asserted square.
Rank zero uses the tensor unit; over the empty scheme the unique arrows satisfy the square.
No finite-type-over-a-field hypothesis, dimension bound, or flatness over Z/N is used.
-/
theorem vectorTensorProjectionComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) S K)
    (hW : DerivedCategory.TStructure.t.plus
      (Etale.vectorIntegrationCoefficient A N hA S d F))
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F))
    (he : e = (compactSupportSiteComparison A
      (Etale.vectorBundlePurityCompactification S d F)).app
        ⟨_, hW⟩) :
    ∃ (hM : DerivedCategory.TStructure.t.plus
          (Etale.vectorBundlePurityTwistedPullback A N hA S d F K))
      (pe : (Etale.vectorBundlePurityLower A S d F).obj
          (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
          (Etale.vectorIntegrationSource A N hA S d F))
      (pp : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (Etale.vectorBundlePurityCompactification S d F)).obj
            ((comparison A _).obj
              (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)) ≅
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj ((comparison A S).obj K)).obj
          (genericVectorSource A N hA S d F)),
      pe.inv = Etale.vectorBundlePurityProjectionMap A N hA S d F K ∧
      HEq pp.inv (comparedModuleProjection A
        (Etale.vectorBundlePurityCompactification S d F)
        (Etale.vectorIntegrationCoefficient A N hA S d F) K) ∧
      (tensorComparison A S K (Etale.vectorIntegrationSource A N hA S d F)).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) S).obj ((comparison A S).obj K)).map
            e.inv ≫ pp.inv =
        (comparison A S).map pe.inv ≫
          (compactSupportSiteComparison A
            (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩ := by
  have hM := vector_twisted_plus A N hN hA S hS d F K hK
  obtain ⟨pe, hpe, _⟩ := (Etale.purityAtModulus N hN A hA S hS d F).2.2.2.2 K
  obtain ⟨pp, hpp, hp⟩ := coefficientFirstCompactSupportSiteSquare A N hA
    S d F K hW hM pe hpe e he
  exact ⟨hM, pe, pp, hpe, hpp, hp⟩

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
