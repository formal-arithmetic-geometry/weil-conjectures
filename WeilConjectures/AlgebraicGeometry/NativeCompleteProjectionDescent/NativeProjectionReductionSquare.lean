/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionDescentMaps
public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionPullCoherence
public import WeilConjectures.PoincareDuality.ProjectionFormulaCompactificationIso

/-! # Descent of the actual compact-support projection mate

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraphs (2)--(3)
(blueprint: lem-sp-complete-projection-reduction-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  Functor.mapDerivedCategory SheafOfModules.changeOfRings SheafOfModules.monoidalCategory
  reductionEpsilon reductionGenerator ordinaryReduction
  derivedTowerEquivalence towerEquivalence reduction totalLimit

variable (m : DescentModels l E)

/-- The normalized reduction square for the compact-support projection.
Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3), and
the node's proof steps 1--5
(blueprint: lem-sp-complete-projection-reduction-square).

Proof: the tensor and pullback reduction models identify the whole-system
comparisons with the canonical scalar-extension comparisons: on flat K-flat
representatives both send a quotient tensor generator to the two quotient
augmentation generators. The representative squares descend to the unbounded
derived categories. Apply the ringed exchange/tensor coherence theorem to the
proper counit mate. For the open factor, transpose the inverse projection maps
under the open adjunction; the normalized open scalar inverse is its mate, and
both transposes are unit tensor identity. Thus the open square commutes before
any evaluation. Transposing the defining openLimit and properLimit formulas,
unit naturality and both triangle identities identify reconstruction with
properScalar followed by the proper image of openScalar. Paste the proper and
open tensor squares, using naturality of properScalar and the canonical
pullback compositor. This gives the displayed square. It uses no completeness,
boundedness, finite-type assumption, or invertibility of reconstruction. -/
theorem projection_reduction_square
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (AX : Limit l E X (m.abelian X) (m.red X))
    (AZ : Limit l E c.Z (m.abelian c.Z) (m.red c.Z))
    (AY : Limit l E Y (m.abelian Y) (m.red Y))
    (M : Integral l E X) (K : Integral l E Y)
    (hOpen : IsIso (systemOpenInverse l E m c.i ((red l E m X).obj M)
      ((VaryingRing.G (rings l E) (transitions l E) c.g).obj ((red l E m Y).obj K)))) :
    (red l E m Y).map
        (CondensedRing.exceptionalProjectionMorphismOfCompactification
          (spIntegralCondensed l E) c M K) ≫
      reconstruction l E m c AX AZ AY (inputTensor l E m f M K) ≫
      (systemImage l E c).map ((m.tensor X).mu.hom.app (M, (ringedPull l E f).obj K) ≫
        (m.systems X).closed.tensor.map (Prod.mkHom (𝟙 _) ((m.pull f).hom.app K))) =
    (m.tensor Y).mu.hom.app ((integralImage l E c).obj M, K) ≫
      (m.systems Y).closed.tensor.map
        (Prod.mkHom (reconstruction l E m c AX AZ AY M) (𝟙 _)) ≫
      systemProjection l E m c ((red l E m X).obj M) ((red l E m Y).obj K) hOpen := by
  obtain ⟨e, he⟩ : ∃ e, e = CondensedRing.leftDerivedUpperStarCompactificationIso
    (spIntegralCondensed l E) c := ⟨_, rfl⟩
  exact Adjunction.compactification_projection_reduction_square (m.tensor X).mu
    (m.tensor c.Z).mu (m.tensor Y).mu (ringedOpenAdj l E c.i) (ringedAdj l E c.g)
    (VaryingRing.jAdj (rings l E) (transitions l E) c.i)
    (VaryingRing.adj (rings l E) (transitions l E) c.g)
    (fun C ↦ (VaryingRing.gComp (rings l E) (transitions l E) c.i c.g).inv.app C ≫
      eqToHom (congrArg (fun g : X ⟶ Y ↦
        (VaryingRing.G (rings l E) (transitions l E) g).obj C) c.comm.symm))
    (m.systemPull c.i).iso (m.systemPull c.g).iso (m.pull c.i) (m.pull c.g) (m.pull f)
    (m.openScalar c.i) (pull_tensor_coherence m c.i) (pull_tensor_coherence m c.g)
    (m.openScalar_normalized c.i) M K
    (hq := CondensedRing.isIso_openImmersionProjectionComparison _ c.i M _) (hs := hOpen)
    (e.inv.app K) (pull_compactification m c K e he)
    (CondensedRing.exceptionalProjectionMorphismOfCompactification
      (spIntegralCondensed l E) c M K)
    (CondensedRing.exceptionalProjectionMorphismOfCompactification_eq _ c M K e he)
    _ (reconstruction_eq m c AX AZ AY M) _ (reconstruction_eq m c AX AZ AY _)
    (systemProjection l E m c ((red l E m X).obj M) ((red l E m Y).obj K) hOpen) rfl

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
