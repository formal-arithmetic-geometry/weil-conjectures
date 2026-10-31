/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData

/-! Component squares of the strict finite projection comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The open projection followed by the compactification pullback compositor
is preserved by the fixed scalar realization. No proper direct image or proper
projection occurs in this square.
Source: blueprint operations proof (2), open mate and pullback composition.
(blueprint: new-lem-sp-strict-finite-open-projection-tail).
Proof: conjugate the ordinary open adjunction by the two module equivalences
and change its right adjoint by openSquarePullbackModel. Naturality of the
ordinary unit and the equivalence triangles give the open coordinate unit
square. Exact localization preserves this equation. The pinned tensor pullback
square, composed with the canonical exact/left-derived comparison for the open
immersion, identifies the mixed restriction tensor map. Transpose the inverse
published open tensor map; its transpose is the unit tensored with the identity
followed by that mixed tensor map. The normalized equation
levels.openTensor_mate gives the same target transpose, so injectivity of the
adjunction Hom bijection identifies the open maps.

For the compositor, evaluate the two ordinary pullback-coordinate composites
on inverse-image unit sections. Both give the iterated unit, with the canonical
fibre-product identification. The uniqueness of the normalized adjoint therefore
identifies them. Localize this square and expand the compactification
exact/left-derived compositor; the comparison factors cancel and c.comm gives
the prescribed intrinsic compositor. Paste it after the open square using tensor
naturality in the second variable and naturality of comparisonFiniteOpen. If
quasi-compactness of the open is used in the representative model, derive it
from quasi-compactness of f and separatedness of c.g. The argument uses no
proper direct image or proper projection, and all unit and tensor universal
properties remain valid for zero coefficients, zero complexes and empty schemes.
-/
theorem strictFiniteOpenProjectionTail (b : Base l E) (o : Operations l E b)
    (levels : ComparisonLevels l E b o)
    (tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n)
    (hpin : (∀ (T : Scheme.{u}) (n : ℕ),
    ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n),
    ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n),
    ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
        (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
          (e.derived.prod e.derived) ⋙ t.functor,
      HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
      HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
      HEq t.functor (comparisonLevelTensor l E b T n) ∧
      ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
      Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
        (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
        (comparisonFiniteConstantSection l E T n) e t d))) :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (n : ℕ)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))),
      (comparisonFiniteRealization l E b c.Z n).map
        (X := (SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) c.Z).obj
            ((openImmersionLowerShriek
                (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory.obj K,
              (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                c.g).leftDerivedFunctor.obj L))
        (Y := (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory.obj
            ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
              (ULift.{u + 1, u} (R l E n)) X).obj
                (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                  f).leftDerivedFunctor.obj L)))
        ((((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).inv.app K).app
            ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              c.g).leftDerivedFunctor.obj L)) ≫
          (openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory.map
            (Y := (SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
              (ULift.{u + 1, u} (R l E n)) X).obj
                (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                  f).leftDerivedFunctor.obj L))
            (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) X).obj K).map
              ((leftDerivedUpperStarCompactificationIso
                (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c).hom.app L))) ≫
      (comparisonFiniteOpen l E b c.i n).hom.app
        ((SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) X).obj
            (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj L)) ≫
      (sfIntrinsicDerivedOpen (R l E n) c.i).map
        ((tensor X n).hom.app
            (K, (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
              f).leftDerivedFunctor.obj L) ≫
          (comparisonLevelTensor l E b X n).map
            (Prod.mkHom (𝟙 _) ((comparisonFinitePull l E b f n).hom.app L))) =
      (tensor c.Z n).hom.app
        ((openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) c.i).mapDerivedCategory.obj K,
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            c.g).leftDerivedFunctor.obj L) ≫
      (comparisonLevelTensor l E b c.Z n).map
        (Prod.mkHom ((comparisonFiniteOpen l E b c.i n).hom.app K)
          ((comparisonFinitePull l E b c.g n).hom.app L)) ≫
      (levels.openTensor c.i n
        ((comparisonFiniteRealization l E b X n).obj K)
        ((proEtaleConstantRingDerivedPullback (R l E n) c.g).obj
          ((comparisonFiniteRealization l E b Y n).obj L))).hom ≫
      (sfIntrinsicDerivedOpen (R l E n) c.i).map
        ((comparisonLevelTensor l E b X n).map
          (Prod.mkHom (𝟙 _)
            (((proEtaleConstantRingPullbackComposition c.i c.g (R l E n)).hom ≫
              eqToHom (congrArg
                (fun h ↦ proEtaleConstantRingDerivedPullback (R l E n) h)
                  c.comm.symm)).app
                    ((comparisonFiniteRealization l E b Y n).obj L)))) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
