/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PointTateFiberComparisonData
import Sheaf.Paper.PointTateFiberCanonicalComparisons
import Sheaf.Paper.PointTateFiniteSectionComparison
import Sheaf.Paper.PointTateNormalizedSectionGenerators
import Sheaf.Paper.PointTateDerivedComparisonCoordinates
import Sheaf.Paper.PointTateCommonStageCoherence

/-! # Canonical coefficient comparisons on signed point Tate lines

Source: main-20261015, def-weil-frobenius-coefficient-twists, finite-reduction
and scalar-extension sentence; Deligne, Weil II (1.1.3), p. 150.
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Retain the point target's published small derived Hom universe. The residue-lisse
-- API's standard-size instance otherwise captures module categories at a larger size.
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Canonical reduction, localization and completed scalar comparisons in all signed
root-line coordinates. Tensor factors are in change-of-rings order (new scalar first).
The maps are fixed on arbitrary sections, not just abstract isomorphisms of free lines.

Source: main-20261015, def-weil-frobenius-coefficient-twists, finite-reduction and
scalar-extension sentence; Deligne, Weil II (1.1.3), p. 150.
(blueprint: lem-pur-point-tate-fiber-coefficient-comparisons).

Proof:
1. Apply normalizedSectionGenerators (lem-pur-point-tate-normalized-section-generators)
to the prescribed root section. It gives one family g of integral generators at all
finite coefficient fields: the positive root tensors, the negative generators evaluating
to one, positive finite reduction, and preservation by every signed scalar map. Take
the finite section isomorphisms z from finiteSectionComparison
(lem-pur-point-tate-finite-section-comparison).
2. Take the constructed canonicalSheaf, canonicalIntegral and canonicalRational
(def-pur-point-tate-canonical-comparisons). Their tensor formulas, applied to g and its
preservation by the scalar maps, give both generator formulas; rationalization
compatibility cancels an isomorphism with its inverse.
3. For negative finite reduction apply the dual-evaluation clause of
signedTwistReduction_comparison to g in degrees -(r+1) and r+1: the integral evaluation
is one and the coefficient quotient preserves one. For localization of a times g apply
pointFibreRationalDown_existsUnique to one tensor a times g; balancing moves a.
4. canonicalDerivedCoordinates (lem-pur-point-tate-derived-comparison-coordinates)
gives the rational normalization, the completed sections square and the rational point
square for the constructed maps.
5. The identity and tower equations are the proved canonicalIntegral_identity,
canonicalIntegral_tower, canonicalRational_identity and canonicalRational_tower.
6. canonicalCommonStage (lem-pur-point-tate-common-stage-coherence) at M and at N
identifies the fixed twistPairComparison with both common-stage representatives. The
defining representative formula of pointQbarFibre gives the two heterogeneous
equalities; rewriting and transitivity give equality of the two representatives. -/
theorem coefficientComparisons (hl : l ≠ D.p)
    (e : (purTwistZlOne (Spec (.of D.k)) l).obj.obj (finalObject D))
    (he : ∀ r : ℕ, IsPrimitiveRoot
      (rootValue D (l ^ (r + 1))
        ((limit.π (proEtaleRootsOfUnityTower (Spec (.of D.k)) l Fact.out) (op r)).hom.app
          (finalObject D) e)) (l ^ (r + 1))) :
    ∃ (g : ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (m : ℤ), integral D l F m)
      (z : FiniteComparisons D l) (β : SheafComparisons D l)
      (α : IntegralComparisons D l) (ρ : RationalComparisons D l),
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (r : ℕ),
      g F (r : ℤ) = positiveGenerator D l F e r) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (r : ℕ),
      integralEvaluate D l F r (g F (Int.negSucc r))
        (positiveGenerator D l F e (r + 1)) = 1) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (n : ℕ) (m : ℤ)
        (a : Padic.coefficientExtensionRing l F (n + 1)) (x : integral D l F m),
      (z F n m).hom (a ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))] x) =
        a • (@id (finite D l F n m)
          ((reduction D l F hl n m).val.app (finalObject D) x))) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (n r : ℕ),
      (reduction D l F hl n (r : ℤ)).val.app (finalObject D) (g F (r : ℤ)) =
        finiteTateProPowerGenerator l F n (Spec (.of D.k)) (finalObject D) 1 r
          (fun _ ↦ e)) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (n r : ℕ),
      finiteEvaluate D l F n r
        ((reduction D l F hl n (Int.negSucc r)).val.app (finalObject D)
          (g F (Int.negSucc r)))
        ((reduction D l F hl n ((r + 1 : ℕ) : ℤ)).val.app
          (finalObject D) (g F ((r + 1 : ℕ) : ℤ))) = 1) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (m : ℤ),
      (rationalLineNormalization D l F hl m).hom =
        (rationalSizeNormalization D l F hl m).hom ≫
          (Functor.mapDerivedCategory.{u + 1, u + 2, u + 1, u + 1, u + 2, u + 2}
            (pointFibreCoefficientDown F)).map
            (rawRationalSingle D l F m).hom ≫
          ((pointFibreCoefficientDown F).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((pointFibreRationalDown_existsUnique D l F).exists.choose.hom.app
              (integralTwistLine l F (Spec (.of D.k)) m)) ∧
      ∀ a : Padic.coefficientExtensionIntegers l F,
        ((pointFibreRationalDown_existsUnique D l F).exists.choose.hom.app
          (integralTwistLine l F (Spec (.of D.k)) m))
          ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
            (pointIntegralToField l F)).unit.app
            ((pointIntegralSections l F D.k).obj
              (integralTwistLine l F (Spec (.of D.k)) m)) (a • g F m)) =
        (a : F) • ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] g F m)) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : F →ₐ[Padic l] L) (m : ℤ),
      (∀ (U : (Spec (.of D.k)).ProEtᵒᵖ)
          (b : (completedIntegralCommRingSheafUnrestricted l L (Spec (.of D.k))).obj.obj U)
          (x : (integralTwistLine l F (Spec (.of D.k)) m).val.obj U),
        (β F L ι m).hom.val.app U
          (completedScalarTensorSection l F L ι (Spec (.of D.k)) _ U b x) =
        b • (@id ((integralTwistLine l L (Spec (.of D.k)) m).val.obj U)
          ((scalarMap D l F hl L ι m).val.app U x))) ∧
      (α F L ι m).hom =
        (pointSectionsTensor D.k l F L ι).hom.app (integralTwistLine l F (Spec (.of D.k)) m) ≫
          (pointCompletedSections D.k l L).map (β F L ι m).hom ∧
      (DerivedCategory.singleFunctor _ 0).map (α F L ι m).hom =
        completedSectionsComparison D l F hl L ι m β ∧
      (∀ b : Padic.coefficientExtensionIntegers l L,
        (α F L ι m).hom (b ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          integralScalarIntegerInclusion l F L ι] g F m) = b • g L m) ∧
      (∀ b : L, (ρ F L ι m).hom
        (b ⊗ₜ[F, ι.toRingHom] ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] g F m)) =
        b • ((1 : L) ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          algebraMap (Padic.coefficientExtensionIntegers l L) L] g L m)) ∧
      (pointModuleRationalization l L).map (α F L ι m).hom =
        ((pointTensorRationalization_existsUnique l F L ι).exists.choose).hom.app
          (integral D l F m) ≫ (ρ F L ι m).hom) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : F →ₐ[Padic l] L) (m : ℤ),
      letI := frobeniusPointPrimeInvertible D l hl
      (Functor.mapDerivedCategory.{u, u + 2, u, u + 1, u + 1, u + 2}
        (ModuleCat.uliftFunctor.{u + 1, u} L)).map
          (rationalPointComparison D l F hl L ι m β).hom.hom ≫
        (rationalLineNormalization D l L hl m).hom =
      (pointFibreTensorLiftIso l F L ι).hom.app
          ((pointRationalFibre D l hl F).obj
            (sfRationalTwistingCoefficient l F (Spec (.of D.k)) m)).obj ≫
        (pointCoefficientFieldDerivedTensor l F L ι).map
          (rationalLineNormalization D l F hl m).hom ≫
        ((ModuleCat.extendScalars ι.toRingHom).mapDerivedCategorySingleFunctor 0).hom.app
          (rational D l F m) ≫
        (DerivedCategory.singleFunctor _ 0).map (ρ F L ι m).hom) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (m : ℤ),
      (α F F (AlgHom.id (Padic l) F) m).hom =
        ((pointIntegralModuleUnit_existsUnique l F).exists.choose).hom.app (integral D l F m) ∧
      (ρ F F (AlgHom.id (Padic l) F) m).hom =
        (ModuleCat.extendScalarsId.{u, u + 1} F).hom.app (rational D l F m)) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : F →ₐ[Padic l] L)
        (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
        (κ : L →ₐ[Padic l] M) (m : ℤ),
      (pointIntegralModuleTensor l L M κ).map (α F L ι m).hom ≫ (α L M κ m).hom =
        ((pointIntegralModuleAssoc_existsUnique l F L ι M κ).exists.choose).hom.app
          (integral D l F m) ≫ (α F M (κ.comp ι) m).hom ∧
      (ModuleCat.extendScalars κ.toRingHom).map (ρ F L ι m).hom ≫ (ρ L M κ m).hom =
        (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
          (rational D l F m) ≫
          (ρ F M (κ.comp ι) m).hom) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
        (F L M N : Padic.FiniteCoefficientFields l Ω) (hFL : F ≤ L)
        (hFM : F ≤ M) (hLM : L ≤ M) (hMN : M ≤ N) (m : ℤ),
      HEq ((pointQbarFibre D l hl Ω).map
          (twistPairComparison D l hl Ω F L hFL m β))
        (pointQbarFibreRepresentative D l hl Ω
          (twistPair D l hl Ω F m) (twistPair D l hl Ω L m) M hFM hLM
          ((stageLineComparison D l hl Ω F M hFM m β).hom ≫
            (stageLineComparison D l hl Ω L M hLM m β).inv)) ∧
      pointQbarFibreRepresentative D l hl Ω
        (twistPair D l hl Ω F m) (twistPair D l hl Ω L m) M hFM hLM
        ((stageLineComparison D l hl Ω F M hFM m β).hom ≫
          (stageLineComparison D l hl Ω L M hLM m β).inv) =
      pointQbarFibreRepresentative D l hl Ω
        (twistPair D l hl Ω F m) (twistPair D l hl Ω L m) N
        (hFM.trans hMN) (hLM.trans hMN)
        ((stageLineComparison D l hl Ω F N (hFM.trans hMN) m β).hom ≫
          (stageLineComparison D l hl Ω L N (hLM.trans hMN) m β).inv)) := by
  classical
  obtain ⟨g, hgpos, hgeval, hgred, hgscalar⟩ :=
    normalizedSectionGenerators D l hl e he
  obtain ⟨z, hz⟩ := finiteSectionComparison D l hl
  obtain ⟨hloc, hcompleted, hpoint⟩ := canonicalDerivedCoordinates D l hl
  refine ⟨g, z, canonicalSheaf D l hl, canonicalIntegral D l hl,
    canonicalRational D l hl, hgpos, hgeval, hz, hgred, ?_, ?_, ?_, hpoint, ?_, ?_, ?_⟩
  · intro F _ _ _ n r
    let := frobeniusPointPrimeInvertible D l hl
    have h := ((signedTwistReduction_comparison l F
      (Spec (.of D.k))).1 n).exists.choose_spec.1.2.2.2 r (finalObject D)
        (g F (Int.negSucc r)) (g F ((r + 1 : ℕ) : ℤ))
    have hh : integralEvaluate D l F r (g F (Int.negSucc r))
        (g F ((r + 1 : ℕ) : ℤ)) = 1 := by
      rw [hgpos]
      exact hgeval F r
    exact h.trans ((congrArg
      ((completedIntegralCommRingProjectionUnrestricted l F (Spec (.of D.k)) n).hom.app
        (finalObject D)) hh).trans (map_one _))
  · intro F _ _ _ m
    refine ⟨hloc F m, ?_⟩
    intro a
    have h := (pointFibreRationalDown_existsUnique D l F).exists.choose_spec
      (integralTwistLine l F (Spec (.of D.k)) m) 1 (a • g F m)
    change ((pointFibreRationalDown_existsUnique D l F).exists.choose.hom.app
      (integralTwistLine l F (Spec (.of D.k)) m))
      ((1 : ULift.{u + 1, u} F) ⊗ₜ[ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l F), pointIntegralToField l F] (a • g F m)) = _
    exact h.trans (by
      let := (algebraMap (Padic.coefficientExtensionIntegers l F) F).toAlgebra
      erw [← TensorProduct.smul_tmul]
      rfl)
  · intro F _ _ _ L _ _ _ ι m
    refine ⟨canonicalSheaf_tensor D l hl F L ι m, rfl,
      hcompleted F L ι m, ?_, ?_, canonicalRational_compatibility D l hl F L ι m⟩
    · intro b
      exact (canonicalIntegral_tensor D l hl F L ι m b (g F m)).trans
        (congrArg (fun x : integral D l L m ↦ b • x) (hgscalar F L ι m))
    · intro b
      have h := canonicalRational_tensor D l hl F L ι m b (g F m)
      have hh := congrArg (fun x : integral D l L m ↦
        b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          algebraMap (Padic.coefficientExtensionIntegers l L) L] x) (hgscalar F L ι m)
      exact h.trans (hh.trans (by
        rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]))
  · intro F _ _ _ m
    exact ⟨canonicalIntegral_identity D l hl F m, canonicalRational_identity D l hl F m⟩
  · intro F _ _ _ L _ _ _ ι M _ _ _ κ m
    exact ⟨canonicalIntegral_tower D l hl F L ι M κ m,
      canonicalRational_tower D l hl F L ι M κ m⟩
  · intro Ω _ _ _ F L M N hFL hFM hLM hMN m
    have hM := canonicalCommonStage D l hl Ω F L M hFL hFM hLM m
    have hN := canonicalCommonStage D l hl Ω F L N hFL
      (hFM.trans hMN) (hLM.trans hMN) m
    have hφ := (pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.2
    have hm := hφ (twistPair D l hl Ω F m) (twistPair D l hl Ω L m) M hFM hLM
      ((stageLineComparison D l hl Ω F M hFM m (canonicalSheaf D l hl)).hom ≫
        (stageLineComparison D l hl Ω L M hLM m (canonicalSheaf D l hl)).inv)
    have hn := hφ (twistPair D l hl Ω F m) (twistPair D l hl Ω L m) N
      (hFM.trans hMN) (hLM.trans hMN)
      ((stageLineComparison D l hl Ω F N (hFM.trans hMN) m
          (canonicalSheaf D l hl)).hom ≫
        (stageLineComparison D l hl Ω L N (hLM.trans hMN) m
          (canonicalSheaf D l hl)).inv)
    rw [← hM] at hm
    rw [← hN] at hn
    exact ⟨hm, eq_of_heq (hm.symm.trans hn)⟩

end WeilConjectures.PointTateFiber
