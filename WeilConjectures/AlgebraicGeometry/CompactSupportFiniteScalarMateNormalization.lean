/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import WeilConjectures.AlgebraicGeometry.SystemOperationExchangeRealization
import WeilConjectures.AlgebraicGeometry.MixedCompletedReductionHomBijective
import WeilConjectures.AlgebraicGeometry.CompactSupportRealizedScalarTranspose

/-! # A step of normalized compact-support scalar comparison

Source: lem-fix-operation-reduction, compact-support and final paragraphs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The fixed whole-system scalar comparison satisfies the finite tensor-unit mate
normalization. Source: lem-fix-operation-reduction, compact-support and final paragraphs;
normalized scalar isomorphisms, proof steps 1 and 5
(blueprint: lem-sf-compact-support-finite-scalar-mate-normalization).
Proof: identify completed scalar reduction with finite derived extension using the
coherent reduction comparison. The representative-normalized derived adjunction
identifies the mixed unit with its scalar unit. The strict Roos comparison preserves
the augmentation and its zero shifted coordinate, and the effectivity counit is the
adjunct of the same projection, so this is the entire mixed-unit square. Precomposing
with the inverse fixed compact-support reduction gives the Hom bijection for every
unbounded target. Naturality of the whole-system counit identifies reduction of the
realized comparison with the proper/open finite mate. Its transpose is compact support
of the input mixed unit followed by restriction of scalars. The Hom bijection identifies
this map with sfCompactSupportFiniteMate. This proves exactly the specified equation,
without claiming that evaluation is faithful on system morphisms. -/
theorem sfCompactSupportFiniteScalarMateNormalization
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (b : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c L)
    (hb : ∀ K : sfIntegralConstructibleCategory l E X,
      (b.hom.app K).hom = (integralScalarExtension l E L ι Y).map
          ((FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app K) ≫
        (FrobeniusExchange.coefficientExchange l E L ι
          (FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g)
          (FrobeniusExchange.systemDerivedOpen l L c.i ⋙ FrobeniusExchange.systemDirect l L c.g)
          (FrobeniusExchange.systemCompactScalar l E L ι c)).app K ≫
        (FrobeniusExchange.compactRealization l L K₀ hl f c).inv.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)) :
    SfCompactSupportIntegralBetaSpec l K₀ hl c E L ι b := by
  intro K n
  let r := sfCompactSupportFiniteReductionIso l K₀ hl c E K n
  let R := (proEtaleCoefficientRestrictScalars Y
    (integralScalarQuotientMap l E L ι n)).mapDerivedCategory
  let η := sfMixedCompletedReductionUnit l E L ι Y n
    ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj
  have hN (Z : proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l L (n + 1))) :
      Function.Bijective (fun a :
        (scalarReductionDerivedExtension l L Y n).obj
          ((integralScalarExtension l E L ι Y).obj
            ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj) ⟶ Z ↦
        (r.inv ≫ η) ≫ R.map a) := by
    have h := (Iso.homCongr r (Iso.refl (R.obj Z))).bijective.comp
      (sfMixedCompletedReductionHomBijective l E L ι Y _ n Z)
    simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_hom,
      Category.comp_id, Category.assoc, η, R] using h
  refine ⟨hN, ?_⟩
  apply (Equiv.ofBijective _ (hN _)).injective
  unfold sfCompactSupportFiniteMate
  erw [Equiv.apply_symm_apply]
  change (r.inv ≫ η) ≫ R.map
    ((scalarReductionDerivedExtension l L Y n).map (b.hom.app K).hom ≫
      (sfCompactSupportFiniteReductionIso l K₀ hl c L
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) n).hom) = _
  rw [hb K, Category.assoc]
  rw [sfCompactSupportRealizedScalarTranspose l K₀ hl c E L ι K n]
  simp only [r, Iso.inv_hom_id_assoc]

end WeilConjectures
