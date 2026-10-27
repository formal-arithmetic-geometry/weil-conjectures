/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.SystemOperationExchangeRealization
import Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection

/-! # The transpose of the realized compact-support scalar map

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

/-- Before using any universal property, the realized proper/open scalar comparison
has the specified mixed-unit transpose. No natural isomorphism b is assumed or chosen.
Source: lem-fix-operation-reduction, compact-support and final paragraphs, second
normalization step; Stacks 0GL6 (remark-Rf-lower-shriek-change-of-rings)
(blueprint: lem-sf-compact-support-realized-scalar-transpose).
Proof: expand coefficientExchange as scalar alpha, the limit of systemCompactScalar,
and scalar beta. Naturality of the whole-system reduction counit moves the system
mate through the counit; the reduction/limit triangular identity cancels the inserted
reconstruction pair. The projection equations for compactRealization identify the
remaining operation counits with the fixed finite reduction isomorphisms. The scalar
counit is the coherent reduction comparison. Its K-flat tensor association sends the
mixed unit to the scalar unit, including the zero shifted Roos coordinate. The
proper adjunction mate and inverse open adjunction mate defining systemCompactScalar
then transpose to compact support of the input mixed unit followed by the canonical
restriction comparison. Mate pasting and the normalized ordinary units give the
displayed equality in the derived category, before invoking any uniqueness of lifts.
This uses naturality of the actual counits, never faithfulness of finite evaluation. -/
theorem sfCompactSupportRealizedScalarTranspose
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    let FX := sfCompactSupportFiniteIntegralFunctor l K₀ hl c E
    let TX := sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
    let q := (integralScalarExtension l E L ι Y).map
        ((FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app K) ≫
      (FrobeniusExchange.coefficientExchange l E L ι
        (FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g)
        (FrobeniusExchange.systemDerivedOpen l L c.i ⋙ FrobeniusExchange.systemDirect l L c.g)
        (FrobeniusExchange.systemCompactScalar l E L ι c)).app K ≫
      (FrobeniusExchange.compactRealization l L K₀ hl f c).inv.app (TX.obj K)
    sfMixedCompletedReductionUnit l E L ι Y n (FX.obj K).obj ≫
        (proEtaleCoefficientRestrictScalars Y
          (integralScalarQuotientMap l E L ι n)).mapDerivedCategory.map
          ((scalarReductionDerivedExtension l L Y n).map q ≫
            (sfCompactSupportFiniteReductionIso l K₀ hl c L (TX.obj K) n).hom) =
      (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom ≫
        (sfAmbientCompactSupportCandidate
          (Padic.coefficientExtensionRing l E (n + 1)) c).map
          (sfMixedCompletedReductionUnit l E L ι X n K.obj) ≫
        (sfCompactSupportRestriction c
          (integralScalarQuotientMap l E L ι n)).hom.app
          ((scalarReductionDerivedExtension l L X n).obj (TX.obj K).obj)  := by
  let TX := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
  let R := (proEtaleCoefficientRestrictScalars Y
    (integralScalarQuotientMap l E L ι n)).mapDerivedCategory
  let r := sfCompactSupportFiniteReductionIso l K₀ hl c L (TX.obj K) n
  apply (cancel_mono (R.map r.inv)).1
  simpa only [TX, R, r] using
    sfCompactSupportRealizedScalarTransposeProjection l K₀ hl c E L ι K n

end WeilConjectures
