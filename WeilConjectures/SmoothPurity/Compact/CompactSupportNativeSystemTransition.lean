/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientTransition
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeOpenTransition
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeDirectTransition

/-! # Coefficient compatibility of native compact-support systems

Native compact-support evaluation is compatible with the horizontal coefficient maps
`B_m → B_n`.

## Implementation details

The square is obtained by composing the ordinary open-extension coefficient square with the
direct-image restriction-transition square, using naturality of proper-image evaluation; the
resulting coefficient comparison is `sfCompactSupportRestriction` by definition. The argument
does not require quotient restriction or evaluation to preserve K-injectives, and uses no
flatness assumption.

## References

* Bhatt–Scholze, 6.7.6–6.7.7
* [Stacks, Tags 03DI, 0D6E and 0D6J](https://stacks.math.columbia.edu/tag/0D6E)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Native compact-support evaluation carries every horizontal coefficient map to
compact support of that map followed by the normalized coefficient square. -/
theorem compactSupportNativeSystemTransition
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) (M : coefficientSequenceDerived.{u, u} l E X) :
    (compactSupportCoefficientTransition l E Y h).app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i ⋙
          ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.g).obj M) ≫
      (proEtaleCoefficientRestrictScalars Y
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.map
          ((compactSupportSystemEvaluation l E c n).hom.app M) =
    (compactSupportSystemEvaluation l E c m).hom.app M ≫
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
        ((compactSupportCoefficientTransition l E X h).app M) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj M) := by
  let A := fun k ↦ Padic.coefficientExtensionRing l E (k + 1)
  let J := ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i
  let P := fun k ↦ proEtaleConstantDerivedDirectImage c.g (A k)
  let eJ := fun k ↦ compactSupportNativeOpenEvaluation l E c.i k
  let eP := fun k ↦ compactSupportNativeDirectEvaluation l E c.g k
  let R := (proEtaleCoefficientRestrictScalars Y
    (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
  let aJ := Functor.mapDerivedCategorySquareIso
    (sfOpenRestriction c.i (compactSupportLevelQuotient l E m n h))
  let aP := sfDerivedImageRestriction c.g (compactSupportLevelQuotient l E m n h)
  have he (k : ℕ) : (compactSupportSystemEvaluation l E c k).hom.app M =
      (eP k).hom.app (J.obj M) ≫ (P k).map ((eJ k).hom.app M) := by
    simp only [compactSupportSystemEvaluation, eP, eJ,
      compactSupportNativeDirectEvaluation, compactSupportNativeOpenEvaluation,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
    rfl
  rw [he n, he m]
  have hJ := compactSupportNativeOpenTransition l E c.i h M
  have hP := compactSupportNativeDirectTransition l E c.g h (J.obj M)
  have hn := aP.hom.naturality ((eJ n).hom.app M)
  dsimp only [Functor.comp_map] at hn
  change (compactSupportCoefficientTransition l E Y h).app _ ≫
      R.map ((eP n).hom.app (J.obj M) ≫ (P n).map ((eJ n).hom.app M)) =
    ((eP m).hom.app (J.obj M) ≫ (P m).map ((eJ m).hom.app M)) ≫
      (P m).map ((sfIntrinsicExtensionByZero c.i (A m)).mapDerivedCategory.map
        ((compactSupportCoefficientTransition l E X h).app M)) ≫
      ((P m).map (aJ.hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj M)) ≫
        aP.hom.app ((sfIntrinsicExtensionByZero c.i (A n)).mapDerivedCategory.obj
          ((coefficientSequenceDerivedEvaluation l E X n).obj M)))
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hP, ← hn]
  rw [← (P m).map_comp_assoc]
  erw [hJ]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end WeilConjectures
