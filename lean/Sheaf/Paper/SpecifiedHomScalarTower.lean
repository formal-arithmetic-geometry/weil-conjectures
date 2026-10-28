/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteRationalDerivedOperations
public import Sheaf.Paper.SfScalarExtensionComposition
/-! Rational tower coherence for the specified Hom comparison.
(blueprint: lem-zl-specified-hom-scalar-evaluation). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
/-- The specified Hom comparison satisfies scalar tower coherence after rationalization.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: localize the integral tower equation and cancel the normalized completion units. -/
theorem specifiedHomScalarRational_tower (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory)
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) :
      (sfRationalScalarExtension l L X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).map
          (rationalHomScalarComparison l E L ι X P).hom ≫
        (rationalHomScalarComparison l L F j X (rationalHomScalarPair l E L ι X P)).hom ≫
        (rationalDerivedInternalHom l F X).map
          (ObjectProperty.homMk
            (X := rationalHomScalarPair l L F j X (rationalHomScalarPair l E L ι X P))
            (Y := rationalHomScalarPair l E F (j.comp ι) X P)
            (Prod.mkHom
              (((sfRationalScalarComp l E L ι X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).inv.app P.obj.1.unop).op)
              ((sfRationalScalarComp l E L ι X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app P.obj.2))) =
        (sfRationalScalarComp l E L ι X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F j).hom.app
            ((rationalDerivedInternalHom l E X).obj P) ≫
          (rationalHomScalarComparison l E F (j.comp ι) X P).hom := by
  sorry
end WeilConjectures
