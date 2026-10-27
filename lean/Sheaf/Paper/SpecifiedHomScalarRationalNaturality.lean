/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteRationalDerivedOperations

/-! The naturality clause for the specified rational Hom comparison.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
This is the rationalized naturality calculation for arbitrary localized arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Rational naturality of the specified Hom comparison for arbitrary localized arrows.
Source: blueprint rational/common-stage paragraphs
(blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: localize the integral comparison and use bilinearity of the rational internal Hom,
with contravariance in the first variable; the universal localization property extends
the equality from integral maps to all localized arrows. -/
theorem specifiedHomScalarRational_naturality (X : Scheme.{u})
    (P P' : (constructibleRationalHomPairs l E X).FullSubcategory)
    (a : P'.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ P'.obj.2) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((rationalDerivedInternalHom l E X).map
          (ObjectProperty.homMk (X := P) (Y := P') (Prod.mkHom a.op b))) ≫
      (rationalHomScalarComparison l E L ι X P').hom =
    (rationalHomScalarComparison l E L ι X P).hom ≫
      (rationalDerivedInternalHom l L X).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l E L ι X P)
          (Y := rationalHomScalarPair l E L ι X P')
          (Prod.mkHom
            (((sfRationalScalarExtension l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map a).op)
            ((sfRationalScalarExtension l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map b))) := by
  sorry

end WeilConjectures
