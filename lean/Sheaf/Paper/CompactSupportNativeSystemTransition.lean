/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.CompactSupportCoefficientTransition

/-! # Coefficient compatibility of native compact-support systems

Source: Stacks 03DI, 0D6E; Bhatt--Scholze 6.7.6
(blueprint: lem-weil-compact-support-native-system-transition).
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
compact support of that map followed by the normalized coefficient square.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 03DI, 0D6E and 0D6J.
(blueprint: lem-weil-compact-support-native-system-transition).
Proof: first apply the ordinary open-extension coefficient square to the horizontal
map of a module system. Its equality follows by transposing under extension and
restriction: both sides restrict to the same horizontal section map, and the unit
normalizations of moduleEvalJ and compactSupportOpenModel identify the transposes.
Exact localization gives this equality for arbitrary derived systems. Next apply
the direct-image restriction-transition theorem to this extended system. The
proper-image evaluation is evalPMate. Its coefficient mate agrees with the
K-injective normalization of sfDerivedImageRestriction: choose a simultaneous
K-injective system and a K-injective resolution of its smaller-level evaluation
after quotient restriction. The ordinary comparison is identity on its sections,
so both squares are the same localization of that resolution map. This argument
does not require quotient restriction or evaluation to preserve K-injectives.
Compose the two squares, use naturality of proper-image evaluation, and cancel
the open and direct-image model isomorphisms. The resulting coefficient comparison
is exactly sfCompactSupportRestriction, by its definition as those two squares.
The same argument uses any m>=n, including m=n, with no flatness assumption. -/
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
  sorry

end WeilConjectures
