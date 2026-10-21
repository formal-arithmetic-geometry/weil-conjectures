/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtalePointPullback

/-!
# Invertibility of powers of ell on continuous rational derived coefficients

Source: Bhatt--Scholze, Section 6.8; blueprint rationalization comparison,
proof of thm-sfb-extend-scalars-localization, "F inverts W"
(blueprint: lem-sfb-rational-derived-scalar-invertible).
-/

@[expose] public section

set_option autoImplicit false

attribute [instance] CategoryTheory.Mod.isGrothendieckAbelian

universe u

open CategoryTheory MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Powers of ell act invertibly on the ordinary unbounded derived category of internal
modules over the actual continuous coefficient ring E_X. The witness t is multiplication
by ell^(-n) on continuous functions. Its value on the ring unit, transported to X, acts
on each degree of the representative C by the displayed unitor/action formula.
Source: Bhatt--Scholze, Section 6.8; blueprint thm-sfb-extend-scalars-localization,
"F inverts W" (blueprint: lem-sfb-rational-derived-scalar-invertible).

Proof: put a = ell^n and b = a^(-1) in E. Since E contains Q_ell, a is nonzero and
ab = ba = 1. Pointwise multiplication gives the corresponding constant sections of
underline E. Pull them back by the strong monoidal upperStarFromPoint X. This inverse
image is a left adjoint between abelian categories, hence preserves finite biproducts
and addition, so the first section is ell^n times the unit. The module action axioms
give m_s m_t = m_(st) and m_1 = id; commutativity makes these module morphisms, and
compatibility of all module maps makes their degreewise actions chain maps A and B.
Thus AB = BA = id and A = ell^n id. By lem-sfb-derived-localization-additive, choose
C and e : Q(C) isomorphic to K. The additive localization Q sends these identities
to inverse identities, with Q(A) = ell^n id. Conjugating Q(B) by e gives the displayed
two-sided inverse on K. This uses every integer degree and no boundedness assumption. -/
theorem rationalDerivedScalar_invertible
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))) (n : ℕ) :
    IsIso ((l ^ n) • 𝟙 K) ∧
    ∃ (t : Profinite.continuousCoefficientRingObj E ⟶
          Profinite.continuousCoefficientRingObj E)
      (C : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)) ℤ)
      (e : DerivedCategory.Q.obj C ≅ K) (B : C ⟶ C),
      (∀ (S : Profinite.{u}) (f : ULift.{u + 1} C(S, E)) (s : S),
        (((t.hom.app (op S)) f).down) s = ((l : E) ^ n)⁻¹ * f.down s) ∧
      (∀ q : ℤ, (B.f q).hom =
        (λ_ (C.X q).X).inv ≫
          ((η[(condensedRingObj (Profinite.continuousCoefficientRingObj E) X)] ≫
            (upperStarFromPoint X).map t) ▷ (C.X q).X) ≫
          ModObj.smul (M := condensedRingObj (Profinite.continuousCoefficientRingObj E) X)
            (X := (C.X q).X)) ∧
      ((l ^ n) • 𝟙 K) ≫ (e.inv ≫ DerivedCategory.Q.map B ≫ e.hom) = 𝟙 K ∧
      (e.inv ≫ DerivedCategory.Q.map B ≫ e.hom) ≫ ((l ^ n) • 𝟙 K) = 𝟙 K := by
  sorry

end AlgebraicGeometry.ProEtale
