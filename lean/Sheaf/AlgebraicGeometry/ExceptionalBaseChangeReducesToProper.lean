/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Base change for an exceptional right adjoint reduces to the proper part

Source: Weil conjectures blueprint,
`sec-smooth-purity/sk-prop-sf-existence/cor-exc-base-change-reduces-to-proper.md`,
order 1812 (blueprint: cor-exc-base-change-reduces-to-proper).

Finite constant-coefficient sheaves are transported through the existing canonical
intrinsic realization. All pullbacks, open adjunctions, and square comparisons below
are constructed from the existing site operations, rather than supplied as arbitrary data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The coefficient ring at positive level `n + 1`, covering precisely all positive levels.
Source: blueprint order 1812 (blueprint: cor-exc-base-change-reduces-to-proper). -/
noncomputable abbrev exceptionalCoefficientRing (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

/-- Finiteness supplied by the existing coefficient theorem, not an additional hypothesis.
Source: blueprint order 1812 (blueprint: cor-exc-base-change-reduces-to-proper). -/
noncomputable instance exceptionalCoefficientRing_finite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (exceptionalCoefficientRing l E n) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/--
Base change for a separated finite-type morphism is obtained by pasting the
open-immersion mate with the proper mate.  The conclusion is conditional on
the supplied ambient exceptional right adjoint data and on invertibility of
the proper comparison; no ambient datum is asserted unconditionally.

Source: Weil conjectures blueprint,
`sec-smooth-purity/sk-prop-sf-existence/cor-exc-base-change-reduces-to-proper.md`,
order 1812 (blueprint: cor-exc-base-change-reduces-to-proper).

Proof:
1. By `def-weil-ambient-exceptional-adjoint`, the left adjoints are `J ⋙ P`
   and `J' ⋙ P'`. Apply `prop-exc-open-adjoint` to each open immersion, then
   compose with `adjP` and `adjP'`. By `lem-cat-right-adjoint-composition`
   (`Adjunction.rightAdjointUniq`), obtain the unit/counit-compatible canonical
   isomorphisms `rho : Rf^× ≅ Q ⋙ j^*` and `rho' : Rf'^× ≅ Q' ⋙ j'^*`.
2. The two pullback-composition comparisons of
   `lem-weil-pbc-proetale-derived-pullback-composition`, transported through the
   constant-module equivalences, give `alpha : j^* ⋙ g'^* ≅ gbar^* ⋙ j'^*`.
   `sfIntrinsicDerivedSquarePullback` constructs this comparison from the
   ordinary site composition isomorphism and its termwise derived descent.
3. Under `def-weil-pbc-adjunction-mate`, the inverse mate of `alpha.hom` is
   `gamma : g'^* ⋙ J' ⟶ J ⋙ gbar^*`. Whisker by `P'` and paste with `deltaP`.
   By clause (2) of `lem-weil-pbc-mate-pasting` (`mateEquiv_hcomp`), its mate
   for the composite adjunctions is `alpha` whiskered by `Q`, followed by
   `betaP` whiskered by `j'^*`. Clause (3), using the compatible identifications
   from Step 1, identifies the ambient mate in the conclusion with this map:
   componentwise, `rho' ∘ beta_f` equals
   `j'^*(betaP) ∘ alpha ∘ g'^*(rho)`.
4. Thus `beta_f = rho'⁻¹ ∘ j'^*(betaP) ∘ alpha ∘ g'^*(rho)`.
   The three comparison isomorphisms are invertible, and the hypothesis makes
   `betaP` invertible. Functors preserve inverse pairs, and reversing and
   inverting the four factors supplies an inverse for every component.
-/
theorem exceptionalBaseChangeReducesToProper
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ)
    {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (c : Compactification f)
    (X' : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (c' : Compactification f')
    (overlineG : c'.Z ⟶ c.Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hsq : IsPullback g' f' f g)
    (hbar : IsPullback overlineG c'.g c.g g)
    (hopen : IsPullback g' c'.i c.i overlineG)
    (ambient : SfAmbientExceptionalRightAdjointDatum (exceptionalCoefficientRing l E n) f c)
    (ambient' : SfAmbientExceptionalRightAdjointDatum (exceptionalCoefficientRing l E n) f' c')
    (Q : proEtaleDerivedCategory Y (exceptionalCoefficientRing l E n) ⥤
      proEtaleDerivedCategory c.Z (exceptionalCoefficientRing l E n))
    (Q' : proEtaleDerivedCategory Y' (exceptionalCoefficientRing l E n) ⥤
      proEtaleDerivedCategory c'.Z (exceptionalCoefficientRing l E n))
    (adjP : proEtaleConstantDerivedDirectImage c.g (exceptionalCoefficientRing l E n) ⊣ Q)
    (adjP' : proEtaleConstantDerivedDirectImage c'.g (exceptionalCoefficientRing l E n) ⊣ Q')
    (deltaP : (sfIntrinsicDerivedPullback (exceptionalCoefficientRing l E n) overlineG) ⋙
      proEtaleConstantDerivedDirectImage c'.g (exceptionalCoefficientRing l E n) ⟶
      proEtaleConstantDerivedDirectImage c.g (exceptionalCoefficientRing l E n) ⋙
        (sfIntrinsicDerivedPullback (exceptionalCoefficientRing l E n) g))
    (betaP : Q ⋙ (sfIntrinsicDerivedPullback (exceptionalCoefficientRing l E n) overlineG) ⟶
      (sfIntrinsicDerivedPullback (exceptionalCoefficientRing l E n) g) ⋙ Q')
    (hbetaP : betaP = (mateEquiv adjP adjP' (TwoSquare.mk _ _ _ _ deltaP)).natTrans) :
    IsIso betaP →
      IsIso ((mateEquiv (ambient.adjunction c) (ambient'.adjunction c')
        (TwoSquare.mk _ _ _ _
          ((Functor.whiskerRight
              ((mateEquiv
                (exceptionalOpenAdjunction c.i (exceptionalCoefficientRing l E n))
                (exceptionalOpenAdjunction c'.i (exceptionalCoefficientRing l E n))).symm
                (TwoSquare.mk _ _ _ _
                  (sfIntrinsicDerivedSquarePullback (exceptionalCoefficientRing l E n)
                    g' c'.i c.i overlineG hopen.w).hom)).natTrans
              (proEtaleConstantDerivedDirectImage c'.g
                (exceptionalCoefficientRing l E n))) ≫
            Functor.whiskerLeft
              (sfIntrinsicDerivedOpen (exceptionalCoefficientRing l E n) c.i)
              deltaP))).natTrans) := by
  sorry

end AlgebraicGeometry.Scheme
