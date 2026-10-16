/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.IntegralResidueTensorPresentation
public import Sheaf.Paper.IntegralResidueDerivedMonoidal
public import Sheaf.Paper.IntegralResidueOrdinaryMonoidal

/-! # Ordinary pullback data and the derived residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Remark 6.8.15.
(blueprint: new-integral-residue-tensor-geometry)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Pullback identifies the restricted residue regular coefficient in degree zero.
The isomorphism is constructed using exact pullback and its ordinary unit comparison. -/
@[irreducible] noncomputable def residueExchangeCoefficientPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y) ≅ residueExchangeCoefficient ℓ E X := by
  let A := Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)
  let P := Mod.regular (condensedRingObj A Y)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (integralReductionMap ℓ E) X)
  letI := residueOrdinaryUpperStarMonoidal A f
  let e : (f)^*⟦integralCoeff ℓ E⟧.obj (SY.obj P) ≅
      SX.obj (Mod.regular (condensedRingObj A X)) :=
    (comapUpperStarIso (integralReductionMap ℓ E) f).symm.app P ≪≫
      SX.mapIso (Functor.Monoidal.εIso (f)^*⟦A⟧).symm
  unfold residueExchangeUpperStar
  exact ((f)^*⟦integralCoeff ℓ E⟧.singleFunctorCompLeftDerivedFunctorIso).app (SY.obj P) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

/-- The tensor presentation on X, with its coefficient identified with pullback from Y. -/
@[irreducible] noncomputable def residueExchangeTensorPullIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X ≅
      tensorRight ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        (residueExchangeCoefficient ℓ E Y)) :=
  residueExchangeTensorIso ℓ E X ≪≫
    (curriedTensor (residueExchangeDerived (integralCoeff ℓ E) X)).flip.mapIso
      (residueExchangeCoefficientPullIso ℓ E f).symm

/-- Ordinary pullback has a strong monoidal structure preserving flat modules,
and its derived tensor comparison agrees with the canonical scalar pull square.
The monoidal structure and both tensor presentations have already been constructed.

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15, balanced tensor associativity.
(blueprint: new-integral-residue-tensor-geometry)

Proof. On ordinary module objects, apply inverse image to the two balanced action
maps defining relative tensor. Inverse image preserves their coequalizer and its
ambient tensor comparison is invertible. The coefficient-pullback isomorphism
identifies the base rings, giving the ordinary tensor comparison. Its unit map is
the coefficient-pullback isomorphism on regular modules. Precompose the unit and
associativity diagrams with the tensor presentation epimorphisms: both sides are
the corresponding unit or associativity equation in the ambient inverse image.
This is the proved residueExchangeOrdinaryPullMonoidal. Inverse image preserves
flat modules: flatness is local and
is preserved by scalar extension, and the coefficient change here is an
isomorphism. This gives hFlat. The derived strong monoidal structure is the
already constructed residueExchangePullMonoidal, computed on flat resolutions.
The coefficient-pullback comparison identifies the pullback of the restricted
regular residue module in degree zero with the corresponding module on X.
Compose that coefficient isomorphism with residueExchangeTensorIso on X to give
tX. On flat resolutions the asserted square is the balanced tensor associativity
square: both routes multiply the same scalar factors. The comparison
residueExchangePullHom is the inverse mate of restriction/pullback, so its scalar
counit identity identifies it with this scalar multiplication comparison. The
canonical tensor presentation uses exactly the extension counit followed by the
balanced tensor isomorphism, hence the square is the stated one, with no freedom
to replace that presentation by an arbitrary automorphism. Uniqueness of left
derived comparisons descends the equality to every complex M. The argument does
not require flatness of the residue coefficient over the integral coefficient,
and applies also to the zero complex and the empty scheme. -/
theorem integralResidue_tensorGeometry {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat,
        letI := residueExchangePullMonoidal ℓ E f
          (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
          ∀ M : residueExchangeDerived (integralCoeff ℓ E) Y,
            (residueExchangeUpperStar (integralCoeff ℓ E) f).map
                ((residueExchangeTensorIso ℓ E Y).hom.app M) ≫
              Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
                M (residueExchangeCoefficient ℓ E Y) =
            (residueExchangeRestrictPullIso ℓ E f).hom.app
                ((residueExchangeReduction ℓ E Y).obj M) ≫
              (residueExchangeRestriction ℓ E X).map
                (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
              (residueExchangeTensorPullIso ℓ E f).hom.app
                ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
