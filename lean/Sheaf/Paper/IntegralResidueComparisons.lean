/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coherent perfect coefficient comparisons for integral reduction

Source: Bhatt--Scholze, Lemma 6.5.9(3), and associativity of derived coefficient change.
(blueprint: lem-weil-pbc-integral-residue-comparisons)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Ambient derived category used by the coefficient-comparison interface. -/
abbrev residueExchangeDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))

/-- Derived pullback with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeUpperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ Y ⥤ residueExchangeDerived Λ X :=
  L((f)^*⟦Λ⟧)

/-- Derived direct image with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeLowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ X ⥤ residueExchangeDerived Λ Y :=
  R((f)_*⟦Λ⟧)

/-- The actual derived adjunction, expressed through the typed functor interface. -/
@[irreducible] noncomputable def residueExchangeAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar Λ f ⊣ residueExchangeLowerStar Λ f :=
  by
    unfold residueExchangeUpperStar residueExchangeLowerStar
    exact derivedUpperStarLowerStarAdjunction Λ f

/-- The actual derived coefficient reduction with its two categories exposed. -/
@[irreducible] noncomputable def residueExchangeReduction (X : Scheme.{u}) :
    residueExchangeDerived (integralCoeff ℓ E) X ⥤
      residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X :=
  integralReduction ℓ E X

/-- The library's canonical composition comparison, with typed pull functors. -/
@[irreducible] noncomputable def residueExchangeUpperStarComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    residueExchangeUpperStar Λ (f ≫ g) ≅
      residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f :=
  by
    unfold residueExchangeUpperStar
    exact leftDerivedUpperStarComp Λ f g

/-- Pullback comparisons for actual derived reduction, compatible with composition.
The data concern arbitrary schemes and morphisms, without constructibility or base change.
Source: Bhatt--Scholze, Remark 6.8.15, and associativity of derived tensor.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
structure IntegralResiduePullComparisons where
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ≅
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f
  comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Z))),
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app K) ≫
        (pull f).hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
        (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((pull g).hom.app K) =
      (pull (f ≫ g)).hom.app K ≫
        (residueExchangeUpperStarComp
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app
            ((residueExchangeReduction ℓ E Z).obj K)

namespace IntegralResiduePullComparisons

variable {ℓ E} (c : IntegralResiduePullComparisons.{u} ℓ E)

/-- The direct-image comparison is the adjunction mate of the inverse pull comparison.
This is an actual construction; no direct-image isomorphism is chosen.
Source: Bhatt--Scholze, Lemma 6.5.9(3), projection comparison by adjunction.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
noncomputable def push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeLowerStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E Y ⟶
      residueExchangeReduction ℓ E X ⋙
        residueExchangeLowerStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  (mateEquiv (residueExchangeAdjunction (integralCoeff ℓ E) f)
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
      (TwoSquare.mk _ _ _ _ (c.pull f).inv)).natTrans

/-- The defining counit equation for the actual direct-image comparison.
Source: Mathlib, mateEquiv_counit.
(blueprint: lem-weil-pbc-integral-residue-push-counit)
Proof. Apply the counit identity of the mates equivalence to the inverse pull comparison.
-/
theorem push_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((c.push f).app K) ≫
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).counit.app
        ((residueExchangeReduction ℓ E X).obj K) =
    (c.pull f).inv.app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeReduction ℓ E X).map
        ((residueExchangeAdjunction (integralCoeff ℓ E) f).counit.app K) := by
  exact mateEquiv_counit (residueExchangeAdjunction (integralCoeff ℓ E) f)
    (residueExchangeAdjunction
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (TwoSquare.mk _ _ _ _ (c.pull f).inv) K

end IntegralResiduePullComparisons

/-- Perfect residue change admits coherent pull comparisons whose direct-image mates
are invertible on the unbounded ambient derived categories.

Source: Bhatt--Scholze, Lemma 6.5.9(3), with the two-term perfect coefficient resolution;
Remark 6.8.15 for the pull-composition constraints.
(blueprint: lem-weil-pbc-integral-residue-comparisons)

Proof. Derive the underived scalar-pull comparison on K-flat resolutions. It identifies
A_X tensor f* K with f* (A_Y tensor K) by associativity of relative tensor and the
canonical coefficient pullback isomorphism. The associativity pentagon and the
coefficientMap composition equations give precisely the displayed composition law,
with the library's leftDerivedUpperStarComp constraints. These equalities can be checked
on K-flat representatives using uniqueness of the derived functor comparison.

The assumed tensor description identifies restriction of scalar reduction with derived
tensor by the residue regular module in degree zero. The direct-image mate of the
preceding canonical pull comparison becomes, after exact restriction, the usual perfect
projection comparison. For a dualizable coefficient this comparison is invertible:
use the coefficient dual's tensor adjunction to identify both sides as right adjoints
of the same tensor-pull functor. Its conjugate isomorphism is the projection map by
the counit characterization of mates. Apply the supplied perfectness to A_Y, and the
canonical coefficient-pull isomorphism identifies its pullback with A_X. Finally exact
faithful restriction of scalars reflects derived isomorphisms by its homology comparison.
Thus every actual push mate is invertible. This uses no boundedness, constructibility,
properness or Cartesian square. Empty schemes and zero complexes are allowed. -/
theorem integralResidue_comparisons
    (hPerfect : ∀ T : Scheme.{u},
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))))
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ c : IntegralResiduePullComparisons.{u} ℓ E,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (c.push f) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
