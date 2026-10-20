/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.GroupTheory.Torsion
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite-pushforward reduction of the tensor comparison

Source: Stacks Project, Tag 0F1J, final finite-pushforward diagram and calculation
(blueprint: lem-kun-0f1j-finite-pushforward-comparison).

The arrows below are actual composites of exchange, projection and unit maps.
The theorem asserts that these specified arrows are isomorphisms and intertwine
specified adjunction mates. All objects are viewed in the unbounded derived category
through the fully faithful inclusion of D⁺. In particular, for finite π, Rπ_* of the
constant complex is canonically π_* of the degree-zero constant sheaf, and Rπ'_* is
canonically the exact termwise π'_*. This is the finite-exactness identification in
the node, not an extra resolution-acyclicity hypothesis.
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Arrows

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]

/-- Exchange for the constant complex, followed by its canonical inverse-image unit
identification. Source: Stacks Project, Tags 0959 and 0F1J
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finiteConstantExchange
    {I X I' X' : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} (sq : CommSq pI π' π p) :
    L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _)) ⟶ R((π')_*[A]).obj (𝟙_ _) :=
  (derivedBaseChangeMap A sq).app (𝟙_ _) ≫
    R((π')_*[A]).map (leftDerivedUpperStarUnitIso A pI).hom

/-- The source reduction arrow: finite constant exchange, the canonical projection
map and the left unitor. Source: Stacks Project, Tags 0F1J and 0F0G
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finiteConstantTensorReduction
    {I X I' X' : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} (sq : CommSq pI π' π p)
    (B : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    ((derivedTensor A X').obj (L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _)))).obj B ⟶
      R((π')_*[A]).obj (L((π')^*[A]).obj B) :=
  ((derivedTensor A X').map (finiteConstantExchange A sq)).app B ≫
    ((rightDerivedLowerStarProjectionMap A π').app (𝟙_ _)).app B ≫
    R((π')_*[A]).map (derivedTensorLeftUnitor A I' (L((π')^*[A]).obj B)).hom

/-- The target reduction arrow: pull back constant exchange, apply the same finite
projection arrow for ρ, and identify the two composite direct images by conjugating
the canonical square inverse-image isomorphism. Source: Stacks Project, Tag 0F1J;
Tags 0D6E and 0DV0 for composition
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finiteConstantTensorTargetReduction
    {I X I' X' J Y : Scheme.{u}} {π : I ⟶ X} {p : X' ⟶ X}
    {pI : I' ⟶ I} {π' : I' ⟶ X'} {h : Y ⟶ X'}
    {hI : J ⟶ I'} {ρ : J ⟶ Y}
    (sq : CommSq pI π' π p) (sqI : CommSq hI ρ π' h)
    (V : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    R((h)_*[A]).obj (((derivedTensor A Y).obj
      (L((h)^*[A]).obj (L((p)^*[A]).obj (R((π)_*[A]).obj (𝟙_ _))))).obj V) ⟶
    R((π')_*[A]).obj (R((hI)_*[A]).obj (L((ρ)^*[A]).obj V)) :=
  R((h)_*[A]).map
    (((derivedTensor A Y).map (L((h)^*[A]).map (finiteConstantExchange A sq))).app V ≫
      finiteConstantTensorReduction A sqI V) ≫
    (conjugateIsoEquiv
      ((derivedUpperStarLowerStarAdjunction A π').comp
        (derivedUpperStarLowerStarAdjunction A hI))
      ((derivedUpperStarLowerStarAdjunction A h).comp
        (derivedUpperStarLowerStarAdjunction A ρ))
      (derivedSquareUpperStarIso A sqI)).inv.app (L((ρ)^*[A]).obj V)

/-- The untensored comparison, with iterated inverse images rather than their
composition abbreviations: its transpose is ρ⁻¹ of the square counit for g.
Source: Stacks Project, Tag 0F1J
(blueprint: lem-kun-0f1j-finite-pushforward-comparison). -/
noncomputable def finitePushforwardUntensoredComparison
    {I' X' J Y S' T : Scheme.{u}} {π' : I' ⟶ X'}
    {h : Y ⟶ X'} {hI : J ⟶ I'} {ρ : J ⟶ Y}
    {e : Y ⟶ T} {f' : X' ⟶ S'} {g : T ⟶ S'}
    (sqI : CommSq hI ρ π' h) (sqG : CommSq e h g f')
    (F : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    L((π')^*[A]).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶
      R((hI)_*[A]).obj (L((ρ)^*[A]).obj (L((e)^*[A]).obj F)) :=
  (derivedUpperStarLowerStarAdjunction A hI).homEquiv _ _
    ((derivedSquareUpperStarIso A sqI).inv.app
        (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ≫
      L((ρ)^*[A]).map
        ((derivedSquareUpperStarIso A sqG).hom.app (R((g)_*[A]).obj F) ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)))

end Arrows

/-- Finite pushforward reduces the specified tensor comparison to the specified
untensored comparison. The four cartesian squares use the projections of the node;
iterated inverse images represent (fᵢ')⁻¹ and eᵢ⁻¹ through their canonical composition
isomorphisms. The first two conjuncts make the two displayed reduction arrows into
canonical isomorphisms. The third is equality of the actual maps. The fourth is the
stated implication of invertibility.

Source: Stacks Project, Tag 0F1J, final finite-pushforward diagram and calculation
(blueprint: lem-kun-0f1j-finite-pushforward-comparison).

Proof plan, in the eight steps of the node:
1. Base changes π' and ρ are finite and proper (lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-finite-proper). Finite direct image is exact on abelian sheaves
   (lemma-weil-pbc-finite-direct-image-exact); exact faithful coefficient forgetting
   gives module exactness (lem-weil-pbc-module-sheaves-colimits-forgetful).
   The canonical exact-derived comparison identifies Rπ'_* and Rρ_* with their
   termwise functors (lem-weil-pbc-exact-functor-derived-functor).
2. Finite exchange identifies P = p⁻¹π_*k with π'_*k, and h⁻¹π'_*k with ρ_*k
   (lemma-weil-pbc-finite-exchange, lem-weil-pbc-exchange-forget-coefficients).
   Inverse image preserves the constant sheaf and its compositions are module-linear
   (prop-weil-pbc-inverse-image-modules-exact,
   lem-weil-pbc-inverse-image-composition-module-linear).
3. Apply the proper torsion projection formula to π', its constant unit and A
   (lem-kun-0f0g). Its projection arrow is def-kun-projection-formula-map,
   transposed to the counit tensored with the identity; use
   lem-kun-inverse-image-monoidal and the left unitor. This is the first arrow.
4. Apply the same construction to ρ and V. Derived direct-image composition
   (lem-weil-pbc-ringed-topoi-derived-pushforward-composition) for
   ρ followed by h and hᵢ followed by π' gives the second arrow.
5. These composition isomorphisms identify successive Hom transposes: exact inverse
   image makes direct image preserve K-injectives
   (lem-weil-pbc-right-adjoint-preserves-kinjective). On one such representative
   composition is the ordinary composite adjunction (def-weil-pbc-composite-adjunction).
6. Transpose the tensor comparison followed by the second arrow twice. Naturality
   and the projection transpose formula give
   (ε_ρ composed with ρ⁻¹E) tensor ρ⁻¹δ, where E is finite exchange and δ is e⁻¹ε_g.
7. Transpose the first arrow followed by π'_* of the untensored comparison twice.
   It gives hᵢ⁻¹ε_π' tensor ρ⁻¹δ. The defining exchange mate equation
   (def-weil-pbc-underived-exchange) identifies these counit factors. Injectivity
   of the common composite Hom bijection proves the third conjunct.
8. A functor preserves invertibility. Conjugating π'_* of the untensored comparison
   by the two specified isomorphisms makes the tensor comparison invertible. -/
theorem finitePushforward_tensorComparison
    {K : Type u} [Field K]
    {X S' T X' Y I I' J : Scheme.{u}}
    (x : X ⟶ Spec (.of K)) (s : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
    [QuasiCompact g] [QuasiSeparated g]
    (_sqBase : IsPullback p f' x s) (sqG : IsPullback e h g f')
    (π : I ⟶ X) [IsFinite π] (pI : I' ⟶ I) (π' : I' ⟶ X')
    (hI : J ⟶ I') (ρ : J ⟶ Y)
    (sqPi : IsPullback pI π' π p) (sqRho : IsPullback hI ρ π' h)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    IsIso (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).homEquiv _
      _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))) ≫
      (finiteConstantTensorTargetReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqPi.toCommSq sqRho.toCommSq
        (L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) =
      (finiteConstantTensorReduction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sqPi.toCommSq
        (L((f')^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
        R((π')_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
          (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ∧
    (IsIso (finitePushforwardUntensoredComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        sqRho.toCommSq sqG.toCommSq ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) →
      IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
        h).homEquiv _ _
        ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) h).app
          (L((p)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I)))).app (L((f')^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ≫
          ((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) Y).obj
            (L((h)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj (L((p)^*[(ModuleCat.{u + 1}
              (ULift.{u + 1} (ZMod ℓ)))]).obj
          (R((π)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) I))))).map
            ((derivedSquareUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
              sqG.toCommSq).hom.app
              (R((g)_*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
            L((e)^*[(ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))]).map
              ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
                g).counit.app ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))))) := sorry

end AlgebraicGeometry.Etale
