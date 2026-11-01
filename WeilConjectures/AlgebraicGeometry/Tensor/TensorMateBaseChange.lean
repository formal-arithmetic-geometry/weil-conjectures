/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-! # Canonical tensor mates and arbitrary constructible base change

Source: main-20261015, sec-six-functors-basics/sk-prop-cohsm/
lem-pur-co-smooth-composition.proof.md, final base-change sentence
(blueprint: lem-pur-tensor-mate-base-change).

The morphism equality is expressed on every retained etale origin, using precisely
the comparison coordinates of def-pur-co-smoothness. All arrows are mapped by nu*;
this is an equality in the small pro-etale derived category. Canonical pullback,
tensor and coefficient-unit comparisons are written explicitly. The equality uses
omega-first coordinates under canonical symmetry, exactly as the recorded tensor clause. Naturality
and the constructible-origin equivalence make this the equality for every Dctf object,
independent of its origin. The pullback assertion is also stated directly on arbitrary
pro-etale objects, preserving each specified Tor interval. No smoothness or invertibility
of theta, b or beta occurs among the hypotheses.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

-- These proved helpers generalize the corresponding private calculation in
-- WeilConjectures.AlgebraicGeometry.Smooth.SmoothExceptionalBaseChange to an arbitrary Cartesian square.
-- The concrete tensor notation and generic monoidal notation unfold to the same structure.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Scheme.Etale.essentiallySmall
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

-- Naturality and left unitality specialize a two-variable tensor mate to the unit.
private lemma unit_tensor_base_change
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy]
    [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy]
    [MonoidalCategory Cx'] [MonoidalCategory Cy']
    (F R : Cy ⥤ Cx) (F' R' : Cy' ⥤ Cx') (Ga : Cx ⥤ Cx') (Gb : Cy ⥤ Cy')
    (τ : ∀ M N : Cy, R.obj M ⊗ F.obj N ⟶ R.obj (M ⊗ N))
    (τ' : ∀ M N : Cy', R'.obj M ⊗ F'.obj N ⟶ R'.obj (M ⊗ N))
    (β : R ⋙ Ga ⟶ Gb ⋙ R')
    (δa : ∀ M N : Cx, Ga.obj (M ⊗ N) ⟶ Ga.obj M ⊗ Ga.obj N)
    (δb : ∀ M N : Cy, Gb.obj (M ⊗ N) ⟶ Gb.obj M ⊗ Gb.obj N)
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N))
    (e : Gb.obj (𝟙_ Cy) ⟶ 𝟙_ Cy')
    (hτ : ∀ M N : Cy,
      Ga.map (τ M N) ≫ β.app (M ⊗ N) ≫ R'.map (δb M N) =
        δa (R.obj M) (F.obj N) ≫ β.app M ▷ Ga.obj (F.obj N) ≫
          R'.obj (Gb.obj M) ◁ κ N ≫ τ' (Gb.obj M) (Gb.obj N))
    (hτ' : ∀ {M M' : Cy'} (φ : M ⟶ M') (N : Cy'),
      R'.map φ ▷ F'.obj N ≫ τ' M' N = τ' M N ≫ R'.map (φ ▷ N))
    (he : ∀ N : Cy, δb (𝟙_ Cy) N ≫ e ▷ Gb.obj N ≫ (λ_ (Gb.obj N)).hom =
      Gb.map (λ_ N).hom) (N : Cy) :
    Ga.map (τ (𝟙_ Cy) N ≫ R.map (λ_ N).hom) ≫ β.app N =
      δa (R.obj (𝟙_ Cy)) (F.obj N) ≫
        (β.app (𝟙_ Cy) ≫ R'.map e) ▷ Ga.obj (F.obj N) ≫
        R'.obj (𝟙_ Cy') ◁ κ N ≫ τ' (𝟙_ Cy') (Gb.obj N) ≫
        R'.map (λ_ (Gb.obj N)).hom := by
  rw [Ga.map_comp, Category.assoc]
  erw [β.naturality]
  change Ga.map (τ (𝟙_ Cy) N) ≫ β.app (𝟙_ Cy ⊗ N) ≫
    R'.map (Gb.map (λ_ N).hom) = _
  rw [← he, R'.map_comp, R'.map_comp]
  rw [reassoc_of% (hτ (𝟙_ Cy) N)]
  rw [← reassoc_of% (hτ' e (Gb.obj N))]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, whisker_exchange_assoc]

-- The actual compact-support projection/exchange square supplies the abstract mate theorem.
private lemma exceptional_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} {g : S' ⟶ S}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (M N : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.map
        (rightDerivedUpperShriekTensorMap f M N) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq).app
        (M ⊗ N) ≫
      (rightDerivedUpperShriek A f').map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g'
      ((rightDerivedUpperShriek A f).obj M)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)).hom ≫
      (rightDerivedUpperShriekBaseChangeMap A sq).app M ▷
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj N)) ≫
      ((rightDerivedUpperShriek A f').obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)) ◁
          (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
            sq.toCommSq N) ≫
      rightDerivedUpperShriekTensorMap f'
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj M)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap A sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction A f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f').app M).app N)
    (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) f').naturality φ) N)
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      g' M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap A sq)
    (inv (rightDerivedLowerShriekBaseChangeMap A sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

-- Only compact-support exchange and projection maps are inverted in this calculation.
private lemma dualizing_tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} {g : S' ⟶ S}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (K : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.map
        (dualizingComplexTensorMap A f K) ≫
      (rightDerivedUpperShriekBaseChangeMap A sq).app K =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g'
      (dualizingComplex A f)
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).hom ≫
      (dualizingComplexBaseChangeMap A sq) ▷
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) ≫
      (dualizingComplex A f') ◁
        (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
          sq.toCommSq K) ≫
      dualizingComplexTensorMap A f'
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) := by
  exact unit_tensor_base_change
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    (rightDerivedUpperShriek A f)
    (upperStar (ModuleCat.{u + 1} A) f').leftDerivedFunctor
    (rightDerivedUpperShriek A f')
    (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    (rightDerivedUpperShriekTensorMap f)
    (rightDerivedUpperShriekTensorMap f')
    (rightDerivedUpperShriekBaseChangeMap A sq)
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
      g' M N).hom)
    (fun M N ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g M N).hom)
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
      sq.toCommSq N)
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom
    (exceptional_tensor_base_change A sq)
    (Adjunction.projectionTensorMap_naturality_left
      (rightDerivedUpperShriekAdjunction A f')
      (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} A) f').app M).app N)
      (fun φ N ↦ NatTrans.congr_app
      ((projectionMap (ModuleCat.{u + 1} A) f').naturality φ) N))
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} A) g) K

end AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.ProEtale

/-- The unit component of the specified standing mate is beta, with the canonical
pullback-of-unit normalization. Source: main-20261015, final base-change sentence of
lem-pur-co-smooth-composition (blueprint: lem-pur-tensor-mate-base-change). -/
noncomputable def tensorMateBaseChangeUnitNormalization
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) : Prop :=
  letI := c.hasCompactification
  letI := (c.ofIsPullback sq).hasCompactification
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
        (Etale.rightDerivedUpperShriek Λ f').map
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      (Etale.dualizingComplexBaseChangeMap Λ sq)

/-- The tensor-mate square on a retained etale origin K, in omega-first coordinates.
This is the node's coefficient-first equality precomposed with the canonical tensor
symmetry. Pullback/tensor comparison preserves that symmetry, so naturality changes
1 tensor beta into beta tensor 1. Thus no hypothesis or equation is changed; this is
the same convention as the recorded finiteComparedTensorClause. The actual tensor
and pullback-square comparisons are explicit below, and only the fixed beta occurs.
Source: main-20261015, final base-change sentence of lem-pur-co-smooth-composition
(blueprint: lem-pur-tensor-mate-base-change). -/
noncomputable def tensorMateBaseChangeIdentity
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) : Prop :=
  letI := c.hasCompactification
  letI := (c.ofIsPullback sq).hasCompactification
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g').leftDerivedFunctor.map
        (Etale.dualizingComplexTensorMap Λ f K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap Λ sq).app K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g'
          (Etale.dualizingComplex Λ f)
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K)).hom ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X').map
          (Etale.dualizingComplexBaseChangeMap Λ sq)).app _ ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X').obj
          (Etale.dualizingComplex Λ f')).map
          (Etale.derivedSquareUpperStarIsoInvApp
            (ModuleCat.{u + 1} Λ) sq.toCommSq K) ≫
        Etale.dualizingComplexTensorMap Λ f'
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj K))

/-- Arbitrary pullback preserves Dctf and its Tor interval; the standing counit mate
at the coefficient unit is beta; and b composed with pullback of theta equals theta'
composed with 1 tensor beta, under the specified derived comparisons.
Source: main-20261015, lem-pur-co-smooth-composition, final base-change sentence
(blueprint: lem-pur-tensor-mate-base-change).

Proof plan, following the six steps of the node:
1. Take a bounded constructible etale origin (lem-sf-proetale-constructible-origin).
Exact inverse image preserves its cohomological bounds and constructibility
(prop-weil-pbc-inverse-image-modules-exact, prop-constructible-pullback). The etale
stalk Tor test preserves its interval; comparison preserves and reflects that same
interval (lem-sf-etale-stalk-tor-test, lem-sf-comparison-tor-amplitude). The canonical
pullback comparison gives the asserted pro-etale object and interval.
2. The constructible exceptional functors and tensor preserve the required domain.
Use thm-sf-ambient-adjoint-class for injective transpose bijections, with the finite
compactification dimension bound from lem-kun-dimension-finite-type. Inverse exchange
exists by thm-cbc-finite-level-proetale. The definition pur9-cs-def-bc gives the
transpose as inverse exchange followed by the pulled-back counit. At the unit this
is precisely beta, proving the unit normalization by injectivity.
3. Identify the proper factor with ambient ringed exchange using
lem-weil-pbc-transport-identifies-exchange; the proper maps are qcqs. Identify the
open factor termwise by lem-cbc-proetale-extension-zero-comparison. Thus the actual
exchange is the one in lem-pur-co-smooth-pf-exchange-coherence, for arbitrary g.
lem-pur-finite-site-counit-projection-transport identifies its counits and theta.
4. In the omega-first order, projection/exchange coherence says E_X c(Pi) equals
Pi' (E_omega tensor 1). Invert only the projections and exchanges to obtain
c(Pi inverse) E_X inverse = (E_omega inverse tensor 1) Pi' inverse.
5. Transpose b a(theta). Naturality of inverse exchange and the defining theta
transpose give (c epsilon_unit tensor 1) c(Pi inverse) E_X inverse. Step 4 rewrites
this as (c epsilon_unit tensor 1) (E_omega inverse tensor 1) Pi' inverse.
6. Naturality of the primed projection and the defining theta' transpose give
exactly the same expression for theta' (beta tensor 1). Injectivity of transpose
proves equality. Canonical tensor pullback commutes with symmetry on K-flat
representatives. Precompose with canonical symmetry to recover the coefficient-first
order. No theta, b or beta is cancelled and no cohomological smoothness is used. -/
theorem tensorMateBaseChange
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [g'.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (∀ K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)),
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y K →
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y'
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj K) ∧
        ∀ a b : ℤ,
          DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} P.Coefficient) Y a b K →
            DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} P.Coefficient) Y' a b
              ((upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj K)) ∧
    tensorMateBaseChangeUnitNormalization P.Coefficient sq c ∧
    ∀ K : _root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
        ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj K) →
      tensorMateBaseChangeIdentity P.Coefficient sq c K := by
  let := c.hasCompactification
  let := (c.ofIsPullback sq).hasCompactification
  let : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    exact ⟨constructibleFiniteTor_leftDerivedFunctor_upperStar_obj g hK,
      fun a b hTor ↦ torAmplitudeIn_leftDerivedUpperStar _ g a b hTor⟩
  · rfl
  · intro K _hK
    apply congrArg
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map)
    exact Etale.dualizing_tensor_base_change P.Coefficient sq K

end AlgebraicGeometry.ProEtale
