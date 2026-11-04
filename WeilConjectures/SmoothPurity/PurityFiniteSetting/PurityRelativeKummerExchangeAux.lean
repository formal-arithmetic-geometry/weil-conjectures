/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerAssembly
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BaseChangeShiftAux

/-! # Auxiliary exchange statements for the relative Kummer computation

Source: blueprint latest, relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).

The canonical coefficient pullbacks are isomorphisms once the exponent is invertible on
the target. Consequently, the derived exchange map of any commutative square is invertible
on a coefficient object as soon as both relative units are.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical pullback on constants is an isomorphism.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
instance isIso_constantPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : IsIso (P.constantPullback f) := by
  unfold constantPullback
  infer_instance

/-- The canonical pullback on the finite twist is an isomorphism when the exponent is
invertible on the target.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
theorem isIso_twistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) : IsIso (P.twistPullback h f) := by
  have := P.isIso_twistEtalePullback h f hr
  unfold twistPullback
  infer_instance

/-- The derived coefficient pullback is an isomorphism when the exponent is invertible on
the target. Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
theorem isIso_derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) :
    IsIso (P.derivedCoefficientPullback h f twisted) := by
  have := P.isIso_twistPullback h f hr
  unfold derivedCoefficientPullback
  cases twisted <;> infer_instance

/-- If the relative unit of `f` on a coefficient object is invertible, so is the
derived adjunction unit at the degree-zero coefficient object of the base.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions). -/
theorem isIso_unit_of_isIso_relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool)
    (hr : IsUnit (P.exponent : Γ(Y, ⊤))) (hu : IsIso (P.relativeUnit h f twisted)) :
    IsIso ((ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted)) := by
  have := P.isIso_derivedCoefficientPullback h f twisted hr
  unfold relativeUnit at hu
  exact IsIso.of_isIso_comp_right _
    ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
      (P.derivedCoefficientPullback h f twisted))

/-- The unit-exchange identity: after the derived pullback of the unit of `f`, the
exchange map on the pulled-back coefficient object is the unit of `f'` followed by the
square comparison. This is `unit_mateEquiv` for the derived exchange mate.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions). -/
theorem derivedBaseChangeMap_unit (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (ProEtale.upperStar A g).leftDerivedFunctor.map
        ((ProEtale.derivedUpperStarLowerStarAdjunction A f).unit.app K) ≫
      (ProEtale.derivedBaseChangeMap A sq).app
        ((ProEtale.upperStar A f).leftDerivedFunctor.obj K) =
      (ProEtale.derivedUpperStarLowerStarAdjunction A f').unit.app
          ((ProEtale.upperStar A g).leftDerivedFunctor.obj K) ≫
        (ProEtale.lowerStar A f').rightDerivedFunctor.map
          ((ProEtale.leftDerivedUpperStarSquareIso A sq).hom.app K) :=
  unit_mateEquiv _ _ _ K

/-- The exchange map transforms the derived pullback of an adjoint morphism into the adjoint
of the pulled-back morphism, precomposed with the square comparison.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: naturality of the exchange map and the unit-exchange identity. -/
theorem derivedBaseChangeMap_homEquiv (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) {M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (φ : (ProEtale.upperStar A f).leftDerivedFunctor.obj M ⟶ L) :
    (ProEtale.upperStar A g).leftDerivedFunctor.map
        ((ProEtale.derivedUpperStarLowerStarAdjunction A f).homEquiv _ _ φ) ≫
      (ProEtale.derivedBaseChangeMap A sq).app L =
      (ProEtale.derivedUpperStarLowerStarAdjunction A f').homEquiv _ _
        ((ProEtale.leftDerivedUpperStarSquareIso A sq).hom.app M ≫
          (ProEtale.upperStar A g').leftDerivedFunctor.map φ) := by
  have e := (ProEtale.derivedBaseChangeMap A sq).naturality φ
  simp only [Functor.comp_map] at e
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, e,
    reassoc_of% (derivedBaseChangeMap_unit A sq M), Functor.map_comp]

/-- The derived exchange map of a commutative square is invertible on a degree-zero
coefficient object as soon as both relative units are invertible. No cartesianness of the
square is needed. Source: blueprint relative Kummer proof, Step 3, affine square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: the coefficient pullback of `f` and naturality reduce to the pulled-back coefficient
object; there the unit-exchange identity and the coefficient pullback of `g` identify the
map with units of `f` and `f'`, which are invertible. -/
theorem isIso_derivedBaseChangeMap_app_of_isIso_relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (twisted : Bool)
    (hY : IsUnit (P.exponent : Γ(Y, ⊤))) (hY' : IsUnit (P.exponent : Γ(Y', ⊤)))
    (hu : IsIso (P.relativeUnit h f twisted)) (hu' : IsIso (P.relativeUnit h f' twisted)) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient) sq).app
      (P.derivedSheaf h X twisted)) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let adj' := ProEtale.derivedUpperStarLowerStarAdjunction A f'
  let c := P.derivedCoefficientPullback h f twisted
  let d := P.derivedCoefficientPullback h g twisted
  have hc : IsIso c := P.isIso_derivedCoefficientPullback h f twisted hY
  have hd : IsIso d := P.isIso_derivedCoefficientPullback h g twisted hY
  have h₁ := P.isIso_unit_of_isIso_relativeUnit h f twisted hY hu
  have h₂ := P.isIso_unit_of_isIso_relativeUnit h f' twisted hY' hu'
  have h₃ : IsIso (adj'.unit.app
      ((ProEtale.upperStar A g).leftDerivedFunctor.obj (P.derivedSheaf h Y twisted))) := by
    have e := adj'.unit.naturality d
    have : IsIso (adj'.unit.app _ ≫
        (_ ⋙ (ProEtale.lowerStar A f').rightDerivedFunctor).map d) := by
      rw [← e]
      dsimp only [Functor.id_map]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((_ ⋙ (ProEtale.lowerStar A f').rightDerivedFunctor).map d)
  have h₄ : IsIso ((ProEtale.derivedBaseChangeMap A sq).app
      ((ProEtale.upperStar A f).leftDerivedFunctor.obj (P.derivedSheaf h Y twisted))) := by
    have e := derivedBaseChangeMap_unit A sq (P.derivedSheaf h Y twisted)
    have : IsIso ((ProEtale.upperStar A g).leftDerivedFunctor.map
        ((ProEtale.derivedUpperStarLowerStarAdjunction A f).unit.app
          (P.derivedSheaf h Y twisted)) ≫ (ProEtale.derivedBaseChangeMap A sq).app
        ((ProEtale.upperStar A f).leftDerivedFunctor.obj (P.derivedSheaf h Y twisted))) := by
      rw [e]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ProEtale.upperStar A g).leftDerivedFunctor.map
        ((ProEtale.derivedUpperStarLowerStarAdjunction A f).unit.app
          (P.derivedSheaf h Y twisted))) _
  have e := (ProEtale.derivedBaseChangeMap A sq).naturality c
  have : IsIso (((ProEtale.lowerStar A f).rightDerivedFunctor ⋙
      (ProEtale.upperStar A g).leftDerivedFunctor).map c ≫
      (ProEtale.derivedBaseChangeMap A sq).app (P.derivedSheaf h X twisted)) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_left (((ProEtale.lowerStar A f).rightDerivedFunctor ⋙
      (ProEtale.upperStar A g).leftDerivedFunctor).map c) _

/-- The exchange-unit identity on coefficient objects: after pulling back the relative
unit of `f`, the exchange map followed by the coefficient pullback of `g'` is the coefficient
pullback of `g`, then the relative unit of `f'`, then the direct image of an automorphism
of the coefficient object on `X'`.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: naturality of the exchange map, `unit_mateEquiv`, and naturality of the unit of
`f'` along the coefficient pullback of `g`. -/
theorem exists_relativeUnit_derivedBaseChangeMap (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) (twisted : Bool) (hX : IsUnit (P.exponent : Γ(X, ⊤)))
    (hY : IsUnit (P.exponent : Γ(Y, ⊤))) (hY' : IsUnit (P.exponent : Γ(Y', ⊤))) :
    ∃ θ : P.derivedSheaf h X' twisted ⟶ P.derivedSheaf h X' twisted, IsIso θ ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
          (P.relativeUnit h f twisted) ≫
        (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient) sq).app
          (P.derivedSheaf h X twisted) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f').rightDerivedFunctor.map
          (P.derivedCoefficientPullback h g' twisted) =
      P.derivedCoefficientPullback h g twisted ≫ P.relativeUnit h f' twisted ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f').rightDerivedFunctor.map
          θ := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let adj' := ProEtale.derivedUpperStarLowerStarAdjunction A f'
  let c := P.derivedCoefficientPullback h f twisted
  let c' := P.derivedCoefficientPullback h f' twisted
  let d := P.derivedCoefficientPullback h g twisted
  let cg := P.derivedCoefficientPullback h g' twisted
  have hc : IsIso c := P.isIso_derivedCoefficientPullback h f twisted hY
  have hc' : IsIso c' := P.isIso_derivedCoefficientPullback h f' twisted hY'
  have hd : IsIso d := P.isIso_derivedCoefficientPullback h g twisted hY
  have hcg : IsIso cg := P.isIso_derivedCoefficientPullback h g' twisted hX
  refine ⟨inv c' ≫ (ProEtale.upperStar A f').leftDerivedFunctor.map (inv d) ≫
    (ProEtale.leftDerivedUpperStarSquareIso A sq).hom.app (P.derivedSheaf h Y twisted) ≫
    (ProEtale.upperStar A g').leftDerivedFunctor.map c ≫ cg, inferInstance, ?_⟩
  have e₁ := (ProEtale.derivedBaseChangeMap A sq).naturality c
  have e₂ := derivedBaseChangeMap_unit A sq (P.derivedSheaf h Y twisted)
  have e₃ := adj'.unit.naturality d
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at e₁ e₃
  unfold relativeUnit
  simp only [Functor.map_comp, Category.assoc, Functor.map_inv]
  rw [reassoc_of% e₁, reassoc_of% e₂]
  erw [reassoc_of% e₃]
  simp
  rfl

/-- Derived pullback preserves invertibility of a map on a homology sheaf.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions). -/
theorem isIso_homology_leftDerivedUpperStar_map (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (φ : K ⟶ L) (n : ℤ) (hφ : IsIso ((DerivedCategory.homologyFunctor _ n).map φ)) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((ProEtale.upperStar A g).leftDerivedFunctor.map φ)) := by
  have : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ ProEtale.upperStar A g).map φ) := by
    dsimp only [Functor.comp_map]
    infer_instance
  rw [NatIso.isIso_map_iff (ProEtale.leftDerivedUpperStarHomologyFunctorIso A g n)] at this
  exact this

/-- Derived pullback preserves vanishing of a homology sheaf.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions). -/
theorem isZero_homology_leftDerivedUpperStar_obj (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (n : ℤ) (hK : IsZero ((DerivedCategory.homologyFunctor _ n).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((ProEtale.upperStar A g).leftDerivedFunctor.obj K)) :=
  ((ProEtale.upperStar A g).map_isZero hK).of_iso
    ((ProEtale.leftDerivedUpperStarHomologyFunctorIso A g n).app K).symm

/-- Reduction of the punctured exchange to degree one: under the relative conclusions over
both bases, the exchange map on the twisted punctured coefficient object is invertible as
soon as it is invertible on the first homology sheaf.
Source: blueprint relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: in degree zero use the exchange-unit identity and the degree-zero unit
isomorphisms; in degrees other than zero and one both homology sheaves vanish. -/
theorem isIso_puncturedBaseChange_of_isIso_homology_one (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B' B : Scheme.{u}} (g : B' ⟶ B)
    (a : B ⟶ Spec (CommRingCat.of P.field.k))
    (hB : P.RelativeKummerConclusions h B a)
    (hB' : P.RelativeKummerConclusions h B' (g ≫ a))
    (h1 : IsIso ((DerivedCategory.homologyFunctor _ 1).map
      ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
        (puncturedSquare g)).app (P.derivedSheaf h (Punctured B) true)))) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
      (puncturedSquare g)).app (P.derivedSheaf h (Punctured B) true)) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let BC := (ProEtale.derivedBaseChangeMap A (puncturedSquare g)).app
    (P.derivedSheaf h (Punctured B) true)
  have hX := P.exponent_isUnit (Punctured B) (puncturedProjection B ≫ a)
  have hY := P.exponent_isUnit B a
  have hY' := P.exponent_isUnit B' (g ≫ a)
  have hcp := P.isIso_derivedCoefficientPullback h (puncturedMap g) true hX
  rw [DerivedCategory.isIso_iff]
  intro n
  by_cases hn1 : n = 1
  · subst hn1
    exact h1
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨θ, hθ, e⟩ := P.exists_relativeUnit_derivedBaseChangeMap h (puncturedSquare g) true
      hX hY hY'
    have hd := P.isIso_derivedCoefficientPullback h g true hY
    have hu := isIso_homology_leftDerivedUpperStar_map A g _ 0 hB.2.2.2.1
    have hu' := hB'.2.2.2.1
    have e' := congrArg (DerivedCategory.homologyFunctor _ 0).map e
    simp only [Functor.map_comp] at e'
    have : IsIso ((DerivedCategory.homologyFunctor _ 0).map
        ((ProEtale.upperStar A g).leftDerivedFunctor.map
          (P.relativeUnit h (puncturedProjection B) true)) ≫
        (DerivedCategory.homologyFunctor _ 0).map BC ≫
        (DerivedCategory.homologyFunctor _ 0).map
          ((ProEtale.lowerStar A (puncturedProjection B')).rightDerivedFunctor.map
            (P.derivedCoefficientPullback h (puncturedMap g) true))) := by
      erw [e']
      infer_instance
    have := IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor _ 0).map
        ((ProEtale.upperStar A g).leftDerivedFunctor.map
          (P.relativeUnit h (puncturedProjection B) true)))
      ((DerivedCategory.homologyFunctor _ 0).map BC ≫
        (DerivedCategory.homologyFunctor _ 0).map
          ((ProEtale.lowerStar A (puncturedProjection B')).rightDerivedFunctor.map
            (P.derivedCoefficientPullback h (puncturedMap g) true)))
    exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor _ 0).map
          ((ProEtale.lowerStar A (puncturedProjection B')).rightDerivedFunctor.map
            (P.derivedCoefficientPullback h (puncturedMap g) true)))
  · have hs := isZero_homology_leftDerivedUpperStar_obj A g n
      (P.isZero_puncturedImage_of_relative_conclusions h B a hB n hn0 hn1)
    have ht := (P.isZero_puncturedImage_of_relative_conclusions h B' (g ≫ a) hB' n hn0
      hn1).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
        ((ProEtale.lowerStar A (puncturedProjection B')).rightDerivedFunctor.mapIso
          (asIso (P.derivedCoefficientPullback h (puncturedMap g) true))))
    exact ⟨⟨0, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

/-- The affine-line exchange is invertible under the relative conclusions over both bases.
Source: blueprint relative Kummer proof, Step 3, affine square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: both twisted relative units of the line projections are invertible. -/
theorem isIso_lineBaseChange_of_relative_conclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B' B : Scheme.{u}} (g : B' ⟶ B)
    (a : B ⟶ Spec (CommRingCat.of P.field.k))
    (hB : P.RelativeKummerConclusions h B a)
    (hB' : P.RelativeKummerConclusions h B' (g ≫ a)) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
        (P.derivedSheaf h (Line B) true)) :=
  P.isIso_derivedBaseChangeMap_app_of_isIso_relativeUnit h _ true (P.exponent_isUnit B a)
    (P.exponent_isUnit B' (g ≫ a)) hB.2.1 hB'.2.1

/-- The shifted exchange map on a degree-one class: for a square `u ≫ π = π' ≫ g`, a class
`κ : CP ⟶ K[1]` over the source whose pullback along `u` is the class `κ'` over the target (up to
coefficient maps), the derived pullback of the adjoint of `κ` followed by the shifted exchange
map is the adjoint of `κ'`, up to the coefficient maps.
Source: blueprint relative Kummer proof, Step 3, punctured square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: the exchange map commutes with the shifts; then apply the exchange-adjoint identity,
naturality of the shift isomorphism of `Rπ'_*`, the Kummer naturality and the coefficient
identity. -/
theorem derivedBaseChangeMap_shift_adjoint (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {π' : X' ⟶ Y'} {π : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq u' π' π g) {C : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    {C' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A)}
    {CP K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {CP' K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A)}
    (cpπ : (ProEtale.upperStar A π).leftDerivedFunctor.obj C ⟶ CP)
    (cpπ' : (ProEtale.upperStar A π').leftDerivedFunctor.obj C' ⟶ CP')
    (cpu : (ProEtale.upperStar A u').leftDerivedFunctor.obj CP ⟶ CP')
    (cpK : (ProEtale.upperStar A u').leftDerivedFunctor.obj K ⟶ K')
    (cpg : (ProEtale.upperStar A g).leftDerivedFunctor.obj C ⟶ C')
    (κ : CP ⟶ K⟦(1 : ℤ)⟧) (κ' : CP' ⟶ K'⟦(1 : ℤ)⟧)
    (hκ : (ProEtale.upperStar A u').leftDerivedFunctor.map κ ≫
      ((ProEtale.upperStar A u').leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K ≫
        cpK⟦(1 : ℤ)⟧' = cpu ≫ κ')
    (hρ : (ProEtale.leftDerivedUpperStarSquareIso A sq).hom.app C ≫
      (ProEtale.upperStar A u').leftDerivedFunctor.map cpπ ≫ cpu =
        (ProEtale.upperStar A π').leftDerivedFunctor.map cpg ≫ cpπ') :
    (ProEtale.upperStar A g).leftDerivedFunctor.map
        ((ProEtale.derivedUpperStarLowerStarAdjunction A π).homEquiv _ _ (cpπ ≫ κ) ≫
          ((ProEtale.lowerStar A π).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K) ≫
      ((ProEtale.upperStar A g).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        ((ProEtale.lowerStar A π).rightDerivedFunctor.obj K) ≫
      ((ProEtale.derivedBaseChangeMap A sq).app K)⟦(1 : ℤ)⟧' ≫
      ((ProEtale.lowerStar A π').rightDerivedFunctor.map cpK)⟦(1 : ℤ)⟧' =
    cpg ≫ (ProEtale.derivedUpperStarLowerStarAdjunction A π').homEquiv _ _ (cpπ' ≫ κ') ≫
      ((ProEtale.lowerStar A π').rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K' := by
  have hs := NatTrans.shift_app_comm (ProEtale.derivedBaseChangeMap A sq) (1 : ℤ) K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hs
  have hm := derivedBaseChangeMap_homEquiv A sq (cpπ ≫ κ)
  have hn := ((ProEtale.lowerStar A π').rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.naturality
    cpK
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  have hr {M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A)}
      {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A)}
      (φ : (ProEtale.upperStar A π').leftDerivedFunctor.obj M ⟶ L) (ψ : L ⟶ L') {Z : _}
      (k : (ProEtale.lowerStar A π').rightDerivedFunctor.obj L' ⟶ Z) :
      (ProEtale.derivedUpperStarLowerStarAdjunction A π').homEquiv _ _ φ ≫
        (ProEtale.lowerStar A π').rightDerivedFunctor.map ψ ≫ k =
      (ProEtale.derivedUpperStarLowerStarAdjunction A π').homEquiv _ _ (φ ≫ ψ) ≫ k := by
    rw [Adjunction.homEquiv_naturality_right, Category.assoc]
  rw [Functor.map_comp, Category.assoc, reassoc_of% hs, reassoc_of% hm, ← hn,
    ← Functor.map_comp_assoc, hr]
  simp only [Category.assoc, Functor.map_comp]
  rw [hκ, reassoc_of% hρ, Adjunction.homEquiv_naturality_left, Category.assoc]

/-- Invertibility of the shifted exchange after a functor `H`, from invertibility of the two
adjoint classes after `H` and of the coefficient maps.
Source: blueprint relative Kummer proof, Step 3, punctured square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: apply `H` to `derivedBaseChangeMap_shift_adjoint` and cancel the invertible factors. -/
theorem isIso_map_derivedBaseChangeMap_shift (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {π' : X' ⟶ Y'} {π : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq u' π' π g) {C : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    {C' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A)}
    {CP K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {CP' K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A)}
    (cpπ : (ProEtale.upperStar A π).leftDerivedFunctor.obj C ⟶ CP)
    (cpπ' : (ProEtale.upperStar A π').leftDerivedFunctor.obj C' ⟶ CP')
    (cpu : (ProEtale.upperStar A u').leftDerivedFunctor.obj CP ⟶ CP')
    (cpK : (ProEtale.upperStar A u').leftDerivedFunctor.obj K ⟶ K')
    (cpg : (ProEtale.upperStar A g).leftDerivedFunctor.obj C ⟶ C')
    (κ : CP ⟶ K⟦(1 : ℤ)⟧) (κ' : CP' ⟶ K'⟦(1 : ℤ)⟧)
    (hκ : (ProEtale.upperStar A u').leftDerivedFunctor.map κ ≫
      ((ProEtale.upperStar A u').leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K ≫
        cpK⟦(1 : ℤ)⟧' = cpu ≫ κ')
    (hρ : (ProEtale.leftDerivedUpperStarSquareIso A sq).hom.app C ≫
      (ProEtale.upperStar A u').leftDerivedFunctor.map cpπ ≫ cpu =
        (ProEtale.upperStar A π').leftDerivedFunctor.map cpg ≫ cpπ')
    [IsIso cpg] [IsIso cpK] {D : Type*} [Category D]
    (H : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A) ⥤ D)
    (h₁ : IsIso (H.map ((ProEtale.upperStar A g).leftDerivedFunctor.map
      ((ProEtale.derivedUpperStarLowerStarAdjunction A π).homEquiv _ _ (cpπ ≫ κ) ≫
        ((ProEtale.lowerStar A π).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K))))
    (h₂ : IsIso (H.map ((ProEtale.derivedUpperStarLowerStarAdjunction A π').homEquiv _ _
      (cpπ' ≫ κ') ≫
        ((ProEtale.lowerStar A π').rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K'))) :
    IsIso (H.map (((ProEtale.derivedBaseChangeMap A sq).app K)⟦(1 : ℤ)⟧')) := by
  have e := congrArg H.map
    (derivedBaseChangeMap_shift_adjoint A sq cpπ cpπ' cpu cpK cpg κ κ' hκ hρ)
  rw [Functor.map_comp H ((ProEtale.upperStar A g).leftDerivedFunctor.map _),
    Functor.map_comp H (((ProEtale.upperStar A g).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
      _), Functor.map_comp H (((ProEtale.derivedBaseChangeMap A sq).app K)⟦(1 : ℤ)⟧'),
    Functor.map_comp H cpg] at e
  have : IsIso (H.map ((ProEtale.upperStar A g).leftDerivedFunctor.map
      ((ProEtale.derivedUpperStarLowerStarAdjunction A π).homEquiv _ _ (cpπ ≫ κ) ≫
        ((ProEtale.lowerStar A π).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app K)) ≫
      H.map (((ProEtale.upperStar A g).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        ((ProEtale.lowerStar A π).rightDerivedFunctor.obj K)) ≫
      H.map (((ProEtale.derivedBaseChangeMap A sq).app K)⟦(1 : ℤ)⟧') ≫
      H.map (((ProEtale.lowerStar A π').rightDerivedFunctor.map cpK)⟦(1 : ℤ)⟧')) := by
    rw [e]
    infer_instance
  rwa [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at this

/-- The edge morphism of a Kummer generator is invertible in degree zero.
Source: blueprint sk-prop-a1-kummer, clause (2) (blueprint: prop-pur-gm-relative-kummer). -/
theorem isIso_homology_zero_kummerAdjoint (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) (hY : IsIso (P.kummerGenerator h Y a)) :
    IsIso ((DerivedCategory.homologyFunctor _ 0).map
      ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).homEquiv _ _
          (P.derivedCoefficientPullback h (puncturedProjection Y) false ≫
            (P.coordinateKummer h Y a).hom) ≫
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
            (P.derivedSheaf h (Punctured Y) true))) := by
  unfold kummerGenerator at hY
  rwa [isIso_comp_left_iff, isIso_comp_right_iff] at hY

end WeilConjectures.PurityFiniteSetting
