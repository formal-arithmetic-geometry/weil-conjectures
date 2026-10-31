/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
import WeilConjectures.AlgebraicGeometry.SbcExchangeIdentity
public import WeilConjectures.AlgebraicGeometry.SbcExchangeDiscrete
import WeilConjectures.AlgebraicGeometry.SbcExchangeSiteComparison
import WeilConjectures.AlgebraicGeometry.SbcExchangeScalarComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison
public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # Compatibility of pro-etale exchange maps

Source: literature/blueprint/latest/blueprint/sec-smooth-base-change/
sk-lem-sbc-exchange-compatibility/_section.md, order 2152, and its proof;
Stacks Project, Tags 07A7, 0E46 and 0E47
(blueprint: sk-lem-sbc-exchange-compatibility).

The existing `RootCoordinateFace.exchange` is the counit mate for the exact
condensed inverse image. The auxiliary `sbcDiscreteExchangePlus` is that same
mate on bounded-below discrete-module sheaves. The main theorem has three
blocks: the four formal laws for every condensed ring, discrete site comparison,
and compatibility with the scalar-six maps in the finite-Tor full subcategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- Naturality, identity, both pasting laws, site comparison and scalar comparison
for the specified exchange maps.
Source: latest blueprint sk-lem-sbc-exchange-compatibility, order 2152,
equations (1)--(2) and all three proof paragraphs
(blueprint: sk-lem-sbc-exchange-compatibility).

Proof: Apply det-sbc-exchange-formal to the exact condensed pullbacks and their
specified right adjoints. Naturality is that of the mate; the identity follows
from the triangle identities. Horizontal and vertical mate pasting give the two
compositor formulas, without inverting exchange. For the site clause, transpose
both routes under the pro-etale f' adjunction. Substitute the defining counit
transpose of exchange and the counit equations for b_f and b_f' from
lem-pe-direct-image-mate-compatibility. Coherence of c_g and c_u from
sk-thm-pe-direct-image-comparison makes the transposes equal; that theorem
makes the b maps isomorphisms for qcqs f,f'. For the scalar clause, use the
canonical scalarSixPullHom and its direct-image mate scalarDirectImageMate in
the scalar/geometric mate rectangle. This is lem-sfb-scalar-geometric-exchange-rectangle
with the pullback comparison in the forward direction. Apply sk-prop-scalar-six
for invertibility, and sk-thm-sf-ctf-stability and scalar preservation to put
the two endpoints in Dctf. The subcategories are full, so the ambient equality
is the asserted equality in Dctf. Finite coefficient maps need not be flat. -/
theorem sbcExchangeCompatibility :
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        [MonObj Λ] [IsCommMonObj Λ],
      (∀ {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
          {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare u f' f g)
          {K L : DerivedCategory (RootCoordinateFace.Modules Λ X)} (v : K ⟶ L),
        (RootCoordinateFace.upper Λ g).map ((RootCoordinateFace.lower Λ f).map v) ≫
            (RootCoordinateFace.exchange Λ u f' f g sq.w).app L =
          (RootCoordinateFace.exchange Λ u f' f g sq.w).app K ≫
            (RootCoordinateFace.lower Λ f').map ((RootCoordinateFace.upper Λ u).map v)) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
          (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
          (K : DerivedCategory (RootCoordinateFace.Modules Λ X)),
        (RootCoordinateFace.exchange Λ (𝟙 X) f f (𝟙 Y) sq.w).app K =
          (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ Y) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app ((RootCoordinateFace.lower Λ f).obj K) ≫
          (RootCoordinateFace.lower Λ f).map
            ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
              Functor.mapDerivedCategoryIdIso _).inv.app K)) ∧
      (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {u : X' ⟶ X} {u' : X'' ⟶ X'}
          {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
          {g : Y' ⟶ Y} {h : Y'' ⟶ Y'}
          (sq₁ : ChosenCartesianSquare u f' f g)
          (sq₂ : ChosenCartesianSquare u' f'' f' h)
          (outer : ChosenCartesianSquare (u' ≫ u) f'' f (h ≫ g))
          (K : DerivedCategory (RootCoordinateFace.Modules Λ X)),
        (RootCoordinateFace.exchange Λ (u' ≫ u) f'' f (h ≫ g) outer.w).app K =
          (RootCoordinateFace.upperComp Λ h g).hom.app
            ((RootCoordinateFace.lower Λ f).obj K) ≫
          (RootCoordinateFace.upper Λ h).map
            ((RootCoordinateFace.exchange Λ u f' f g sq₁.w).app K) ≫
          (RootCoordinateFace.exchange Λ u' f'' f' h sq₂.w).app
            ((RootCoordinateFace.upper Λ u).obj K) ≫
          (RootCoordinateFace.lower Λ f'').map
            ((RootCoordinateFace.upperComp Λ u' u).inv.app K)) ∧
      (∀ {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
          {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
          (sq₁ : ChosenCartesianSquare u f' f v)
          (sq₂ : ChosenCartesianSquare v e' e g)
          (outer : ChosenCartesianSquare u (f' ≫ e') (f ≫ e) g)
          (K : DerivedCategory (RootCoordinateFace.Modules Λ X)),
        (RootCoordinateFace.exchange Λ u (f' ≫ e') (f ≫ e) g outer.w).app K =
          (RootCoordinateFace.upper Λ g).map
              ((RootCoordinateFace.lowerComp Λ f e).hom.app K) ≫
          (RootCoordinateFace.exchange Λ v e' e g sq₂.w).app
            ((RootCoordinateFace.lower Λ f).obj K) ≫
          (RootCoordinateFace.lower Λ e').map
            ((RootCoordinateFace.exchange Λ u f' f v sq₁.w).app K) ≫
          (RootCoordinateFace.lowerComp Λ f' e').inv.app
            ((RootCoordinateFace.upper Λ u).obj K))) ∧
    (∀ (A : Type u) [CommRing A]
        {X' X Y' Y : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
        {f : X ⟶ Y} {g : Y' ⟶ Y}
        [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
        (sq : ChosenCartesianSquare u f' f g)
        (K : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))),
      (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y').mapDerivedCategoryPlus.map
          ((Etale.derivedBaseChangeMapPlus
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app K) ≫
        (comparisonDirectImageCanonicalMate (ULift.{u + 1, u} A) f').app
          ((Etale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) u).mapDerivedCategoryPlus.obj K) =
      (directImageComparisonPullbackPlusIso (ULift.{u + 1, u} A) g).inv.app
          ((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctorPlus.obj K) ≫
        (ProEtale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategoryPlus.map
          ((comparisonDirectImageCanonicalMate (ULift.{u + 1, u} A) f).app K) ≫
        (sbcDiscreteExchangePlus A sq).app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategoryPlus.obj K) ≫
        (ProEtale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').rightDerivedFunctorPlus.map
          ((directImageComparisonPullbackPlusIso (ULift.{u + 1, u} A) u).hom.app K)) ∧
    (∀ (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
        [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
        (hcd : BaseFieldFiniteCD ell k) {Λ Λ' : ScalarSixRing.{u}}
        (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
        {X' X Y' Y : Over (Spec (.of k))}
        [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
        [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
        (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
        (sq : ChosenCartesianSquare u.left f'.left f.left g.left)
        (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      (constantModelBoundedConstructible Λ'.X Y'.left ⊓ DerivedCategory.finiteTorAmplitude _)
        ((scalarSixChange a Y'.left).obj
          ((scalarSixPull Λ g.left).obj ((RootCoordinateFace.lower Λ.X f.left).obj K.obj))) ∧
      (constantModelBoundedConstructible Λ'.X Y'.left ⊓ DerivedCategory.finiteTorAmplitude _)
        ((RootCoordinateFace.lower Λ'.X f'.left).obj
          ((scalarSixPull Λ' u.left).obj ((scalarSixChange a X.left).obj K.obj))) ∧
      IsIso ((scalarSixPullHom a g.left).app
        ((RootCoordinateFace.lower Λ.X f.left).obj K.obj)) ∧
      IsIso ((scalarDirectImageMate a f.left).app K.obj) ∧
      IsIso ((scalarDirectImageMate a f'.left).app ((scalarSixPull Λ u.left).obj K.obj)) ∧
      IsIso ((scalarSixPullHom a u.left).app K.obj) ∧
      (scalarSixPullHom a g.left).app ((RootCoordinateFace.lower Λ.X f.left).obj K.obj) ≫
          (scalarSixPull Λ' g.left).map ((scalarDirectImageMate a f.left).app K.obj) ≫
          (RootCoordinateFace.exchange Λ'.X u.left f'.left f.left g.left sq.w).app
            ((scalarSixChange a X.left).obj K.obj) =
        (scalarSixChange a Y'.left).map
            ((RootCoordinateFace.exchange Λ.X u.left f'.left f.left g.left sq.w).app K.obj) ≫
          (scalarDirectImageMate a f'.left).app ((scalarSixPull Λ u.left).obj K.obj) ≫
          (RootCoordinateFace.lower Λ'.X f'.left).map
            ((scalarSixPullHom a u.left).app K.obj)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Λ
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro X' X Y' Y u f' f g sq K L v
      exact RootCoordinateFace.exchange_naturality Λ u f' f g sq.w v
    · intro X Y f sq K
      exact sbcExchangeIdentity Λ f sq K
    · intro X'' X' X Y'' Y' Y u u' f f' f'' g h sq₁ sq₂ outer K
      exact RootCoordinateFace.exchange_vertical_pasting Λ u f' f g u' f'' h sq₁.w sq₂.w outer.w K
    · intro X' X Y' Y Z' Z u f' f v e' e g sq₁ sq₂ outer K
      exact RootCoordinateFace.exchange_horizontal_pasting Λ u f' f v e' e g sq₁.w sq₂.w outer.w K
  · intro A _ X' X Y' Y u f' f g _ _ _ _ sq K
    exact sbcExchangeSiteComparison A sq K
  · intro ell _ k _ _ _ _hcd Λ Λ' a _ha X' X Y' Y
      _ _ _ _ _ _ _ _ _ _ _ _ u f' f g sq K
    exact sbcExchangeScalarComparison (ell := ell) (k := k) (hcd := _hcd)
      (a := a) (ha := _ha) u f' f g sq K

end AlgebraicGeometry.Scheme
