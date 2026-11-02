/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarAdjunctions

/-! # Scalar restriction and proper/open coherence

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03D7 and 03DI
(blueprint: lem-sf-semilinear-scalar-proper-open). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- The intrinsic ordinary projector is an actual composite of natural transformations.
Source: Stacks 03DI and 0F7B
(blueprint: lem-sf-semilinear-scalar-proper-open). -/
def scalarOrdinaryPi
    (κ : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
      StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (StrictTower.Towers B X) ⟶
      StrictTower.towerPullback B s ⋙ StrictTower.towerJ B s :=
  (scalarTowerAdj B s).unit ≫
    Functor.whiskerLeft (StrictTower.towerPullback B s) (κ s).inv

/-- The intrinsic proper/open arrows and their compatibility with scalar restriction.
Source: Stacks 03D8, 03DI and 0F7B
(blueprint: lem-sf-semilinear-scalar-proper-open). -/
structure OrdinaryScalarProperOpen (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C) where
  /-- The constant-tower cartesian open comparison, fixed by its transpose below. -/
  beta : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (_h : gU ≫ j = j' ≫ g) (_hsq : IsPullback gU j' j g),
    StrictTower.towerJ B j ⋙ StrictTower.towerPullback B g ≅
      StrictTower.towerPullback B gU ⋙ StrictTower.towerJ B j'
  /-- The inverse beta is exactly the open-unit transpose. -/
  beta_unit : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : StrictTower.Towers B U),
    ((scalarTowerOpenAdj B j').homEquiv _ _)
        ((beta gU j' j g h hsq).inv.app M) =
      (StrictTower.towerPullback B gU).map ((scalarTowerOpenAdj B j).unit.app M) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((StrictTower.towerJ B j).obj M)
  /-- Restriction preserves that canonical beta, before deriving or evaluation. -/
  beta_comparison : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U),
    (C.rho X').map ((moduleBeta R φ gU j' j g h hsq).hom.app M) ≫
        (G.a j').hom.app ((pull R φ gU).obj M) ≫
        (StrictTower.towerJ B j').map ((G.b gU).hom.app M) =
      (G.b g).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B g).map ((G.a j).hom.app M) ≫
        (beta gU j' j g h hsq).hom.app ((C.rho U).obj M)
  /-- The clopen extension/direct comparison, normalized by the inverse open unit. -/
  clopen : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
    StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s
  /-- This equation specifies the canonical open-to-direct map, rather than an arbitrary iso. -/
  clopen_unit : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (N : StrictTower.Towers B U),
    (scalarTowerOpenAdj B s).unit.app N ≫
        ((scalarTowerAdj B s).homEquiv _ _).symm ((clopen s).hom.app N) = 𝟙 N
  /-- Preservation of the actual ordinary clopen projector. -/
  pi_comparison : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (M : Modules R φ X),
    (C.rho X).map ((modulePi R φ s).app M) ≫
        (G.a s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.towerJ B s).map ((G.b s).hom.app M) =
      (scalarOrdinaryPi B clopen s).app ((C.rho X).obj M)
  /-- The constant ordinary alpha, specified by its full clopen word below. -/
  alpha : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
    StrictTower.towerJ B i ⋙ StrictTower.towerPullback B p ⟶
      StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k
  /-- Alpha is beta, then the clopen projector, then the canonical compositors. -/
  alpha_eq : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S),
    (alpha k r p i h).app M =
      (beta (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((scalarOrdinaryPi B clopen (StrictTower.squareLift k r p i h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app M ≫
          (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom.app M)
  /-- Preservation of the intrinsic ordinary alpha for every proper/open square. -/
  alpha_comparison : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Modules R φ S),
    (C.rho W).map ((moduleAlpha R φ k r p i h).app M) ≫
        (G.a k).hom.app ((pull R φ r).obj M) ≫
        (StrictTower.towerJ B k).map ((G.b r).hom.app M) =
      (G.b p).hom.app ((extension R φ i).obj M) ≫
        (StrictTower.towerPullback B p).map ((G.a i).hom.app M) ≫
        (alpha k r p i h).app ((C.rho S).obj M)

/-- The normalized adjunction comparisons preserve beta, the clopen projector and alpha.
Source: Stacks 03D8, 03DI and 0F7B; blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-proper-open).
Proof: choose the constant-tower cartesian beta as the inverse open-unit transpose.
The inverse-image compositor comparison follows by taking the mates of the
sectionwise direct-image compositor. The open compositor comparison follows from
uniqueness of the unit-preserving left-adjoint comparison. Transposing the two sides
of beta compatibility, substituting these compositor and open-unit equations,
gives identical morphisms; the adjunction bijection proves their equality.
For a clopen map, the open unit is invertible and its inverse transpose is the
extension/direct-image comparison. Take its inverse and compose with the
direct-image unit to define pi. The already established unit and mate comparisons
prove pi compatibility. Define alpha by the specified beta, pi and compositor
word. Substitute beta and pi compatibility and the two compositor equations into
this word. Naturality moves each coefficient comparison through the factors, and
the neighboring inverse comparisons cancel. The resulting equation is alpha
compatibility. None of these arguments assumes that the proper/open square is
cartesian or that a coefficient map is flat. -/
theorem ordinaryScalarProperOpen (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n)
    (C : OrdinaryScalarRestriction R φ B ψ) (G : OrdinaryScalarAdjunctions R φ B ψ C) :
    Nonempty (OrdinaryScalarProperOpen R φ B ψ C G) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
