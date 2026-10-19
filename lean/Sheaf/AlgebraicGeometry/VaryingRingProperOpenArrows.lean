/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations
public import Sheaf.Paper.ConstantTowerDirectImageNormalization

/-!
# Intrinsic proper/open arrows for varying rings

Source: Stacks Project, Tags 0F7B, 03DI and 09AE, and the explicit lift/projection
construction in the blueprint (blueprint: def-sp-varying-ring-proper-open-arrows).

All intrinsic maps are first constructed on module systems, then localized termwise.
Their derived proper/open comparison is the specified ordinary adjunction mate.

## Main definitions

- `moduleBeta`, `modulePi`: the intrinsic open comparison and clopen projection.
- `moduleAlpha`, `alpha`, `gamma`: the actual system arrow, its localization and mate.
- `constantGamma`: the arbitrary constant-ring comparison from the strict-tower calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The square comparison is uniquely fixed by the explicit compositor formula.
Source: Stacks, Tag 07A7 (blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: the displayed composite is a witness, and its defining equality gives uniqueness. -/
theorem moduleSquareG_existsUnique {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    ∃! e : pull R φ i ⋙ pull R φ r ≅ pull R φ p ⋙ pull R φ k,
      e = (moduleGComp R φ r i).symm ≪≫ eqToIso (congrArg (pull R φ) h.symm) ≪≫
        moduleGComp R φ k p := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

/-- Canonical comparison of the two iterated inverse images around any commutative square.
Source: Stacks, Tag 07A7 (blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    pull R φ i ⋙ pull R φ r ≅ pull R φ p ⋙ pull R φ k :=
  (moduleSquareG_existsUnique R φ k r p i h).choose

/-- The square comparison retains exactly its original compositor formula.
Source: Stacks, Tag 07A7 (blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: this is the defining equality of the uniquely specified comparison. -/
theorem moduleSquareG_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    moduleSquareG R φ k r p i h =
      (moduleGComp R φ r i).symm ≪≫ eqToIso (congrArg (pull R φ) h.symm) ≪≫
        moduleGComp R φ k p :=
  (moduleSquareG_existsUnique R φ k r p i h).choose_spec.1

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose.
Source: Stacks, Tags 09AE and 07A7
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleBetaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Modules R φ U) :
    (extension R φ j').obj ((pull R φ gU).obj M) ⟶ (pull R φ g).obj ((extension R φ j).obj M) :=
  ((moduleJAdj R φ j').homEquiv _ _).symm
    ((pull R φ gU).map ((moduleJAdj R φ j).unit.app M) ≫
      (moduleSquareG R φ gU j' j g h).inv.app ((extension R φ j).obj M))

/-- Naturality of the specified open-unit transpose. Source: Stacks, Tag 09AE
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: use naturality of the open unit, the pullback compositor and the adjunction
Hom equivalence. The transposes of both sides are the same naturality square. -/
theorem moduleBetaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Modules R φ U) (f : M ⟶ N) :
    (pull R φ gU ⋙ extension R φ j').map f ≫ moduleBetaInvApp R φ gU j' j g h N =
      moduleBetaInvApp R φ gU j' j g h M ≫ (extension R φ j ⋙ pull R φ g).map f := by
  unfold moduleBetaInvApp
  apply (moduleJAdj R φ j').homEquiv_naturality_right_square
  have hu := (moduleJAdj R φ j).unit.naturality f
  change f ≫ (moduleJAdj R φ j).unit.app N =
    (moduleJAdj R φ j).unit.app M ≫
      (pull R φ j).map ((extension R φ j).map f) at hu
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  have hn := (moduleSquareG R φ gU j' j g h).inv.naturality ((extension R φ j).map f)
  simp only [Functor.comp_map] at hn ⊢
  rw [hn]

/-- The inverse comparison as a natural transformation with the specified transpose.
Source: Stacks, Tag 09AE (blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleBetaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    pull R φ gU ⋙ extension R φ j' ⟶ extension R φ j ⋙ pull R φ g where
  app := moduleBetaInvApp R φ gU j' j g h
  naturality := moduleBetaInvApp_naturality R φ gU j' j g h

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary rings. Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: restriction commutes with direct image on the same pulled-back test object.
The two routes are left adjoint to these canonically identified right adjoints.
Their unique unit-preserving comparison is invertible and its inverse has exactly
the displayed transpose. The equalities descend from strict complexes. -/
theorem moduleBetaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (moduleBetaInv R φ gU j' j g h) := by
  sorry

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU.
Source: Stacks, Tag 09AE (blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleBeta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : extension R φ j ⋙ pull R φ g ≅ pull R φ gU ⋙ extension R φ j' :=
  (@asIso _ _ _ _ (moduleBetaInv R φ gU j' j g h)
    (moduleBetaInv_isIso R φ gU j' j g h hsq)).symm

/-- The open-extension unit is invertible. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: on an object lying over the open there is exactly one lift to it, so restriction
of the extension presheaf is the original module. This survives sheafification,
termwise extension to strict towers, and exact localization. -/
theorem moduleJAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (moduleJAdj R φ j).unit := by
  sorry

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleOpenToP {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension R φ j ⟶ push R φ j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (extension R φ j) (moduleAdj R φ j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (moduleJAdj R φ j).unit (moduleJAdj_unit_isIso R φ j)) (push R φ j) ≫
          (Functor.leftUnitor _).hom

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: over each pro-etale test object split sections into the product of sections on
the inverse image of the clopen image and on its complement. Both extension and direct
image give the first factor with zero second factor. The specified comparison is the
identity on the first factor. The same formula acts termwise on towers and complexes. -/
theorem moduleOpenToP_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (moduleOpenToP R φ j) := by
  sorry

/-- The intrinsic clopen component projection, with no arbitrary splitting choice.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def modulePi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Modules R φ X) ⟶ pull R φ s ⋙ extension R φ s :=
  (moduleAdj R φ s).unit ≫ Functor.whiskerLeft (pull R φ s)
    (@inv _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s))

/-- Equality transport for open extension, independent of proof-irrelevant instances.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: substitute the equality of scheme maps; proof irrelevance identifies the
open-immersion instances and hence the chosen universal-property functors. -/
theorem moduleJ_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    extension R φ f = extension R φ g := by
  subst g
  rfl

/-- The canonical equality transport for ordinary extension by zero.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-proper-open-arrows). -/
def moduleJCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :=
  eqToIso (moduleJ_congr R φ h)

/-- The normalized non-cartesian open comparison uses moduleBeta and the intrinsic clopen
projection, followed by the open and pullback compositors. Source: Stacks, Tag 0F7B
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : extension R φ i ⋙ pull R φ p ⟶ pull R φ r ⋙ extension R φ k :=
  (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (pull R φ (pullback.snd p i))
    (modulePi R φ (StrictTower.squareLift k r p i h))) (extension R φ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (pull R φ (pullback.snd p i)) (pull R φ (StrictTower.squareLift k r p i h))
      (extension R φ (StrictTower.squareLift k r p i h))).inv (extension R φ (pullback.fst p i)) ≫
  (Functor.associator (pull R φ (pullback.snd p i) ⋙ pull R φ (StrictTower.squareLift k r p i h))
    (extension R φ (StrictTower.squareLift k r p i h)) (extension R φ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (pull R φ (pullback.snd p i) ⋙ pull R φ (StrictTower.squareLift k r p i h))
    ((moduleJComp R φ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (moduleJCongr R φ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((moduleGComp R φ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).hom) (extension R φ k)

/-- The intrinsic derived arrow is the localization of the constructed system map.
Source: Stacks 0F7B; Zheng 4.1
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J R φ i ⋙ G R φ p ⟶ G R φ r ⋙ J R φ k :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules R φ S) (.up ℤ)) _ _
      (extension R φ i ⋙ pull R φ p).mapDerivedCategory
      (pull R φ r ⋙ extension R φ k).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (moduleAlpha R φ k r p i h) (.up ℤ))
          DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso _ _).hom

/-- The normalized proper/open map is exactly the unit-square-counit mate.
Source: Stacks 0F7B, 07A7
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : P R φ r ⋙ J R φ i ⟶ J R φ k ⋙ P R φ p :=
  mateEquiv (adj R φ r) (adj R φ p) (alpha R φ k r p i h)


/-- Embed a single coefficient complex as a constant strict tower.
Source: the constant-ring calculus (blueprint: def-sp-varying-ring-proper-open-arrows). -/
abbrev constantDerived (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    DerivedCategory (StrictTower.Modules B X) ⥤ StrictTower.Derived B X :=
  StrictTower.ConstantNormalization.delta B X

/-- Evaluation of this constant tower is canonically the original derived complex.
Source: Stacks 05RU (blueprint: def-sp-varying-ring-proper-open-arrows). -/
def constantEval (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    constantDerived B X ⋙ StrictTower.ev B X 0 ≅
      𝟭 (DerivedCategory (StrictTower.Modules B X)) :=
  StrictTower.ConstantNormalization.deltaEval B X 0

/-- The single-coefficient source comparison uses the actual tower evaluation maps.
Source: the arbitrary-ring clopen calculus
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def constantSource (B : Type (u + 1)) [CommRing B]
    {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T) [IsOpenImmersion i]
    (M : DerivedCategory (StrictTower.Modules B V)) :
    (StrictTower.ev B T 0).obj ((StrictTower.J B i).obj
      ((StrictTower.R B r).obj ((constantDerived B V).obj M))) ≅
    (StrictTower.moduleJ B i).mapDerivedCategory.obj
      ((StrictTower.moduleDirectImage B r).rightDerivedFunctor.obj M) :=
  (StrictTower.evalJ B i 0).app _ ≪≫
    (StrictTower.moduleJ B i).mapDerivedCategory.mapIso
      ((@asIso _ _ _ _ (StrictTower.evalR B r 0)
          (StrictTower.evalR_isIso B r 0)).app _ ≪≫
        (StrictTower.moduleDirectImage B r).rightDerivedFunctor.mapIso
          ((constantEval B V).app M))

/-- The corresponding single-coefficient target comparison.
Source: the arbitrary-ring clopen calculus
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def constantTarget (B : Type (u + 1)) [CommRing B]
    {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T) [IsOpenImmersion k]
    (M : DerivedCategory (StrictTower.Modules B V)) :
    (StrictTower.ev B T 0).obj ((StrictTower.R B p).obj
      ((StrictTower.J B k).obj ((constantDerived B V).obj M))) ≅
    (StrictTower.moduleDirectImage B p).rightDerivedFunctor.obj
      ((StrictTower.moduleJ B k).mapDerivedCategory.obj M) :=
  (@asIso _ _ _ _ (StrictTower.evalR B p 0) (StrictTower.evalR_isIso B p 0)).app _ ≪≫
    (StrictTower.moduleDirectImage B p).rightDerivedFunctor.mapIso
      ((StrictTower.evalJ B k 0).app _ ≪≫
        (StrictTower.moduleJ B k).mapDerivedCategory.mapIso ((constantEval B V).app M))

/-- The arbitrary constant-ring clopen-projection mate, recovered from the dependency's
strict-tower construction by constant embedding and evaluation. This definition is
valid for infinite rings too and introduces no new single-level comparison choice.
Source: lem-cbc-strict-tower-proper-open-calculus
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def constantGamma (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : DerivedCategory (StrictTower.Modules B V)) :
    (StrictTower.moduleJ B i).mapDerivedCategory.obj
        ((StrictTower.moduleDirectImage B r).rightDerivedFunctor.obj M) ⟶
      (StrictTower.moduleDirectImage B p).rightDerivedFunctor.obj
        ((StrictTower.moduleJ B k).mapDerivedCategory.obj M) :=
  (constantSource B r i M).inv ≫
    (StrictTower.ev B T 0).map
      ((StrictTower.gamma B k r p i h).app ((constantDerived B V).obj M)) ≫
        (constantTarget B k p M).hom

end AlgebraicGeometry.ProEtale.VaryingRing
