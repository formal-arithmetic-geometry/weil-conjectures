/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

/-! # Induced equivariance on the Tor sheaves of an equivariant immersion

Source: Stacks Project, Cohomology, Tags 08BP and 06YJ, and Groupoids, Tag 03LF.
(blueprint: def-sfb-equivariant-immersion-tor)

Tor on W is H^{-q}(Li^*(M[0])). Flat pullback of cohomology and the recorded,
counit-normalized composition of derived pullbacks give its linearization.
All comparison models retain their counit normalization. They are data used in
specifying a canonical construction, rather than arbitrary isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.EquivariantCoherent

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings X.toRingedSpace))]

/-- The existing tensor pullback with its recorded derived-model categories explicit.
Source: Stacks 0096 (blueprint: def-sfb-equivariant-immersion-tor). -/
abbrev modelPullback {X Z : Scheme.{u}} (f : X ⟶ Z) :
    SheafOfModules.{u} (moduleRings Z.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback f

/-- Exact pullback identified with its derived functor, with the original recorded
counit retained. Source: Stacks 06YJ and 02N4
(blueprint: def-sfb-equivariant-immersion-tor). -/
structure FlatDerivedModel {X Z : Scheme.{u}} (f : X ⟶ Z) where
  additive : (modelPullback f).Additive
  limits : PreservesFiniteLimits (modelPullback f)
  colimits : PreservesFiniteColimits (modelPullback f)
  comparison : letI := additive; letI := limits; letI := colimits
    derivedPullback f ≅ (modelPullback f).mapDerivedCategory.{w, w}
  normalization : letI := additive; letI := limits; letI := colimits
    (isoWhiskerLeft DerivedCategory.Qh comparison).hom ≫
      (modelPullback f).mapDerivedCategoryFactorsh.hom =
        recordedDerivedPullbackCounit f

/-- The uniquely normalized comparison on a module in degree zero.
Source: Stacks 06YJ (blueprint: def-sfb-equivariant-immersion-tor). -/
def flatSingleComparison {X Z : Scheme.{u}} {f : X ⟶ Z} (D : FlatDerivedModel f)
    (M : (SheafOfModules.{u}
      (moduleRings Z.toRingedSpace))) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings Z.toRingedSpace)) 0).obj M) ≅
      (DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) 0).obj
        ((modelPullback f).obj M) :=
  letI := D.additive
  letI := D.limits
  letI := D.colimits
  D.comparison.app _ ≪≫
    ((modelPullback f).mapDerivedCategorySingleFunctor 0).app M

/-- Flat pullback commutes with the cohomology of any derived object, using the
retained counit comparison. Source: Stacks 02N4 and 06YJ
(blueprint: def-sfb-equivariant-immersion-tor). -/
def flatHomologyComparison {X Z : Scheme.{u}} {f : X ⟶ Z} (D : FlatDerivedModel f)
    (n : ℤ) (K : schemeDerivedCategory Z) :
    (modelPullback f).obj ((DerivedCategory.homologyFunctor.{w} (SheafOfModules.{u}
      (moduleRings Z.toRingedSpace)) n).obj K) ≅
      (DerivedCategory.homologyFunctor.{w} (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) n).obj ((derivedPullback f).obj K) :=
  letI := D.additive
  letI := D.limits
  letI := D.colimits
  ((modelPullback f).mapDerivedCategoryHomologyFunctorIso n).app K ≪≫
    (DerivedCategory.homologyFunctor.{w} (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) n).mapIso (D.comparison.symm.app K)

variable {S : Scheme.{u}} {G Y W : Over S} [GrpObj G] [ModObj G Y] [ModObj G W]
  {DY : ActionGroupoidModel G Y} {DW : ActionGroupoidModel G W}
  (i : W ⟶ Y) [IsModHom G i]

/-- The ordinary sheaf Tor on W, as the cohomology of the actual derived pullback.
This is O_W tensor^L_{O_Y} M, not an arbitrary Tor functor.
Source: Stacks 08BP and 06YJ (blueprint: def-sfb-equivariant-immersion-tor). -/
def immersionTor (M : Coherent DY) (q : ℕ) : (SheafOfModules.{u}
      (moduleRings W.left.toRingedSpace)) :=
  (DerivedCategory.homologyFunctor.{w} (SheafOfModules.{u}
      (moduleRings W.left.toRingedSpace)) (-(q : ℤ))).obj
    ((derivedPullback i.left).obj
      ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings Y.left.toRingedSpace)) 0).obj (underlying M)))

/-- Equivariance of derived pullback, with every composition comparison pinned to
its retained counit. Source: Stacks 03LF and 06YJ
(blueprint: def-sfb-equivariant-immersion-tor). -/
def derivedImmersionLinearization (A : FlatDerivedModel (target G Y))
    (P : FlatDerivedModel (source G Y)) (M : Coherent DY)
    (ha : target G W ≫ i.left = (G ◁ i).left ≫ target G Y)
    (hp : source G W ≫ i.left = (G ◁ i).left ≫ source G Y) :
    (derivedPullback (target G W)).obj
        ((derivedPullback i.left).obj
          ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings Y.left.toRingedSpace)) 0).obj (underlying M))) ≅
      (derivedPullback (source G W)).obj
        ((derivedPullback i.left).obj
          ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings Y.left.toRingedSpace)) 0).obj (underlying M))) :=
  (recordedDerivedPullbackComposition (target G W) i.left).app _ ≪≫
    eqToIso (congrArg (fun f => (derivedPullback f).obj
      ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings Y.left.toRingedSpace)) 0).obj (underlying M))) ha) ≪≫
    (recordedDerivedPullbackComposition (G ◁ i).left (target G Y)).symm.app _ ≪≫
    (derivedPullback (G ◁ i).left).mapIso (flatSingleComparison A (underlying M)) ≪≫
    (derivedPullback (G ◁ i).left).mapIso
      ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings (G ⊗ Y).left.toRingedSpace)) 0).mapIso (linearization M)) ≪≫
    (derivedPullback (G ◁ i).left).mapIso (flatSingleComparison P (underlying M)).symm ≪≫
    (recordedDerivedPullbackComposition (G ◁ i).left (source G Y)).app _ ≪≫
    eqToIso (congrArg (fun f => (derivedPullback f).obj
      ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
      (moduleRings Y.left.toRingedSpace)) 0).obj (underlying M))) hp.symm) ≪≫
    (recordedDerivedPullbackComposition (source G W) i.left).symm.app _

/-- The induced Tor linearization, obtained by flat base change along action and
projection and then taking cohomology. Source: Stacks 03LF, 08BP and 06YJ
(blueprint: def-sfb-equivariant-immersion-tor). -/
def immersionTorLinearization (AY : FlatDerivedModel (target G Y))
    (PY : FlatDerivedModel (source G Y)) (AW : FlatDerivedModel (target G W))
    (PW : FlatDerivedModel (source G W)) (M : Coherent DY) (q : ℕ)
    (ha : target G W ≫ i.left = (G ◁ i).left ≫ target G Y)
    (hp : source G W ≫ i.left = (G ◁ i).left ≫ source G Y) :
    (modelPullback (target G W)).obj (immersionTor i M q) ≅
      (modelPullback (source G W)).obj (immersionTor i M q) :=
  flatHomologyComparison AW (-(q : ℤ)) _ ≪≫
    (DerivedCategory.homologyFunctor.{w} (SheafOfModules.{u}
      (moduleRings (G ⊗ W).left.toRingedSpace)) (-(q : ℤ))).mapIso
      (derivedImmersionLinearization i AY PY M ha hp) ≪≫
    (flatHomologyComparison PW (-(q : ℤ)) _).symm

/-- A coherent realization of Tor with exactly the induced linearization. The
underlying isomorphism intertwines the specified Tor comparison on G × W.
Source: Stacks 03LF, 08BP and 06YJ
(blueprint: def-sfb-equivariant-immersion-tor). -/
def IsTor (AY : FlatDerivedModel (target G Y)) (PY : FlatDerivedModel (source G Y))
    (AW : FlatDerivedModel (target G W)) (PW : FlatDerivedModel (source G W))
    (M : Coherent DY) (q : ℕ) (T : Coherent DW) : Prop :=
  ∃ e : underlying T ≅ immersionTor i M q,
    ∀ (ha : target G W ≫ i.left = (G ◁ i).left ≫ target G Y)
      (hp : source G W ≫ i.left = (G ◁ i).left ≫ source G Y),
      (modelPullback (target G W)).map e.hom ≫
          (immersionTorLinearization i AY PY AW PW M q ha hp).hom =
        (linearization T).hom ≫ (modelPullback (source G W)).map e.hom

end AlgebraicGeometry.EquivariantCoherent
