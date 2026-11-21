/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement

/-! # Normalization predicates for signed line pullback

## References

* Stacks Project, Tag 03EL
* Stacks Project, Tag 04J0
* Stacks Project, Tag 0GMX
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

/-- Unit, degree one, positive tensor recursion, and negative evaluation normalization. -/
def SignedLinePullbackNormalized
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m) : Prop :=
  (∀ (V : C) (r : R.obj.obj (op V)),
    (P 0).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L 0) V r) = a.hom.app (op V) r) ∧
  (P 1).hom = p.hom ∧
  (∀ (n : ℕ) (V : C) (x : (scalarTensorPower R L (n + 1)).val.obj (op V))
    (y : L.val.obj (op V)),
    (P (.ofNat (n + 2))).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (scalarTensorPower R L (n + 2)) V
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L (op V) x y)) =
      siteSheafTensorTmul (scalarTensorPower R' L' (n + 1)) L' (op (U.obj V))
        ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            (scalarTensorPower R L (n + 1)) V x))
        (p.hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            L V y))) ∧
  (∀ (n : ℕ) (V : C)
    (φ : (signedLinePower.{u, v, w} L (.negSucc n)).val.obj (op V))
    (x : (scalarTensorPower R L (n + 1)).val.obj (op V)),
    (((P (.negSucc n)).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L (.negSucc n)) V φ)).app
          (op (Over.mk (𝟙 (U.obj V)))))
      ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          (scalarTensorPower R L (n + 1)) V x)) =
      a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) x))

/-- The actual scalar/pullback square, tested on its canonical local generators: the pulled
image of `x ⊗ s` is `(pulled x ⊗ 1) ⊗ b(s)`. -/
def SignedLineScalarPullbackSquare
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N') : Prop :=
  ∀ (V : C) (x : L.val.obj (op V)) (s : S.obj.obj (op V)),
    q.hom.val.app (op (U.obj V))
      ((ringedSitePullbackFunctor b (module_pushforward_isRightAdjoint_of_universes b)).map
        c.hom |>.val.app (op (U.obj V))
          (ringedSitePullbackSection b (module_pushforward_isRightAdjoint_of_universes b)
            (changeOfRingsOfUniverses ι L) V (scalarExtensionSection ι L (op V) s x))) =
      c'.hom.val.app (op (U.obj V))
        (scalarExtensionSection ι' L' (op (U.obj V)) (b.hom.app (op V) s)
          (p.hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              L V x)))

end SheafOfModules
