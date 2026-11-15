/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Relative higher-direct-image exchange for field extensions

## References

* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Relative exchange for a sheaf annihilated by an integer invertible in the base field.
This compares higher direct images, without an injectivity or acyclicity hypothesis
(Stacks, Tag 0F1C). -/
theorem nonempty_fieldExtension_higherDirectImage_iso
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : n • 𝟙 F = 0)
    (q : ℕ) :
    Nonempty
      ((upperStar AddCommGrpCat.{u + 1}
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
          (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F) ≅
        ((lowerStar AddCommGrpCat.{u + 1}
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).rightDerived q).obj
          ((upperStar AddCommGrpCat.{u + 1}
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj F)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst f g
  let f' := pullback.snd f g
  let U := upperStar AddCommGrpCat.{u + 1} g
  let D := (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
    ((DerivedCategory.singleFunctor _ 0).obj F)
  obtain ⟨e⟩ := nonempty_fieldExtension_derivedDirectImage_single_iso (K := K) f n hn F hF
  exact ⟨U.mapIso
      ((lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorObjSingleFunctorIso
        F q).symm ≪≫
    (U.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).app D ≪≫
    (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso e ≪≫
    (lowerStar AddCommGrpCat.{u + 1} f').homologyRightDerivedFunctorObjSingleFunctorIso
      ((upperStar AddCommGrpCat.{u + 1} p).obj F) q⟩

end AlgebraicGeometry.Etale
