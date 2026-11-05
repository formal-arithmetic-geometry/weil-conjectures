/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.LowerShriekForget
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.WeilSheaf.ProperProjectionFormula
public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionIso

/-! # Natural geometric comparisons for the compact projection formula -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The geometric realization on bounded constructible complexes, used in compact projection
comparisons. -/
def compactProjectionForget (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l X ⥤ BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left) :=
  ObjectProperty.lift _ (forget ⋙ (adicSheafDerivedEquivCondensedMod l _).functor)
    (fun L ↦ (geometricFiberBoundedConstructibleObj L).property)

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The realization as a composite of derived functors agrees with the derived composite. -/
def compactProjectionForgetRealizationIso :
    compactProjectionForget k₀ l X ⋙ (boundedConstructible _).ι ≅
      (objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X :=
  Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
    (Functor.mapDerivedCategoryCompIso
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
      (adicSheafEquivCondensedMod l _).functor).symm

/-- The natural comparison between native tensor and geometric tensor. -/
def compactProjectionForgetTensorIso :
    nativeConstructibleTensor k₀ l X ⋙ compactProjectionForget k₀ l X ≅
      (compactProjectionForget k₀ l X).prod (compactProjectionForget k₀ l X) ⋙ tensor _ := by
  let e := compactProjectionForgetRealizationIso k₀ l X
  let t := Functor.isoWhiskerLeft ((objectProperty k₀ l X).ι.prod (objectProperty k₀ l X).ι)
    (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X)
  apply ((boundedConstructible _).fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft (nativeConstructibleTensor k₀ l X) e ≪≫ t ≪≫
    Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) (Functor.uncurry.obj (curriedTensor _))

variable {X} {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The natural pullback comparison on bounded constructible complexes. -/
def compactProjectionForgetUpperStarIso :
    upperStar f ⋙ compactProjectionForget k₀ l X ≅
      compactProjectionForget k₀ l Y ⋙
        CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f) := by
  apply ((boundedConstructible _).fullyFaithfulι.whiskeringRight _).preimageIso
  exact Functor.isoWhiskerLeft (upperStar f) (compactProjectionForgetRealizationIso k₀ l X) ≪≫
    Functor.isoWhiskerLeft (objectProperty k₀ l Y).ι
      (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l f).symm ≪≫
    Functor.isoWhiskerRight (compactProjectionForgetRealizationIso k₀ l Y).symm _ ≪≫
    Functor.isoWhiskerLeft (compactProjectionForget k₀ l Y)
      (CondensedRing.boundedConstructibleUpperStarCompatibility
        (Profinite.padicAlgClRingObj l) l (geometricFiberHom (k₀ := k₀) f)).symm

end AlgebraicGeometry.WeilComplex
