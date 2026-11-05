/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionForgetIsoTransport

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
  let a := Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
    (adicSheafEquivCondensedMod l _).functor
  let e := projectionTensorForgetIso (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X) a
  refine NatIso.ofComponents (fun MN ↦ ObjectProperty.isoMk _ (e.app (MN.1.obj, MN.2.obj))) ?_
  intro A B φ
  apply ObjectProperty.hom_ext
  have h := e.hom.naturality (Prod.mkHom φ.1.hom φ.2.hom)
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    curriedTensor_map_app, curriedTensor_obj_map, tensorHom_def] using h

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
  let aX := Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
    (adicSheafEquivCondensedMod l _).functor
  let aY := Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
    (adicSheafEquivCondensedMod l _).functor
  let e := projectionPushForgetIso
    (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l f).symm aY aX
  exact NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (e.app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _ (e.hom.naturality φ.hom))

end AlgebraicGeometry.WeilComplex
