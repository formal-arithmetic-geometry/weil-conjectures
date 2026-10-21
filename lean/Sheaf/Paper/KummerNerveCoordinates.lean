/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.TameRootTowerExtension
public import Sheaf.Paper.KummerCechDescent
public import Sheaf.CategoryTheory.CondensedEquivariantBarData

/-! # The canonical coordinates of the punctured Kummer nerve
Source: direct-image proof (3), ratios of successive root lifts.
(blueprint: def-sfb-kummer-nerve-coordinates).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Successive products of the group parameters specify all vertices from the first.
The empty product specifies the first vertex, and n=0 is included.
Source: direct-image proof (3), inhomogeneous Kummer coordinates
(blueprint: def-sfb-kummer-nerve-coordinates). -/
def kummerPrefixParameter (G : Type u) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (n : ℕ) (i : Fin (n + 1)) : C(CategoryTheory.CondensedBar.power G n, G) :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val),
    ⟨fun g ↦ g j, continuous_apply j⟩

/-- The vertex map of the actual parameterized punctured tower.
Source: direct-image proof (3), covering nerve
(blueprint: def-sfb-kummer-nerve-coordinates). -/
def kummerNerveVertex {X B : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction X G)
    (_f : X ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    coefficientParameter X (CategoryTheory.CondensedBar.power G n) ⟶ X :=
  coefficientActionFamily action.act (CategoryTheory.CondensedBar.power G n)
    (kummerPrefixParameter G n i)

/-- All vertices lie over the same base, on the full profinite parameter object.
Source: direct-image proof (3), torsor nerve
(blueprint: def-sfb-kummer-nerve-coordinates).
Proof: each vertex is a parameter pullback of the action. Compose the given
over-quotient identity with that parameter map and use naturality of the parameter
projection. This proves an equality of scheme maps, not pointwise equality. -/
theorem kummerNerveVertex_over {X B : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction X G)
    (f : X ⟶ B)
    (h : action.act ≫ f = coefficientParameterProjection X G ≫ f)
    (n : ℕ) (i : Fin (n + 1)) :
    kummerNerveVertex action f n i ≫ f =
      coefficientParameterProjection X (CategoryTheory.CondensedBar.power G n) ≫ f := by
  sorry

/-- The canonical map from parameterized root lifts to the actual Cech fibre product.
Its vertices, rather than an arbitrary nerve isomorphism, fix the Kummer coordinates.
Source: direct-image proof (3), augmented Kummer nerve
(blueprint: def-sfb-kummer-nerve-coordinates). -/
def kummerNerveCoordinateMap {X B : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction X G)
    (f : X ⟶ B)
    (h : action.act ≫ f = coefficientParameterProjection X G ≫ f) (n : ℕ) :
    coefficientParameter X (CategoryTheory.CondensedBar.power G n) ⟶
      (Arrow.mk f).cechNerve.obj (op (.mk n)) :=
  WidePullback.lift
    (coefficientParameterProjection X (CategoryTheory.CondensedBar.power G n) ≫ f)
    (fun i ↦ kummerNerveVertex action f n i)
    (fun i ↦ kummerNerveVertex_over action f h n i)

/-- The canonical nerve coordinates lie over the actual punctured base.
Source: direct-image proof (3), covering-nerve augmentation
(blueprint: def-sfb-kummer-nerve-coordinates).
Proof: compose the wide-pullback lift with its base projection. The wide-pullback
lift equation gives the displayed projection followed by f exactly. -/
theorem kummerNerveCoordinateMap_over {X B : Scheme.{u}} {G : Profinite.{u}} [CommGroup G]
    [IsTopologicalGroup G] (action : ProfiniteCoefficientAction X G)
    (f : X ⟶ B)
    (h : action.act ≫ f = coefficientParameterProjection X G ≫ f) (n : ℕ) :
    kummerNerveCoordinateMap action f h n ≫
        (CondensedRing.cechProjection f (.mk n)) =
      coefficientParameterProjection X (CategoryTheory.CondensedBar.power G n) ≫ f := by
  sorry

/-- A presentation of the canonical root-coordinate maps with their structural
maps kept explicit. Equality with the actual wide-pullback lift is part of the data,
so this introduces no arbitrary nerve comparison.
Source: direct-image proof (3), actual Kummer nerve
(blueprint: def-sfb-kummer-nerve-coordinates). -/
structure KummerNerveCoordinateData {X B : Scheme.{u}} {G : Profinite.{u}}
    [CommGroup G] [IsTopologicalGroup G] (action : ProfiniteCoefficientAction X G)
    (f : X ⟶ B) (h : action.act ≫ f = coefficientParameterProjection X G ≫ f) where
  map : ∀ n : ℕ, coefficientParameter X (CategoryTheory.CondensedBar.power G n) ⟶
    ((CondensedRing.cechOver f).obj (op (.mk n))).left
  canonical : ∀ n : ℕ, map n = kummerNerveCoordinateMap action f h n
  over : ∀ n : ℕ, map n ≫ ((CondensedRing.cechOver f).obj (op (.mk n))).hom =
    coefficientParameterProjection X (CategoryTheory.CondensedBar.power G n) ≫ f

end AlgebraicGeometry.ProEtale
