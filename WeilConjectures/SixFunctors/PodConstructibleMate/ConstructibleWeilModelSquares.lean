/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange

/-! # Finite-field models and geometric compactified squares

Source: main-20261015, lem-fix-weil-operations.proof.md, geometric comparison diagrams
(blueprint: def-pod-constructible-weil-model-squares).

The existing six-functor space category is over k. These model diagrams are over k₀;
scalar extension maps them to that existing category and its existing compactified squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PodConstructibleMate

/-- The finite-type model objects, with no separatedness on their structure maps.
This is the source's index of geometric fibers, using Mathlib's full subcategory.
Source: prop-weil-operations.proof.md, geometric models
(blueprint: def-pod-constructible-weil-model-squares). -/
abbrev Models (D : FiniteFieldDatum.{u}) :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of D.k₀)) ↦
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- Actual scalar extension to the geometric fibers, retaining their k-structures.
Source: prop-weil-operations.proof.md, geometric models
(blueprint: def-pod-constructible-weil-model-squares). -/
def fiberModels (D : FiniteFieldDatum.{u}) : Models D ⥤ SixFunctorSpace D :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (fun X ↦ FrobeniusExchange.fiber_finiteType D X.obj)

/-- A compactified square of the finite-type models. Its geometric image below
is the existing SixFunctorCompactifiedSquare; no new geometric comparison is chosen.
Source: def-exchange-projection, model squares used in lem-fix-weil-operations.proof.md
(blueprint: def-pod-constructible-weil-model-squares). -/
structure ModelSquare (D : FiniteFieldDatum.{u}) where
  X : Models D
  Y : Models D
  X' : Models D
  Y' : Models D
  Z : Models D
  Z' : Models D
  f : X ⟶ Y
  f' : X' ⟶ Y'
  g : Y' ⟶ Y
  g' : X' ⟶ X
  i : X ⟶ Z
  i' : X' ⟶ Z'
  p : Z ⟶ Y
  p' : Z' ⟶ Y'
  h : Z' ⟶ Z
  open_i : IsOpenImmersion i.hom.left
  open_i' : IsOpenImmersion i'.hom.left
  proper_p : IsProper p.hom.left
  proper_p' : IsProper p'.hom.left
  factorization : f = i ≫ p
  factorization' : f' = i' ≫ p'
  square : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left
  properSquare : IsPullback h.hom.left p'.hom.left p.hom.left g.hom.left
  openSquare : IsPullback g'.hom.left i'.hom.left i.hom.left h.hom.left
  squareComm : g' ≫ f = f' ≫ g
  properComm : h ≫ p = p' ≫ g
  openComm : g' ≫ i = i' ≫ h

/-- Scalar extension preserves the model's Cartesian squares, including squares
whose schemes have nonseparated structure morphisms.
Source: def-exchange-projection and the base-change convention of the source
(blueprint: def-pod-constructible-weil-model-squares).
Proof: view the Cartesian scheme square as a pullback in the over category; pullback
along Spec k preserves this pullback. The over forgetful functor creates pullbacks,
so its underlying scheme square is Cartesian. No separatedness enters this argument. -/
theorem fiberModels_isPullback
    (D : FiniteFieldDatum.{u}) {X Y X' Y' : Models D}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left) :
    IsPullback (((fiberModels D).map g').hom.left) (((fiberModels D).map f').hom.left)
      (((fiberModels D).map f).hom.left) (((fiberModels D).map g).hom.left) := by
  have sqOver : IsPullback g'.hom f'.hom f.hom g.hom :=
    sq.of_map_of_faithful (Over.forget (Spec (.of D.k₀)))
  exact (sqOver.map (Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).map
      (Over.forget (Spec (.of D.k)))

/-- The same compactified square after scalar extension, with its original chosen
open and proper factors. Source: def-exchange-projection, geometric-fiber convention
(blueprint: def-pod-constructible-weil-model-squares). -/
def ModelSquare.fiber {D : FiniteFieldDatum.{u}} (Q : ModelSquare D) :
    SixFunctorCompactifiedSquare D where
  X := (fiberModels D).obj Q.X
  Y := (fiberModels D).obj Q.Y
  X' := (fiberModels D).obj Q.X'
  Y' := (fiberModels D).obj Q.Y'
  Z := (fiberModels D).obj Q.Z
  Z' := (fiberModels D).obj Q.Z'
  f := (fiberModels D).map Q.f
  f' := (fiberModels D).map Q.f'
  g := (fiberModels D).map Q.g
  g' := (fiberModels D).map Q.g'
  i := (fiberModels D).map Q.i
  i' := (fiberModels D).map Q.i'
  p := (fiberModels D).map Q.p
  p' := (fiberModels D).map Q.p'
  h := (fiberModels D).map Q.h
  open_i := MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ Q.i.hom Q.open_i
  open_i' := MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ Q.i'.hom Q.open_i'
  proper_p := MorphismProperty.overPullbackMap (P := @IsProper) _ Q.p.hom Q.proper_p
  proper_p' := MorphismProperty.overPullbackMap (P := @IsProper) _ Q.p'.hom Q.proper_p'
  factorization := (congrArg (fiberModels D).map Q.factorization).trans
    ((fiberModels D).map_comp Q.i Q.p)
  factorization' := (congrArg (fiberModels D).map Q.factorization').trans
    ((fiberModels D).map_comp Q.i' Q.p')
  square := fiberModels_isPullback D Q.f Q.f' Q.g Q.g' Q.square
  properSquare := fiberModels_isPullback D Q.p Q.p' Q.g Q.h Q.properSquare
  openSquare := fiberModels_isPullback D Q.i Q.i' Q.h Q.g' Q.openSquare
  squareComm := ((fiberModels D).map_comp Q.g' Q.f).symm.trans
    ((congrArg (fiberModels D).map Q.squareComm).trans ((fiberModels D).map_comp Q.f' Q.g))
  properComm := ((fiberModels D).map_comp Q.h Q.p).symm.trans
    ((congrArg (fiberModels D).map Q.properComm).trans ((fiberModels D).map_comp Q.p' Q.g))
  openComm := ((fiberModels D).map_comp Q.g' Q.i).symm.trans
    ((congrArg (fiberModels D).map Q.openComm).trans ((fiberModels D).map_comp Q.i' Q.h))

/-- Transport a composite compactification only across functoriality of scalar extension.
Source: def-exchange-projection, composition convention
(blueprint: def-pod-constructible-weil-model-squares). -/
def fiberCompositionCompactification (D : FiniteFieldDatum.{u})
    {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification (((fiberModels D).map (f ≫ g)).hom.left)) :
    Compactification ((((fiberModels D).map f) ≫ ((fiberModels D).map g)).hom.left) :=
  c.copy (congrArg (fun e ↦ e.hom.left) ((fiberModels D).map_comp f g)).symm

end WeilConjectures.PodConstructibleMate
