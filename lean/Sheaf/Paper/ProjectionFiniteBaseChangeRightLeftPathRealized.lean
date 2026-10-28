/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups D7, B2
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation
import Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality
import all Sheaf.Paper.FiniteProjectionIterationRealization
import Sheaf.Paper.FiniteProjectionDiamondRightCoordinates
import all Sheaf.Paper.ProjectionFiniteBaseChangeLeftPrefix

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

open CompactSupportFiniteProjection

attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor

private theorem inverse_comparison
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x : B} {a b : A} (p : x ≅ R.functor.obj b) (c : a ≅ b) :
    (R.inverse.mapIso (p ≪≫ R.functor.mapIso c.symm) ≪≫
      (R.unitIso.app a).symm).hom =
      R.inverse.map p.hom ≫ R.unitIso.inv.app b ≫ c.inv := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  exact congrArg (fun t ↦ R.inverse.map p.hom ≫ t)
    (R.unitIso.inv.naturality c.inv)

private theorem inverse_transport
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x y : B} {a b c : A} (p : x ≅ R.functor.obj a)
    (s : y ≅ R.functor.obj b) (d : b ≅ c) (e : x ⟶ y) (f : a ⟶ c)
    (h : e ≫ (s ≪≫ R.functor.mapIso d).hom = p.hom ≫ R.functor.map f) :
    R.inverse.map e ≫ (R.inverse.mapIso s ≪≫ (R.unitIso.app b).symm).hom ≫ d.hom =
      (R.inverse.mapIso p ≪≫ (R.unitIso.app a).symm).hom ≫ f := by
  have h' := congrArg (fun t ↦ R.inverse.map t ≫ R.unitIso.inv.app c) h
  simp -implicitDefEqProofs only [Functor.map_comp, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] at h'
  rw [inverse_unit_naturality R d.hom, inverse_unit_naturality R f] at h'
  simpa -implicitDefEqProofs only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc] using h'

private theorem exchange_transport_self
    {A B C E H : Type*} [Category A] [Category B] [Category C]
    [Category E] [Category H]
    (R : E ⥤ H) (U V : C ⥤ E) (F : A ⥤ C) (G : B ⥤ E) (W : A ⥤ B)
    (c : U ≅ V) (ex : F ⋙ U ⟶ W ⋙ G)
    {x : C} {y : B} {z z' : H} {k : A}
    (p : z ≅ R.obj (V.obj x)) (s : z' ≅ R.obj (G.obj y))
    (b : x ≅ F.obj k) (v : y ≅ W.obj k) :
    (p.hom ≫ R.map (V.map b.hom) ≫ R.map (c.inv.app _) ≫
        R.map (ex.app k) ≫ R.map (G.map v.inv) ≫ s.inv) ≫
      (s ≪≫ R.mapIso (G.mapIso v)).hom =
    (p ≪≫ R.mapIso (c.symm.app x)).hom ≫ R.map (U.map b.hom ≫ ex.app k) := by
  simpa using exchange_transport R U V F G W c ex p s b v (Iso.refl k)

private def mu_transformation {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj
        (fixedDerivedPull (C := C) (E := E) (n := n) f)).obj
      (fixedTensor (C := C) (E := E) (n := n) Y) ≅
    (((Functor.whiskeringLeft₂ _).obj
        (fixedDerivedPull (C := C) (E := E) (n := n) f)).obj
      (fixedDerivedPull (C := C) (E := E) (n := n) f)).obj
        (fixedTensor (C := C) (E := E) (n := n) X) :=
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  leftDerivedUpperStarTensorNatIso
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left

private def mu_coordinates {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    (fixedDerivedPull (C := C) (E := E) (n := n) f).obj
        (((fixedTensor (C := C) (E := E) (n := n) Y).obj K).obj L) ≅
      ((fixedTensor (C := C) (E := E) (n := n) X).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj K)).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj L) :=
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  ((mu_transformation (hn := hn) f).app K).app L

private theorem mu_coordinates_hom {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (mu_coordinates (hn := hn) f K L).hom =
      (leftDerivedUpperStarTensorIso
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        f.hom.left K L).hom := by
  rfl

attribute [local irreducible] mu_transformation

private theorem mu_coordinates_naturality {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {K K' : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))}
    (s : K ⟶ K')
    (L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    let U := fixedDerivedPull (C := C) (E := E) (n := n) f
    let TY := fixedTensor (C := C) (E := E) (n := n) Y
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    U.map ((TY.map s).app L) ≫ (mu_coordinates (hn := hn) f K' L).hom =
      (mu_coordinates (hn := hn) f K L).hom ≫ (TX.map (U.map s)).app (U.obj L) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact congr_app ((mu_transformation (hn := hn) f).hom.naturality s) L

private def exchange_coordinates (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X) :
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    (fixedDerivedPull (C := C) (E := E) (n := n) Q.g).obj
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
          Q.compactification).obj (RX.inverse.obj K.obj)) ⟶
      (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
        (Q.compactification.ofIsPullback Q.square)).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj
          (RX.inverse.obj K.obj)) :=
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  FiniteProjectionExchange.ex
    (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) Q.square
    Q.compactification
    ((realization (C := C) (E := E) (n := n) (hn := hn) Q.X).inverse.obj K.obj)

-- Compare the canonical maps by their coordinates rather than their derived constructions.
attribute [local irreducible] leftDerivedUpperStarTensorIso projectionMapOfCompactification
  rightDerivedLowerShriekOfCompactificationBaseChangeMap

private theorem diamond_right_coordinates
    (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let TB := fixedTensor (C := C) (E := E) (n := n) Q.Y'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
    let a := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      Q.compactification
    let k := RX.inverse.obj K.obj
    let l := RY.inverse.obj L.obj
    FiniteProjectionExchange.diamondRight
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) Q.square
        Q.compactification k l =
      (mu_coordinates (hn := hn) Q.g (F.obj k) l).hom ≫
        (TB.map (exchange_coordinates Q K)).app (U.obj l) ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) Q.f'
          (Q.compactification.ofIsPullback Q.square) (a.obj k) (U.obj l) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  dsimp only
  rw [finiteProjectionDiamondRight_fixed_coordinates (hn := hn), mu_coordinates_hom]
  rfl

private def exchange_transformation (Q : SixFunctorCompactifiedSquare D) :
    sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
        Q.compactification ⋙ fixedDerivedPull (C := C) (E := E) (n := n) Q.g ⟶
      fixedDerivedPull (C := C) (E := E) (n := n) Q.g' ⋙
        sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
          (Q.compactification.ofIsPullback Q.square) :=
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    Q.square Q.compactification

private theorem exchange_conjugation
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let V := sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) Q.g.hom.left
    let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let c := fixedPullComparison (C := C) (E := E) (n := n) Q.g
    let p := pullRealization S.toSixFunctorFiniteOperations Q.g
      ((S.finite.support Q.f Q.compactification).obj K)
    let s := supportRealization S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
    let b := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification K
    let v := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K
    (sixFunctorProjectionFiniteExchange S Q K).hom =
      p.hom ≫ R.functor.map (V.map b.hom) ≫ R.functor.map (c.inv.app _) ≫
        R.functor.map ((exchange_transformation (hn := hn) Q).app (RX.inverse.obj K.obj)) ≫
        R.functor.map (G.map v.inv) ≫ s.inv := by
  rfl

private def square_source_coordinates
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
    let TY := fixedTensor (C := C) (E := E) (n := n) Q.Y
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      Q.compactification
    let k := RX.inverse.obj K.obj
    let l := RY.inverse.obj L.obj
    ((S.finite.pull Q.g).obj
      (((partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
        ((S.finite.support Q.f Q.compactification).obj K)).obj L)).obj ≅
      R.functor.obj (U.obj (((TY.obj (F.obj k)).obj l))) :=
  sixFunctorProjectionFiniteSquareSource S Q K L

private def square_target_coordinates
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
    let V := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let W := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X'
    let F' := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let k := RX.inverse.obj K.obj
    let l := RY.inverse.obj L.obj
    ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).obj
      (((partialTensor S.toSixFunctorFiniteOperations Q.X').obj
        ((S.finite.pull Q.g').obj K)).obj
        ((torPull S.toSixFunctorFiniteOperations Q.f').obj
          ((torPull S.toSixFunctorFiniteOperations Q.g).obj L)))).obj ≅
      R.functor.obj (F'.obj (((TX.obj (V.obj k)).obj (W.obj (U.obj l))))) :=
  sixFunctorProjectionFiniteSquareTarget S Q K L

private def right_coordinate_statement
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) : Prop :=
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
    let V := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let TB := fixedTensor (C := C) (E := E) (n := n) Q.Y'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      Q.compactification
    let k := RX.inverse.obj K.obj
    let l := RY.inverse.obj L.obj
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫
      (square_target_coordinates S Q K L).hom =
    (square_source_coordinates S Q K L).hom ≫ R.functor.map
      ((mu_coordinates (hn := hn) Q.g (F.obj k) l).hom ≫
        (TB.map (exchange_coordinates Q K)).app (U.obj l) ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) Q.f'
          (Q.compactification.ofIsPullback Q.square) (V.obj k) (U.obj l))

private theorem right_from_coordinates
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left)
    (h : right_coordinate_statement S Q K L) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let source := sixFunctorProjectionFiniteSquareSource S Q K L
    let target := sixFunctorProjectionFiniteSquareTarget S Q K L
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫ target.hom =
      source.hom ≫ R'.functor.map
        (FiniteProjectionExchange.diamondRight A Q.square Q.compactification
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  exact h.trans (congrArg (fun q ↦
    (sixFunctorProjectionFiniteSquareSource S Q K L).hom ≫ R.functor.map q)
    (diamond_right_coordinates Q K L).symm)

attribute [local irreducible] realization fixedComponent

private theorem exchange_inverse
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    R.inverse.map (sixFunctorProjectionFiniteExchange S Q K).hom ≫
      (fixedSupportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)).hom ≫
      F.map (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K).hom =
    (fixedPullRealization S.toSixFunctorFiniteOperations Q.g
      ((S.finite.support Q.f Q.compactification).obj K)).hom ≫
      U.map (fixedSupportRealization S.toSixFunctorFiniteOperations Q.f
        Q.compactification K).hom ≫
      exchange_coordinates Q K := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
  let V := sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) Q.g.hom.left
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  let c := fixedPullComparison (C := C) (E := E) (n := n) Q.g
  let p := pullRealization S.toSixFunctorFiniteOperations Q.g
    ((S.finite.support Q.f Q.compactification).obj K)
  let s := supportRealization S.toSixFunctorFiniteOperations Q.f'
    (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
  let b := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification K
  let v := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K
  let ex := exchange_transformation (C := C) (E := E) (n := n) (hn := hn) Q
  have h := exchange_transport_self R.functor U V _ G _ c ex p s b v
  have h' := inverse_transport R (p ≪≫ R.functor.mapIso (c.symm.app _)) s
    (G.mapIso v) _ _ h
  have hc := inverse_comparison R p (c.app _)
  rw [exchange_conjugation]
  have hf := h'.trans (congrArg (fun t ↦ t ≫ U.map b.hom ≫ ex.app _) hc)
  dsimp only [R, U, V, G, c, p, s, b, v, ex] at hf
  simpa -implicitDefEqProofs only [fixedSupportRealization, fixedPullRealization,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc, exchange_coordinates, exchange_transformation] using hf



private theorem projection_pasting
    {A : Type*} [Category A] {a b c d e f : A}
    {p : a ⟶ b} {x : b ⟶ c} {y : a ⟶ d} {q : d ⟶ c}
    {r : b ⟶ e} {z : e ⟶ f} {t : c ⟶ f}
    (h₁ : p ≫ x = y ≫ q) (h₂ : r ≫ z = x ≫ t) :
    y ≫ (q ≫ t) = p ≫ r ≫ z := by
  rw [← Category.assoc, ← h₁, Category.assoc, ← h₂]

private theorem projection_transport
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X'
    let TY := fixedTensor (C := C) (E := E) (n := n) Q.Y'
    let k := RX.inverse.obj ((S.finite.pull Q.g').obj K).obj
    let l := R.inverse.obj ((torPull S.toSixFunctorFiniteOperations Q.g).obj L).obj
    let a := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K
    let b := fixedPullRealization S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩
    fixedComponent (C := C) (E := E) (n := n) (hn := hn) Q.f'
        (Q.compactification.ofIsPullback Q.square) k l ≫
      F.map (((TX.mapIso a).app (U.obj l) ≪≫ (TX.obj _).mapIso (U.mapIso b)).hom) =
    (TY.map (F.map a.hom)).app l ≫
    (TY.obj (F.obj ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj
      ((realization (C := C) (E := E) (n := n) (hn := hn) Q.X).inverse.obj K.obj)))).map b.hom ≫
      fixedComponent (C := C) (E := E) (n := n) (hn := hn) Q.f'
        (Q.compactification.ofIsPullback Q.square)
        ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) Q.X).inverse.obj K.obj))
        ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g).obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) Q.Y).inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let TX := fixedTensor (C := C) (E := E) (n := n) Q.X'
  let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  let a := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K
  let b := fixedPullRealization S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩
  let l := RY.inverse.obj ((torPull S.toSixFunctorFiniteOperations Q.g).obj L).obj
  let k' := (fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj
    ((realization (C := C) (E := E) (n := n) (hn := hn) Q.X).inverse.obj K.obj)
  have h₁ := fixed_projection_first_coordinates
    (C := C) (E := E) (n := n) (hn := hn) Q.f'
    (Q.compactification.ofIsPullback Q.square) a.hom l
  have h₂ := fixed_projection_second_coordinates
    (C := C) (E := E) (n := n) (hn := hn) Q.f'
    (Q.compactification.ofIsPullback Q.square) k' b.hom
  exact (congrArg (fun z ↦ fixedComponent
      (C := C) (E := E) (n := n) (hn := hn) Q.f'
      (Q.compactification.ofIsPullback Q.square)
      (RX.inverse.obj ((S.finite.pull Q.g').obj K).obj) l ≫ z)
    (F.map_comp ((TX.map a.hom).app (U.obj l))
      ((TX.obj k').map (U.map b.hom)))).trans (projection_pasting h₁ h₂)

private theorem tensor_cancel
    {A B C : Type*} [Category A] [Category B] [Category C] (T : A ⥤ B ⥤ C)
    {x x' z z' : A} {y y' : B} (a : x ≅ x') (b : y ≅ y')
    (f : x ⟶ z) (g : z ≅ z') :
    (T.map a.inv).app y' ≫ (T.obj x).map b.inv ≫ (T.map f).app y ≫
      (T.map g.hom).app y ≫ (T.obj z').map b.hom =
      (T.map (a.inv ≫ f ≫ g.hom)).app y' := by
  rw [reassoc_of% (T.map f).naturality b.inv,
    reassoc_of% (T.map g.hom).naturality b.inv]
  rw [← (T.obj z').map_comp b.inv b.hom, b.inv_hom_id,
    (T.obj z').map_id, Category.comp_id]
  simp -implicitDefEqProofs only [Functor.map_comp, NatTrans.comp_app]

private theorem tensor_projection_pasting
    {A B : Type*} [Category A] [Category B]
    (U : A ⥤ B) (TA : A ⥤ A ⥤ A) (TB : B ⥤ B ⥤ B)
    {h h' l : A} {x y y' k k' : B} {z z' : B}
    (a : x ≅ U.obj h) (b : y ≅ U.obj l) (s : h ≅ h')
    (c : y' ≅ k) (d : k ≅ k') (e : x ⟶ y') (ex : U.obj h' ⟶ k')
    (mu : U.obj ((TA.obj h).obj l) ⟶ (TB.obj (U.obj h)).obj (U.obj l))
    (mu' : U.obj ((TA.obj h').obj l) ⟶ (TB.obj (U.obj h')).obj (U.obj l))
    (pf : (TB.obj k).obj y ⟶ z) (pf' : (TB.obj k').obj (U.obj l) ⟶ z')
    (t : z ⟶ z')
    (he : a.inv ≫ e ≫ c.hom ≫ d.hom = U.map s.hom ≫ ex)
    (hp : pf ≫ t = (TB.map d.hom).app y ≫ (TB.obj k').map b.hom ≫ pf')
    (hm : U.map ((TA.map s.hom).app l) ≫ mu' =
      mu ≫ (TB.map (U.map s.hom)).app (U.obj l)) :
    mu ≫ (TB.map a.inv).app (U.obj l) ≫ (TB.obj x).map b.inv ≫
      (TB.map e).app y ≫ (TB.map c.hom).app y ≫ pf ≫ t =
    U.map ((TA.map s.hom).app l) ≫ mu' ≫ (TB.map ex).app (U.obj l) ≫ pf' := by
  rw [hp]
  have ht := tensor_cancel TB a b e (c ≪≫ d)
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.map_comp,
    NatTrans.comp_app, Category.assoc] at ht
  have he' := congrArg (fun f ↦ (TB.map f).app (U.obj l)) he
  simp -implicitDefEqProofs only [Functor.map_comp, NatTrans.comp_app] at he'
  rw [reassoc_of% ht, reassoc_of% he', ← reassoc_of% hm]

private theorem right_map_assembly
    {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    (R₀ : A ≌ A') (R : B ≌ B') (U : A ⥤ B) (T : B ⥤ B ⥤ B)
    {h₀ h₁ : A} {m m' l k k' z z' v : B} {src tgt x y n : B'}
    (p : src ≅ R.functor.obj v)
    (c₀ : v ≅ U.obj (R₀.inverse.obj (R₀.functor.obj h₀)))
    (mu : U.obj h₀ ≅ (T.obj m).obj l)
    (mu' : U.obj h₁ ≅ (T.obj m').obj l)
    (a : R.inverse.obj x ≅ m) (b : R.inverse.obj n ≅ l)
    (c : R.inverse.obj y ≅ k) (e : x ⟶ y) (ex : m' ⟶ k')
    (pf : (T.obj k).obj (R.inverse.obj n) ⟶ z)
    (pf' : (T.obj k').obj l ⟶ z') (t : z ≅ z')
    (target : tgt ≅ R.functor.obj z) (w : h₀ ≅ h₁)
    (ht : mu.hom ≫ (T.map a.inv).app l ≫
      (T.obj (R.inverse.obj x)).map b.inv ≫
      (T.map (R.inverse.map e)).app (R.inverse.obj n) ≫
      (T.map c.hom).app (R.inverse.obj n) ≫ pf ≫ t.hom =
      U.map w.hom ≫ mu'.hom ≫ (T.map ex).app l ≫ pf') :
    (p ≪≫ R.functor.mapIso (c₀ ≪≫
        U.mapIso (R₀.unitIso.app h₀).symm ≪≫ mu ≪≫
        (T.mapIso a.symm).app l ≪≫
        (T.obj (R.inverse.obj x)).mapIso b.symm)).hom ≫
      R.functor.map ((T.map (R.inverse.map e)).app (R.inverse.obj n)) ≫
      R.functor.map ((T.obj (R.inverse.obj y)).map (R.inverse.map (𝟙 n))) ≫
      ((R.functor.mapIso ((T.mapIso c).app (R.inverse.obj n))).hom ≫
        R.functor.map pf ≫ target.inv) ≫
      (target ≪≫ R.functor.mapIso t).hom =
    (p ≪≫ R.functor.mapIso (c₀ ≪≫ U.mapIso
      (R₀.inverse.mapIso (R₀.functor.mapIso w) ≪≫
        (R₀.unitIso.app h₁).symm))).hom ≫
      R.functor.map (mu'.hom ≫ (T.map ex).app l ≫ pf') := by
  have ht' := congrArg (fun z ↦ p.hom ≫ R.functor.map c₀.hom ≫
    R.functor.map (U.map (R₀.unitIso.inv.app h₀)) ≫ R.functor.map z) ht
  simp only [Functor.map_comp] at ht'
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_assoc]
  have hw := congrArg (fun q ↦ R.functor.map (U.map q))
    (R₀.unitIso.inv.naturality w.hom)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hw
  rw [reassoc_of% hw]
  exact ht'

private theorem inverse_cancel_left
    {A : Type*} [Category A] {x y z : A} (a : x ≅ y)
    (p : x ⟶ z) (q : y ⟶ z) (h : p = a.hom ≫ q) : a.inv ≫ p = q := by
  rw [h, a.inv_hom_id_assoc]

attribute [local implicit_reducible] partialTensor torPull
  CompactSupportFiniteProjection.tensor fixedTensor fixedDerivedPull

private theorem partial_tensor_map_coordinates
    (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    {K K' : sixFunctorFiniteCategory D C E n hn X} (a : K ⟶ K')
    (L : finiteTorConstructibleCategory C.l E n hn X.obj.left) :
    let R := realization (C := C) (E := E) (n := n) (hn := hn) X
    let T := fixedTensor (C := C) (E := E) (n := n) X
    (((partialTensor S.toSixFunctorFiniteOperations X).map a).app L).hom =
      R.functor.map ((T.map (R.inverse.map a.hom)).app (R.inverse.obj L.obj)) ≫
        R.functor.map ((T.obj (R.inverse.obj K'.obj)).map
          (R.inverse.map (𝟙 L.obj))) := by
  rfl

private theorem right_realization
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let source := sixFunctorProjectionFiniteSquareSource S Q K L
    let target := sixFunctorProjectionFiniteSquareTarget S Q K L
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫ target.hom =
      source.hom ≫ R'.functor.map
        (FiniteProjectionExchange.diamondRight A Q.square Q.compactification
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
  let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  let TY := fixedTensor (C := C) (E := E) (n := n) Q.Y
  let TB := fixedTensor (C := C) (E := E) (n := n) Q.Y'
  let h := RY.inverse.obj ((S.finite.support Q.f Q.compactification).obj K).obj
  let l := RY.inverse.obj L.obj
  let a := fixedPullRealization S.toSixFunctorFiniteOperations Q.g
    ((S.finite.support Q.f Q.compactification).obj K)
  let b := fixedPullRealization S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩
  let s := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification K
  let c := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f'
    (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
  let d := F.mapIso (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K)
  let e := R.inverse.map (sixFunctorProjectionFiniteExchange S Q K).hom
  let ex := exchange_coordinates Q K
  let mu := mu_coordinates (hn := hn) Q.g h l
  let mu' := mu_coordinates (hn := hn) Q.g
    ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      Q.compactification).obj (RX.inverse.obj K.obj)) l
  have he := inverse_cancel_left a _ _ (exchange_inverse S Q K)
  have hp := projection_transport S Q K L
  have hm := mu_coordinates_naturality (hn := hn) Q.g s.hom l
  have ht := tensor_projection_pasting U TY TB a b s c d e ex mu.hom mu'.hom
    _ _ _ he hp hm
  let M := ((partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
    ((S.finite.support Q.f Q.compactification).obj K)).obj L
  let p := pullRealization S.toSixFunctorFiniteOperations Q.g M
  let cp := fixedPullComparison (C := C) (E := E) (n := n) Q.g
  let TX := fixedTensor (C := C) (E := E) (n := n) Q.X'
  let U' := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
  let ak := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K
  let lp := R.inverse.obj ((torPull S.toSixFunctorFiniteOperations Q.g).obj L).obj
  let tf := F.mapIso ((TX.mapIso ak).app (U'.obj lp) ≪≫
    (TX.obj ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj
      (RX.inverse.obj K.obj))).mapIso (U'.mapIso b))
  let target := targetComparison S.toSixFunctorFiniteOperations Q.f'
    (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj K)
    ((torPull S.toSixFunctorFiniteOperations Q.g).obj L)
  have hr := right_map_assembly RY R U TB
    (h₀ := ((TY.obj h).obj l))
    (h₁ := ((TY.obj ((sfFixedCompactSupport
      (Padic.coefficientExtensionRing C.l E n) Q.compactification).obj
        (RX.inverse.obj K.obj))).obj l)) p (cp.symm.app _) mu mu' a b c
    (sixFunctorProjectionFiniteExchange S Q K).hom ex _ _ tf target
    ((TY.mapIso s).app l) ht
  dsimp only [R, RY, RX, U, F, TY, TB, h, l, a, b, s, c, d, e, ex, mu, mu',
    M, p, cp, TX, U', ak, lp, tf, target] at hr
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, CategoryTheory.Functor.map_comp,
    Category.assoc] at hr
  have hc : right_coordinate_statement S Q K L := by
    dsimp only [right_coordinate_statement]
    unfold square_source_coordinates square_target_coordinates
      sixFunctorProjectionFiniteRightPath sixFunctorProjectionFiniteSquareTarget
      sixFunctorProjectionFiniteSquareSource sixFunctorProjectionFiniteMu
      component projectionFullConjugate sourceComparison projectionTensorLeftRealization
      sixFunctorProjectionFiniteTensorRealization
    simp -implicitDefEqProofs only [ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.comp_hom]
    conv_lhs =>
      arg 1
      arg 2
      arg 1
      rw [partial_tensor_map_coordinates S Q.Y'
        (sixFunctorProjectionFiniteExchange S Q K)
        ((torPull S.toSixFunctorFiniteOperations Q.g).obj L)]
    dsimp only [ObjectProperty.isoMk, ObjectProperty.homMk]
    dsimp only [fixedDerivedPull, ObjectProperty.ι, inducedFunctor,
      Ideal.Quotient.instRingQuotient, Ideal.Quotient.commRing] at hr ⊢
    simp -implicitDefEqProofs only [mu_coordinates_hom, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
      CategoryTheory.Functor.map_comp, Category.assoc] at hr ⊢
    convert hr using 1
    rfl
  exact right_from_coordinates S Q K L hc

/-- Realized equality of the right and left finite projection routes.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, route normalization.
(blueprint: lem-sf-finite-base-change-right-left-path-realized).

Proof: independently realize the right route using tensor and projection naturality
and cancellation of the coefficient unit. The existing left-route calculation
realizes the left route. The fixed-scalar diamond equality identifies the two
resulting composites after the common source and target comparisons.
-/
theorem sixFunctorProjectionFinite_right_left_path_realized
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let target := sixFunctorProjectionFiniteSquareTarget S Q K L
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫ target.hom =
      I.map (sixFunctorProjectionFiniteLeftPath S Q K L) ≫ target.hom := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  dsimp only
  rw [right_realization S Q K L,
    sixFunctorProjectionFinite_left_route_calculation S Q K L,
    sixFunctorProjectionFinite_diamond_equality S Q K L]
  rfl


end WeilConjectures
