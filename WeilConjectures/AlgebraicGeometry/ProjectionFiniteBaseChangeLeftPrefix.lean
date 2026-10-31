/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteProjectionIterationRealization

/-! # Projection and exchange at the start of the left base-change route

Source: prop-sf-pf-coherence.proof.md, base-change paragraph, tensor identifications.
-/

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
open CompactSupportFiniteProjection
private theorem exchange_transport
    {A B C E H : Type*} [Category A] [Category B] [Category C]
    [Category E] [Category H]
    (R : E ⥤ H) (U V : C ⥤ E) (F : A ⥤ C) (G : B ⥤ E) (W : A ⥤ B)
    (c : U ≅ V) (ex : F ⋙ U ⟶ W ⋙ G)
    {x : C} {y : B} {z z' : H} {k k' : A}
    (p : z ≅ R.obj (V.obj x)) (s : z' ≅ R.obj (G.obj y))
    (b : x ≅ F.obj k) (v : y ≅ W.obj k) (d : k ≅ k') :
    (p.hom ≫ R.map (V.map b.hom) ≫ R.map (c.inv.app _) ≫
        R.map (ex.app k) ≫ R.map (G.map v.inv) ≫ s.inv) ≫
      (s ≪≫ R.mapIso (G.mapIso (v ≪≫ W.mapIso d))).hom =
    (p ≪≫ R.mapIso (c.symm.app x)).hom ≫
      R.map (U.map (b.hom ≫ F.map d.hom) ≫ ex.app k') := by
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [s.inv_hom_id_assoc]
  rw [← R.map_comp_assoc (G.map v.inv) (G.map v.hom),
    ← G.map_comp, v.inv_hom_id, G.map_id, R.map_id, Category.id_comp]
  rw [← R.map_comp_assoc (V.map b.hom) (c.inv.app _), c.inv.naturality]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  have hn : U.map (F.map d.hom) ≫ ex.app k' = ex.app k ≫ G.map (W.map d.hom) :=
    ex.naturality d.hom
  rw [← R.map_comp (ex.app k) (G.map (W.map d.hom)), ← hn]
  simp -implicitDefEqProofs only [Functor.map_comp]
  rfl


private theorem prefix_pasting
    {C E H : Type*} [Category C] [Category E] [Category H]
    (R : E ⥤ H) (U : C ⥤ E)
    {x y z : H} {a₀ a₁ a₂ a₃ : C} {b₀ b₁ : E}
    (p : x ⟶ y) (q : y ⟶ z) (m : z ⟶ R.obj b₀)
    (e : y ⟶ R.obj (U.obj a₁))
    (p₀ : x ≅ R.obj b₁) (q₀ : b₁ ≅ U.obj a₀)
    (a : a₀ ⟶ a₁) (b : a₁ ⟶ a₃) (c : a₀ ≅ a₂) (d : a₂ ⟶ a₃)
    (f : U.obj a₃ ⟶ b₀)
    (hp : p ≫ e = (p₀ ≪≫ R.mapIso q₀).hom ≫ R.map (U.map a))
    (hc : a ≫ b = c.hom ≫ d)
    (he : q ≫ m = e ≫ R.map (U.map b ≫ f)) :
    p ≫ q ≫ m = (p₀ ≪≫ R.mapIso (q₀ ≪≫ U.mapIso c)).hom ≫
      R.map (U.map d ≫ f) := by
  rw [he, ← Category.assoc p, hp]
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (U.map a) (U.map b), ← U.map_comp, hc]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]


variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}


private theorem derived_pull_naturality
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {K L : sixFunctorFiniteCategory D C E n hn Y} (a : K ⟶ L) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let U := fixedDerivedPull (C := C) (E := E) (n := n) f
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let eK := pullRealization S f K ≪≫
      RX.functor.mapIso ((fixedPullComparison (C := C) (E := E) (n := n) f).symm.app _)
    let eL := pullRealization S f L ≪≫
      RX.functor.mapIso ((fixedPullComparison (C := C) (E := E) (n := n) f).symm.app _)
    IX.map ((S.finite.pull f).map a) ≫ eL.hom =
      eK.hom ≫ RX.functor.map (U.map (RY.inverse.map a.hom)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let IY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let e := (S.finitePullback f ≪≫ Functor.isoWhiskerLeft IY
    ((Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence Y.obj.left (Padic.coefficientExtensionRing C.l E n)).inverse
      (AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left ⋙
        (sfIntrinsicModuleEquivalence X.obj.left
          (Padic.coefficientExtensionRing C.l E n)).functor)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _))) ≪≫
    Functor.isoWhiskerLeft (IY ⋙ RY.inverse)
      (Functor.isoWhiskerRight
        (fixedPullComparison (C := C) (E := E) (n := n) f).symm RX.functor)
  exact e.hom.naturality a


-- Keep coefficient equivalences and tensor resolutions behind their coordinate APIs.
attribute [local implicit_reducible] realization fixedTensor fixedDerivedPull
  finiteTorConstructible partialTensor torPull CompactSupportFiniteProjection.tensor
  AlgebraicGeometry.ProEtale.derivedTensorRightDerivedLowerShriek
  AlgebraicGeometry.ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  fixedComponent
attribute [local irreducible] sixFunctorFiniteRealization sfIntrinsicDerivedEquivalence
  AlgebraicGeometry.ProEtale.derivedTensor component projectionTensorCoordinateComponent
  AlgebraicGeometry.ProEtale.projectionMapOfCompactification
  supportRealization pullRealization fixedSupportRealization fixedPullRealization
  sourceComparison fixedPullComparison sixFunctorProjectionFiniteTensorRealization
  AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor


/-- The inverse-coordinate projection square, before pullback or exchange. -/
private theorem projection_source_coordinates
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      Q.compactification
    let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj
      ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)
    let d := sixFunctorProjectionFiniteTensorRealization S Q.X K
        ((torPull S.toSixFunctorFiniteOperations Q.f).obj L) ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
    let b := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification M
    let p := component S.toSixFunctorFiniteOperations Q.f Q.compactification K L
    let c := RY.inverse.mapIso
        (sourceComparison S.toSixFunctorFiniteOperations Q.f Q.compactification K L) ≪≫
      (RY.unitIso.app _).symm
    let pf := fixedComponent (C := C) (E := E) (n := n) (hn := hn)
      Q.f Q.compactification (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)
    RY.inverse.map p.hom ≫ (b.hom ≫ F.map d.hom) = c.hom ≫ pf := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  simp -implicitDefEqProofs only [sourceComparison, projectionTensorLeftRealization]
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
  rw [inverse_unit_naturality]
  have hfc := fixed_component_realization S.toSixFunctorFiniteOperations Q.f
    Q.compactification K L
  simp -implicitDefEqProofs only [sixFunctorProjectionFiniteTensorRealization,
    ObjectProperty.ι_obj, ObjectProperty.ι_map, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv] at hfc ⊢
  conv_rhs at hfc => rw [← Category.assoc]
  exact hfc

/-- Exchange transport in fixed coordinates at an arbitrary normalized input. -/
private theorem realized_exchange_prefix
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (M : sixFunctorFiniteCategory D C E n hn Q.X)
    {T : DerivedCategory (Sheaf (ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))}
    (d : (realization (C := C) (E := E) (n := n) (hn := hn) Q.X).inverse.obj M.obj ≅ T) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
    let W := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      Q.compactification
    let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let b := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification M
    let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
      R'.functor.mapIso (G.mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ W.mapIso d))
    I.map (sixFunctorProjectionFiniteExchange S Q M) ≫ mid.hom =
      (pullRealization S.toSixFunctorFiniteOperations Q.g
          ((S.finite.support Q.f Q.compactification).obj M) ≪≫
        R'.functor.mapIso
          ((fixedPullComparison (C := C) (E := E) (n := n) Q.g).symm.app _)).hom ≫
      R'.functor.map (U.map (b.hom ≫ F.map d.hom) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
          Q.square Q.compactification).app _) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
  let V := sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) Q.g.hom.left
  let W := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    Q.compactification
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
  let b := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification M
  have he := exchange_transport R'.functor U V F G W
    (fixedPullComparison (C := C) (E := E) (n := n) Q.g)
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      Q.square Q.compactification)
    (pullRealization S.toSixFunctorFiniteOperations Q.g
      ((S.finite.support Q.f Q.compactification).obj M))
    (supportRealization S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M))
    b (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M) d
  let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
    R'.functor.mapIso (G.mapIso
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ W.mapIso d))
  simp -implicitDefEqProofs only [sixFunctorProjectionFiniteExchange, ObjectProperty.ι_map,
    ObjectProperty.homMk, SixFunctorOperationDatum.finiteExchangeProjection,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, ObjectProperty.ι_obj,
    Functor.comp_obj, R', V, b, F, G, realization, A, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc] at he ⊢
  exact he

/-- Projection followed by exchange, before the final tensor transport.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, first route.
(blueprint: lem-sf-finite-base-change-left-prefix).
Proof: expand the pullback realization and the prescribed exchange. Naturality of
pullRealization transports the conjugated finite projection to inverse coordinates.
The proved fixed-component realization calculation identifies its source and target
maps. Expand the exchange conjugation and use naturality of the fixed exchange;
its pull and support comparison isomorphisms cancel against `mid`. Naturality of
the coefficient-equivalence unit identifies the remaining endpoint with
`SquareSource`. Functoriality and associativity complete the displayed equation.
The result contains the full projection and exchange subcalculation, while the
final tensor/pullback-compositor transport is stated separately. The argument
uses only the prescribed comparison isomorphisms and applies to zero inputs,
identity maps and empty schemes. -/
theorem sixFunctorProjectionFinite_left_prefix
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
    let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
      (Q.compactification.ofIsPullback Q.square)
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj
      ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)
    let d := sixFunctorProjectionFiniteTensorRealization S Q.X K
        ((torPull S.toSixFunctorFiniteOperations Q.f).obj L) ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
    let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
        (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
      R'.functor.mapIso (F.mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ U.mapIso d))
    I.map ((S.finite.pull Q.g).map
        (component S.toSixFunctorFiniteOperations Q.f Q.compactification K L)) ≫
      I.map (sixFunctorProjectionFiniteExchange S Q M) ≫ mid.hom =
    (sixFunctorProjectionFiniteSquareSource S Q K L).hom ≫ R'.functor.map
      ((FiniteProjectionExchange.pull A Q.g.hom.left).map
          (FiniteProjectionExchange.pf A Q.compactification
            (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) ≫
        FiniteProjectionExchange.ex A Q.square Q.compactification
          (FiniteProjectionExchange.tensor A Q.X.obj.left (RX.inverse.obj K.obj)
            ((FiniteProjectionExchange.pull A Q.f.hom.left).obj
              (RY.inverse.obj L.obj)))) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
  let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
  let U := fixedDerivedPull (C := C) (E := E) (n := n) Q.g
  let V := sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) Q.g.hom.left
  let W := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    Q.compactification
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
  let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj
    ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)
  let d := sixFunctorProjectionFiniteTensorRealization S Q.X K
      ((torPull S.toSixFunctorFiniteOperations Q.f).obj L) ≪≫
    (TX.obj (RX.inverse.obj K.obj)).mapIso
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
  let b := fixedSupportRealization S.toSixFunctorFiniteOperations Q.f Q.compactification M
  let p := component S.toSixFunctorFiniteOperations Q.f Q.compactification K L
  let c := RY.inverse.mapIso
      (sourceComparison S.toSixFunctorFiniteOperations Q.f Q.compactification K L) ≪≫
    (RY.unitIso.app _).symm
  let pf := fixedComponent (C := C) (E := E) (n := n) (hn := hn)
    Q.f Q.compactification (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)
  have hp := derived_pull_naturality S.toSixFunctorFiniteOperations Q.g p
  have hc := projection_source_coordinates S Q K L
  let mid := supportRealization S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M) ≪≫
    R'.functor.mapIso (G.mapIso
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ W.mapIso d))
  have he' := realized_exchange_prefix S Q M d
  simp -implicitDefEqProofs only [FiniteProjectionExchange.pf]
  rw [← projectionTensorCoordinateComponent_eq]
  unfold sixFunctorProjectionFiniteSquareSource
  exact prefix_pasting R'.functor U
    (I.map ((S.finite.pull Q.g).map p))
    (I.map (sixFunctorProjectionFiniteExchange S Q M)) mid.hom _
    (pullRealization S.toSixFunctorFiniteOperations Q.g
      (((partialTensor S.toSixFunctorFiniteOperations Q.Y).obj
        ((S.finite.support Q.f Q.compactification).obj K)).obj L))
    ((fixedPullComparison (C := C) (E := E) (n := n) Q.g).symm.app _)
    (RY.inverse.map p.hom) (b.hom ≫ F.map d.hom) c pf
    (FiniteProjectionExchange.ex A Q.square Q.compactification
      (FiniteProjectionExchange.tensor A Q.X.obj.left (RX.inverse.obj K.obj)
        ((FiniteProjectionExchange.pull A Q.f.hom.left).obj (RY.inverse.obj L.obj))))
    hp hc he'

end WeilConjectures
