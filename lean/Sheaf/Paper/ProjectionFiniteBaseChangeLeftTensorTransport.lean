/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import Sheaf.Paper.FinitePullbackCompositionFixedCoordinates

/-! # Tensor and pullback comparisons at the end of the left base-change route

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
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem inverse_realized
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x : B} {a b : A} (p : x ≅ R.functor.obj a) (q : a ⟶ b) :
    R.inverse.map (p.hom ≫ R.functor.map q) ≫ R.unitIso.inv.app b =
      (R.inverse.mapIso p ≪≫ (R.unitIso.app a).symm).hom ≫ q := by
  simp -implicitDefEqProofs only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← Functor.comp_map, R.unitIso.inv.naturality q]
  rfl

private theorem square_pasting
    {A : Type*} [Category A] {x y x' y' w z w' z' : A}
    (a : x ≅ y) (b : x' ≅ y') (c : w ≅ z) (d : w' ≅ z')
    (p : y ⟶ z) (q : x ⟶ w) (p' : y' ⟶ z') (q' : x' ⟶ w')
    (t : x ⟶ x') (u : w ⟶ w')
    (h1 : a.hom ≫ p = q ≫ c.hom) (h2 : b.hom ≫ p' = q' ≫ d.hom)
    (hc : t ≫ q' = q ≫ u) :
    a.inv ≫ t ≫ b.hom ≫ p' = p ≫ c.inv ≫ u ≫ d.hom := by
  rw [h2, ← Category.assoc t, hc]
  apply (cancel_epi a.hom).1
  simp only [← Category.assoc, a.hom_inv_id, Category.id_comp]
  rw [h1]
  simp only [Category.assoc, c.hom_inv_id_assoc]

private theorem support_pasting
    {A B : Type*} [Category A] [Category B] (H : A ⥤ B)
    {x y : B} {a b c d : A} (v : x ⟶ y)
    (s : y ≅ H.obj a) (t : x ≅ H.obj b) (e : a ≅ c) (f : b ≅ d)
    (w : b ⟶ a) (z : d ⟶ c)
    (hs : v ≫ s.hom = t.hom ≫ H.map w)
    (ht : w ≫ e.hom = f.hom ≫ z) :
    v ≫ (s ≪≫ H.mapIso e).hom = (t ≪≫ H.mapIso f).hom ≫ H.map z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc]
  rw [hs]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [ht]

private theorem support_naturality
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {K L : sixFunctorFiniteCategory D C E n hn X} (a : K ⟶ L) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let IY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
    IY.map ((S.finite.support f c).map a) ≫ (supportRealization S f c L).hom =
      (supportRealization S f c K).hom ≫ RY.functor.map (F.map (RX.inverse.map a.hom)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let F := sixFunctorFiniteSupport D C E n hn f c
  let e := S.finiteSupport f c ≪≫ Functor.isoWhiskerLeft IX
    (Functor.isoWhiskerRight RX.counitIso.symm F ≪≫
      Functor.isoWhiskerLeft RX.inverse
        (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c))
  exact e.hom.naturality a

private theorem pull_cast
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} {f g : X ⟶ Y} (h : f = g)
    (L : sixFunctorFiniteCategory D C E n hn Y) :
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    RX.inverse.map (eqToHom (congrArg (fun f ↦ ((S.finite.pull f).obj L).obj) h)) ≫
        (fixedPullRealization S g L).hom =
      (fixedPullRealization S f L).hom ≫
        eqToHom (congrArg (fun f ↦ (fixedDerivedPull (C := C) (E := E) (n := n) f).obj
          (RY.inverse.obj L.obj)) h) := by
  subst g
  simp -implicitDefEqProofs only [eqToHom_refl]
  rw [(realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.map_id]
  simp -implicitDefEqProofs only [Category.id_comp, Category.comp_id]

attribute [local implicit_reducible] finiteTorConstructible partialTensor torPull tensor
  fixedTensor fixedDerivedPull coordinates

attribute [local irreducible] realization AlgebraicGeometry.ProEtale.derivedTensor
  DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local irreducible] fixedPullRealization pullRealization supportRealization
  sixFunctorProjectionFiniteMu
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor

private theorem derived_cast_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (L : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    eqToHom (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj L)
      h) = (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h.symm).inv.app L := by
  subst g
  rfl

set_option maxHeartbeats 1200000 in
-- Normalizing the full coefficient and derived-functor expressions needs extra heartbeats.
private theorem square_pull
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let P := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let P' := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
    let tau := (torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
      ObjectProperty.homMk (eqToHom (congrArg
        (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
      (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom
    R.inverse.map tau.hom ≫
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.f'
        ⟨((torPull S.toSixFunctorFiniteOperations Q.g).obj L).obj,
          ((torPull S.toSixFunctorFiniteOperations Q.g).obj L).property.1⟩).hom ≫
      P'.map (fixedPullRealization S.toSixFunctorFiniteOperations Q.g
        ⟨L.obj, L.property.1⟩).hom =
    (fixedPullRealization S.toSixFunctorFiniteOperations Q.g'
      ⟨((torPull S.toSixFunctorFiniteOperations Q.f).obj L).obj,
        ((torPull S.toSixFunctorFiniteOperations Q.f).obj L).property.1⟩).hom ≫
      P.map (fixedPullRealization S.toSixFunctorFiniteOperations Q.f
        ⟨L.obj, L.property.1⟩).hom ≫
      (FiniteProjectionExchange.theta A Q.square.toCommSq).inv.app (RY.inverse.obj L.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
  let N : sixFunctorFiniteCategory D C E n hn Q.Y := ⟨L.obj, L.property.1⟩
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.X'.obj.left).ι
  let a := R.inverse.mapIso (I.mapIso ((S.finite.pullComposition Q.g' Q.f).app N))
  let b := R.inverse.mapIso (I.mapIso ((S.finite.pullComposition Q.f' Q.g).app N))
  let c := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    Q.g'.hom.left Q.f.hom.left).app (RY.inverse.obj L.obj)
  let d := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    Q.f'.hom.left Q.g.hom.left).app (RY.inverse.obj L.obj)
  let t := R.inverse.map (eqToHom (congrArg
    (fun f ↦ ((S.finite.pull f).obj N).obj) Q.squareComm))
  let v := (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
    (congrArg (fun f ↦ f.hom.left) Q.squareComm).symm).inv.app (RY.inverse.obj L.obj)
  have h1 := pullbackComposition_fixed_coordinates S.toSixFunctorFiniteOperations Q.g' Q.f N
  have h2 := pullbackComposition_fixed_coordinates S.toSixFunctorFiniteOperations Q.f' Q.g N
  have hc := pull_cast S.toSixFunctorFiniteOperations Q.squareComm N
  have hv := derived_cast_inv A (congrArg (fun f ↦ f.hom.left) Q.squareComm)
    (RY.inverse.obj L.obj)
  have hc' : t ≫ (fixedPullRealization S.toSixFunctorFiniteOperations (Q.f' ≫ Q.g) N).hom =
      (fixedPullRealization S.toSixFunctorFiniteOperations (Q.g' ≫ Q.f) N).hom ≫ v :=
    hc.trans (congrArg (fun z ↦
      (fixedPullRealization S.toSixFunctorFiniteOperations (Q.g' ≫ Q.f) N).hom ≫ z) hv)
  have h := square_pasting a b c d _ _ _ _ t v h1 h2 hc'
  simp -implicitDefEqProofs only [a, b, c, d, t, v, torPullComposition,
    ObjectProperty.isoMk_hom, ObjectProperty.isoMk_inv,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    FiniteProjectionExchange.theta, leftDerivedUpperStarSquareIso,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc] at h ⊢
  convert h using 1 <;> rfl

private theorem tensor_inverse_cancel
    {A : Type*} [Category A] (T : A ⥤ A ⥤ A)
    {k k' l l' : A} (e : k' ≅ k) (d : l' ≅ l) :
    ((T.mapIso e.symm).app l).hom ≫ (T.obj k').map d.inv ≫
      ((T.mapIso e).app l').hom ≫ (T.obj k).map d.hom = 𝟙 _ := by
  change (T.map e.inv).app l ≫ (T.obj k').map d.inv ≫
    (T.map e.hom).app l' ≫ (T.obj k).map d.hom = _
  rw [← NatTrans.naturality_assoc]
  rw [← NatTrans.comp_app_assoc, ← T.map_comp, e.inv_hom_id, T.map_id]
  simp -implicitDefEqProofs only [NatTrans.id_app, Category.id_comp, ← Functor.map_comp,
    d.inv_hom_id]
  exact (T.obj k).map_id l

set_option maxHeartbeats 1200000 in
-- Normalizing the full coefficient and derived-functor expressions needs extra heartbeats.
private theorem mu_fixed
    (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn Y)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let T := fixedTensor (C := C) (E := E) (n := n) X
    let P := fixedDerivedPull (C := C) (E := E) (n := n) f
    let k := RX.inverse.obj ((S.finite.pull f).obj K).obj
    let l := RX.inverse.obj ((torPull S.toSixFunctorFiniteOperations f).obj L).obj
    RX.inverse.map (sixFunctorProjectionFiniteMu S f K L).hom.hom ≫
      RX.unitIso.inv.app ((T.obj k).obj l) ≫
      ((T.mapIso (fixedPullRealization S.toSixFunctorFiniteOperations f K)).app l).hom ≫
      (T.obj (P.obj (RY.inverse.obj K.obj))).map
        (fixedPullRealization S.toSixFunctorFiniteOperations f ⟨L.obj, L.property.1⟩).hom =
    (fixedPullRealization S.toSixFunctorFiniteOperations f
      (((partialTensor S.toSixFunctorFiniteOperations Y).obj K).obj L)).hom ≫
      P.map (sixFunctorProjectionFiniteTensorRealization S Y K L).hom ≫
      (FiniteProjectionExchange.mu A f.hom.left (RY.inverse.obj K.obj)
        (RY.inverse.obj L.obj)).hom := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let T := fixedTensor (C := C) (E := E) (n := n) X
  let P := fixedDerivedPull (C := C) (E := E) (n := n) f
  let M := ((partialTensor S.toSixFunctorFiniteOperations Y).obj K).obj L
  let e := fixedPullRealization S.toSixFunctorFiniteOperations f K
  let d := fixedPullRealization S.toSixFunctorFiniteOperations f ⟨L.obj, L.property.1⟩
  let q := (fixedPullComparison (C := C) (E := E) (n := n) f).symm.app
      (RY.inverse.obj M.obj) ≪≫
    P.mapIso (sixFunctorProjectionFiniteTensorRealization S Y K L) ≪≫
    leftDerivedUpperStarTensorIso
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      f.hom.left (RY.inverse.obj K.obj) (RY.inverse.obj L.obj) ≪≫
    (T.mapIso e.symm).app _ ≪≫ (T.obj _).mapIso d.symm
  unfold sixFunctorProjectionFiniteMu
  change RX.inverse.map ((pullRealization S.toSixFunctorFiniteOperations f M).hom ≫
    RX.functor.map q.hom) ≫ _ = _
  erw [reassoc_of% inverse_realized RX (pullRealization S.toSixFunctorFiniteOperations f M)
    q.hom]
  dsimp only [q]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
  simp -implicitDefEqProofs only [Category.assoc]
  erw [tensor_inverse_cancel T e d]
  erw [Category.comp_id]
  simp only [fixedPullRealization, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv]
  simp only [Category.assoc]
  rfl

private theorem tensor_transport
    {A B : Type*} [Category A] [Category B] (R : A ≌ B) (T : A ⥤ A ⥤ A)
    {k k' l₀ l₁ l₂ l₃ : A} {x : B} {y : A}
    (m : x ⟶ R.functor.obj ((T.obj k).obj l₀)) (e : k ≅ k')
    (tau : l₀ ⟶ l₁) (r : l₀ ⟶ l₂) (target : l₁ ⟶ l₃) (tail : l₂ ⟶ l₃)
    (p : R.inverse.obj x ⟶ y) (z : y ⟶ (T.obj k').obj l₂)
    (hm : R.inverse.map m ≫ R.unitIso.inv.app ((T.obj k).obj l₀) ≫
      (T.map e.hom).app l₀ ≫ (T.obj k').map r = p ≫ z)
    (hs : tau ≫ target = r ≫ tail) :
    R.inverse.map (m ≫ R.functor.map ((T.obj k).map tau)) ≫
      R.unitIso.inv.app ((T.obj k).obj l₁) ≫
      (T.map e.hom).app l₁ ≫ (T.obj k').map target =
    p ≫ z ≫ (T.obj k').map tail := by
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map, R.unitIso.inv.naturality_assoc]
  simp -implicitDefEqProofs only [Functor.id_map]
  rw [(T.map e.hom).naturality_assoc]
  rw [← (T.obj k').map_comp, hs]
  simp -implicitDefEqProofs only [Functor.map_comp]
  rw [reassoc_of% hm]

private theorem tensor_pasting
    {A : Type*} [Category A] (T : A ⥤ A ⥤ A)
    {k k' l₁ l₂ l₃ l₄ l₅ x b y z z' : A}
    {a : x ⟶ b} {u : b ⟶ (T.obj k).obj l₁}
    {p : x ⟶ y} {q : y ⟶ z} {mu₀ : z ⟶ (T.obj k').obj l₂}
    {q' : z ⟶ z'} {mu₁ : z' ⟶ (T.obj k').obj l₄}
    (e : k ≅ k') (r : l₁ ⟶ l₅) (s : l₅ ⟶ l₃)
    (v : l₂ ⟶ l₄) (theta : l₄ ⟶ l₃)
    (ht : a ≫ u ≫ (T.map e.hom).app l₁ ≫ (T.obj k').map (r ≫ s) =
      p ≫ q ≫ mu₀ ≫ (T.obj k').map (v ≫ theta))
    (hn : mu₀ ≫ (T.obj k').map v = q' ≫ mu₁) :
    a ≫ u ≫ (T.obj k).map r ≫ (T.map e.hom).app l₅ ≫ (T.obj k').map s =
      p ≫ q ≫ q' ≫ mu₁ ≫ (T.obj k').map theta := by
  simp only [Functor.map_comp] at ht ⊢
  rw [(T.map e.hom).naturality_assoc, ht, reassoc_of% hn]

private theorem tensor_identity_map
    {A : Type*} [Category A] (T : A ⥤ A ⥤ A)
    {k l l' : A} (a : l ⟶ l') :
    (T.map (𝟙 k)).app l ≫ (T.obj k).map a = (T.obj k).map a := by
  rw [T.map_id, NatTrans.id_app, Category.id_comp]

private theorem mu_naturality_right
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : FiniteProjectionExchange.Dcat A Y)
    {L L' : FiniteProjectionExchange.Dcat A Y} (a : L ⟶ L') :
    (FiniteProjectionExchange.mu A f K L).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((FiniteProjectionExchange.pull A f).obj K)).map
          ((FiniteProjectionExchange.pull A f).map a) =
    (FiniteProjectionExchange.pull A f).map
      (((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map a) ≫
      (FiniteProjectionExchange.mu A f K L').hom := by
  exact (((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) f).hom.app K).naturality a).symm

set_option maxHeartbeats 1200000 in
-- Normalizing the full coefficient and derived-functor expressions needs extra heartbeats.
private theorem tensor_square_fixed
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let T := fixedTensor (C := C) (E := E) (n := n) Q.X'
    let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
    let P := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
    let P' := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
    let K' := (S.finite.pull Q.g').obj K
    let Lf := (torPull S.toSixFunctorFiniteOperations Q.f).obj L
    let Lg := (torPull S.toSixFunctorFiniteOperations Q.g).obj L
    let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj Lf
    let tau := (torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
      ObjectProperty.homMk (eqToHom (congrArg
        (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
      (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom
    let w := (sixFunctorProjectionFiniteMu S Q.g' K Lf).hom ≫
      ((partialTensor S.toSixFunctorFiniteOperations Q.X').obj K').map tau
    let e := sixFunctorProjectionFiniteTensorRealization S Q.X' K'
        ((torPull S.toSixFunctorFiniteOperations Q.f').obj Lg) ≪≫
      (T.obj (R.inverse.obj K'.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f' ⟨Lg.obj, Lg.property.1⟩) ≪≫
      (T.mapIso (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K)).app _ ≪≫
      (T.obj _).mapIso (P'.mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩))
    let d := sixFunctorProjectionFiniteTensorRealization S Q.X K Lf ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
    R.inverse.map w.hom ≫ e.hom =
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ P.mapIso d).hom ≫
      FiniteProjectionExchange.target A Q.square (RX.inverse.obj K.obj)
        (RY.inverse.obj L.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y
  let T := fixedTensor (C := C) (E := E) (n := n) Q.X'
  let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
  let P := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
  let P' := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
  let K' := (S.finite.pull Q.g').obj K
  let Lf := (torPull S.toSixFunctorFiniteOperations Q.f).obj L
  let Lg := (torPull S.toSixFunctorFiniteOperations Q.g).obj L
  let tau := (torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
    ObjectProperty.homMk (eqToHom (congrArg
      (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
    (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom
  let rk := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K
  let rl := fixedPullRealization S.toSixFunctorFiniteOperations Q.g' ⟨Lf.obj, Lf.property.1⟩
  let rf := fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩
  let rf' := fixedPullRealization S.toSixFunctorFiniteOperations Q.f' ⟨Lg.obj, Lg.property.1⟩
  let rg := fixedPullRealization S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩
  let m := (sixFunctorProjectionFiniteMu S Q.g' K Lf).hom.hom
  have hm := mu_fixed S Q.g' K Lf
  have hs := square_pull S Q L
  have ht := tensor_transport R T m rk (R.inverse.map tau.hom) rl.hom
    (rf'.hom ≫ P'.map rg.hom)
    (P.map rf.hom ≫ (FiniteProjectionExchange.theta A Q.square.toCommSq).inv.app
      (RY.inverse.obj L.obj)) _ _ hm hs
  simp -implicitDefEqProofs only [Category.assoc] at ht
  have hn := mu_naturality_right A Q.g'.hom.left (RX.inverse.obj K.obj) rf.hom
  have h := tensor_pasting T rk rf'.hom (P'.map rg.hom) (P.map rf.hom)
    ((FiniteProjectionExchange.theta A Q.square.toCommSq).inv.app (RY.inverse.obj L.obj))
    ht hn
  have hw : (((partialTensor S.toSixFunctorFiniteOperations Q.X').obj K').map tau).hom =
      R.functor.map ((T.obj (R.inverse.obj K'.obj)).map (R.inverse.map tau.hom)) := by
    change R.functor.map ((T.map (R.inverse.map (𝟙 K'.obj))).app _) ≫ _ = _
    rw [R.inverse.map_id, T.map_id]
    simp only [NatTrans.id_app, R.functor.map_id, Category.id_comp]
    rfl
  change R.inverse.map (m ≫
    (((partialTensor S.toSixFunctorFiniteOperations Q.X').obj K').map tau).hom) ≫ _ = _
  rw [hw]
  dsimp only
  simp -implicitDefEqProofs only [sixFunctorProjectionFiniteTensorRealization,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, FiniteProjectionExchange.target,
    FiniteProjectionExchange.tensorMap] at h ⊢
  erw [tensor_identity_map]
  convert h using 1 <;> rfl

set_option maxHeartbeats 1200000 in
-- Normalizing the full coefficient and derived-functor expressions needs extra heartbeats.
/-- The final tensor/pullback transport of the left route has its fixed-scalar target.
This assertion contains no projection component and no exchange map.

Source: prop-sf-pf-coherence.proof.md, base-change paragraph, canonical monoidality
and pullback-square comparisons; finitePullCompositionNormalization.
(blueprint: lem-sf-finite-base-change-left-tensor-transport).

Proof: move the tensor transport across supportRealization by naturality. Expand Mu
and cancel its inverse fixed-pull comparisons against the target tensor comparisons.
Naturality of the coefficient equivalence unit cancels the remaining tensor unit.
Use finitePullCompositionNormalization on each of the two restricted compositors.
The equality transport for Q.squareComm then gives the inverse canonical derived
square comparison. More explicitly, write r_h for fixedPullRealization along h and
tau for the displayed restricted square transport. In inverse realization coordinates,
tau followed by r_f' at g-star L and f'-star of r_g equals r_g' at f-star L,
then g'-star of r_f, then the inverse fixed square comparison. This follows by
applying the two normalization equations, cancelling their common composite-map
pullback realization, and transporting that realization along Q.squareComm.
Tensor this equation with the fixed first input. Naturality of the canonical
monoidality map moves r_f through it, giving the fixed-scalar target. This calculation
uses only invertible coordinate comparisons, and is valid for zero inputs, identity
maps and empty schemes. No finite-Tor assumption on the first input is used. -/
theorem sixFunctorProjectionFinite_left_tensor_transport
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
    I.map ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map
      ((sixFunctorProjectionFiniteMu S Q.g' K
          ((torPull S.toSixFunctorFiniteOperations Q.f).obj L)).hom ≫
        ((partialTensor S.toSixFunctorFiniteOperations Q.X').obj
          ((S.finite.pull Q.g').obj K)).map
          ((torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
            ObjectProperty.homMk (eqToHom (congrArg
              (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj)
              Q.squareComm)) ≫
            (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom))) ≫
      (sixFunctorProjectionFiniteSquareTarget S Q K L).hom =
    mid.hom ≫ R'.functor.map (F.map
      (FiniteProjectionExchange.target A Q.square (RX.inverse.obj K.obj)
        (RY.inverse.obj L.obj))) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) Q.X'
  let R' := realization (C := C) (E := E) (n := n) (hn := hn) Q.Y'
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
    (Q.compactification.ofIsPullback Q.square)
  let K' := (S.finite.pull Q.g').obj K
  let Lf := (torPull S.toSixFunctorFiniteOperations Q.f).obj L
  let M := ((partialTensor S.toSixFunctorFiniteOperations Q.X).obj K).obj Lf
  let tau := (torPullComposition S.toSixFunctorFiniteOperations Q.g' Q.f L).inv ≫
    ObjectProperty.homMk (eqToHom (congrArg
      (fun f ↦ ((torPull S.toSixFunctorFiniteOperations f).obj L).obj) Q.squareComm)) ≫
    (torPullComposition S.toSixFunctorFiniteOperations Q.f' Q.g L).hom
  let w := (sixFunctorProjectionFiniteMu S Q.g' K Lf).hom ≫
    ((partialTensor S.toSixFunctorFiniteOperations Q.X').obj K').map tau
  have hs := support_naturality S.toSixFunctorFiniteOperations Q.f'
    (Q.compactification.ofIsPullback Q.square) w
  have ht := tensor_square_fixed S Q K L
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) Q.X
  let T := fixedTensor (C := C) (E := E) (n := n) Q.X'
  let TX := fixedTensor (C := C) (E := E) (n := n) Q.X
  let P := fixedDerivedPull (C := C) (E := E) (n := n) Q.g'
  let P' := fixedDerivedPull (C := C) (E := E) (n := n) Q.f'
  let Lg := (torPull S.toSixFunctorFiniteOperations Q.g).obj L
  let e := sixFunctorProjectionFiniteTensorRealization S Q.X' K'
      ((torPull S.toSixFunctorFiniteOperations Q.f').obj Lg) ≪≫
    (T.obj (R.inverse.obj K'.obj)).mapIso
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.f' ⟨Lg.obj, Lg.property.1⟩) ≪≫
    (T.mapIso (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' K)).app _ ≪≫
    (T.obj _).mapIso (P'.mapIso
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.g ⟨L.obj, L.property.1⟩))
  let d := sixFunctorProjectionFiniteTensorRealization S Q.X K Lf ≪≫
    (TX.obj (RX.inverse.obj K.obj)).mapIso
      (fixedPullRealization S.toSixFunctorFiniteOperations Q.f ⟨L.obj, L.property.1⟩)
  have hp := support_pasting (F ⋙ R'.functor)
    ((intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι.map
      ((S.finite.support Q.f' (Q.compactification.ofIsPullback Q.square)).map w))
    (supportRealization S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) _)
    (supportRealization S.toSixFunctorFiniteOperations Q.f'
      (Q.compactification.ofIsPullback Q.square) ((S.finite.pull Q.g').obj M))
    e (fixedPullRealization S.toSixFunctorFiniteOperations Q.g' M ≪≫ P.mapIso d)
    (R.inverse.map w.hom) _ hs ht
  unfold sixFunctorProjectionFiniteSquareTarget
  simp -implicitDefEqProofs only [e, d, w, tau, targetComparison,
    projectionTensorTargetRealization, sixFunctorProjectionFiniteTensorRealization,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.comp_map, Functor.map_comp, Category.assoc] at hp ⊢
  convert hp using 1 <;> rfl

end WeilConjectures
