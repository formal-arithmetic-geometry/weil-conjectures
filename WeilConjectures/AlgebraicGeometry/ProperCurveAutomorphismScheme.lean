/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.Curve.ProperProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveCurveIsomGraphs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import WeilConjectures.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Automorphism schemes of proper curves

Source: Stacks Project, moduli-curves.tex, Tag 0DSQ, pulled back along `(C,C)`;
Yoneda constructs the group structure on the projective Isom scheme
(blueprint: lem-sfb-proper-curve-automorphism-scheme).

The automorphisms over a test scheme are natural automorphisms of the restriction to
its slice site. This is the sheaf of the fibre product over that test scheme: on a
scheme over `T` its sections are exactly the sections of `C` on that scheme. Thus no
scheme presentation of `C`, or reducedness assumption on the test scheme, is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structural map to the represented base scheme, on every test scheme.
Source: Stacks Project, Tag 025Y, algebraic spaces over a base
(blueprint: lem-sfb-proper-curve-automorphism-scheme). -/
def automorphismSchemeStructureMap {S : Scheme.{u}} (C : AlgebraicSpace S) :
    C.obj.obj ⟶ yoneda.obj (Over.mk (𝟙 S)) where
  app T := ↾fun _ ↦ Over.homMk T.unop.hom (by simp)
  naturality := by
    intro T U a
    ext x
    apply Over.OverMorphism.ext
    exact a.unop.w.symm

/-- Automorphisms of `C ×_S T` over `T`, expressed on the slice of test schemes over `T`.
The slice `Over T` here is the slice of `Over S`, canonically equivalent to schemes over
`T.left`. Restricting the sheaf to this slice is its sheaf fibre product with `h_T`.
Source: Stacks Project, Tag 0DSQ, the Isom functor with both arguments equal
(blueprint: lem-sfb-proper-curve-automorphism-scheme). -/
abbrev curveAutomorphisms {S : Scheme.{u}} (C : AlgebraicSpace S) (T : Over S) :=
  Aut ((Over.forget T).op ⋙ C.obj.obj)

/-- Pullback of automorphisms is restriction along composition of test-scheme maps.
The identity `Over.map a ⋙ Over.forget T = Over.forget T'` makes this an automorphism
of precisely the restriction for `T'`, without a choice of a comparison isomorphism.
Source: Stacks Project, Tag 0DSQ, functoriality of the Isom functor
(blueprint: lem-sfb-proper-curve-automorphism-scheme). -/
def curveAutomorphismBaseChange {S : Scheme.{u}} (C : AlgebraicSpace S)
    {T' T : Over S} (a : T' ⟶ T) (α : curveAutomorphisms C T) :
    curveAutomorphisms C T' :=
  Functor.isoWhiskerLeft (Over.map a).op α

private theorem representableWith_of_iso {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {F G F' G' : (Over S)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (h : IsRepresentableWith P f) (e : F ≅ F') (d : G ≅ G') :
    IsRepresentableWith P (e.inv ≫ f ≫ d.hom) := by
  intro T a
  obtain ⟨U, p, q, hp, hP⟩ := h T (a ≫ d.inv)
  refine ⟨U, p, q ≫ e.hom, ?_, hP⟩
  exact hp.of_iso (Iso.refl _) e (Iso.refl _) d (by simp) (by simp)
    (by simp) (by simp)

private theorem iso_isEtale {S : Scheme.{u}} {U : Over S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (e : yoneda.obj U ≅ F) : IsEtale e.hom := by
  intro T a
  refine ⟨T, 𝟙 T, a ≫ e.inv, ?_, ?_⟩
  · simpa using (IsPullback.of_vert_isIso
      (fst := a ≫ e.inv) (snd := 𝟙 (yoneda.obj T)) (f := e.hom) (g := a)
      ⟨by simp⟩)
  · change Etale (𝟙 T.left)
    infer_instance

private def relativeProductIso {D : Type*} [Category D] [HasBinaryProducts D]
    [HasPullbacks D] {F B : D} (hB : IsTerminal B) (f : F ⟶ B) :
    Limits.pullback f f ≅ Limits.prod F F where
  hom := prod.lift (Limits.pullback.fst f f) (Limits.pullback.snd f f)
  inv := Limits.pullback.lift prod.fst prod.snd (hB.hom_ext _ _)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

private def structure_terminal {S : Scheme.{u}} :
    IsTerminal (yoneda.obj (Over.mk (𝟙 S))) :=
  (Over.mkIdTerminal (X := S)).isTerminalObj yoneda _

private theorem separated_absolute {S : Scheme.{u}} (C : AlgebraicSpace S)
    (h : MapToSchemeIsSeparated C (Over.mk (𝟙 S)) (automorphismSchemeStructureMap C)) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 C.obj.obj) (𝟙 C.obj.obj)) := by
  have hh := representableWith_of_iso _ h (Iso.refl _)
    (relativeProductIso structure_terminal (automorphismSchemeStructureMap C))
  convert hh using 1
  apply prod.hom_ext <;> simp [relativeProductIso]

private def representedPoint {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {U : Over S} (e : yoneda.obj U ≅ F) : Point F → U.left :=
  Quot.lift (fun p ↦ (e.inv.app _ p.value).left (IsLocalRing.closedPoint p.K)) (by
    rintro p q ⟨L, hL, t, a, b, h⟩
    have ha := (ConcreteCategory.congr_hom (e.inv.naturality a.op) p.value).symm
    have hb := (ConcreteCategory.congr_hom (e.inv.naturality b.op) q.value).symm
    change a ≫ e.inv.app _ p.value = e.inv.app _ (F.map a.op p.value) at ha
    change b ≫ e.inv.app _ q.value = e.inv.app _ (F.map b.op q.value) at hb
    have hab : a ≫ e.inv.app _ p.value = b ≫ e.inv.app _ q.value := by
      rw [ha, hb, h]
    have hh := congrArg (fun f ↦ f.left (IsLocalRing.closedPoint L)) hab
    change (e.inv.app _ p.value).left (a.left (IsLocalRing.closedPoint L)) =
      (e.inv.app _ q.value).left (b.left (IsLocalRing.closedPoint L)) at hh
    have hap : a.left (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint p.K :=
      Subsingleton.elim (α := Spec (.of p.K)) _ _
    have hbq : b.left (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint q.K :=
      Subsingleton.elim (α := Spec (.of q.K)) _ _
    simpa only [hap, hbq] using hh)

private theorem representedPoint_schemePointMap {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U T : Over S} (e : yoneda.obj U ≅ F)
    (a : yoneda.obj T ⟶ F) (x : T.left) :
    representedPoint e (schemePointMap a x) = (yoneda.preimage (a ≫ e.inv)).left x := by
  change (e.inv.app _ (a.app _ _)).left _ = _
  have ha := congrArg (fun f ↦ f.app (op (Over.mk
      (T.left.fromSpecResidueField x ≫ T.hom)))
      (Over.homMk (T.left.fromSpecResidueField x) rfl))
    (yoneda.map_preimage (a ≫ e.inv))
  change _ = e.inv.app _ (a.app _ _) at ha
  rw [← ha]
  change (T.left.fromSpecResidueField x ≫
    (yoneda.preimage (a ≫ e.inv)).left) _ = _
  simp

private theorem representedPoint_inverse {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (e : yoneda.obj U ≅ F) :
    Function.RightInverse (schemePointMap e.hom) (representedPoint e) := by
  intro x
  rw [representedPoint_schemePointMap]
  have h : yoneda.preimage (e.hom ≫ e.inv) = 𝟙 U := by simp
  rw [h]
  rfl

private theorem representedPoint_leftInverse {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (e : yoneda.obj U ≅ F) :
    Function.LeftInverse (schemePointMap e.hom) (representedPoint e) := by
  intro p
  induction p using Quot.inductionOn with
  | h p =>
    let f := e.inv.app _ p.value
    let x := f.left (IsLocalRing.closedPoint p.K)
    let g := Scheme.descResidueField (Scheme.stalkClosedPointTo f.left)
    have hg : Spec.map g ≫ U.left.fromSpecResidueField x = f.left :=
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField p.K U.left f.left
    change Quot.mk _ _ = Quot.mk _ p
    apply Quot.sound
    let a : Over.mk p.base ⟶
        Over.mk (U.left.fromSpecResidueField x ≫ U.hom) :=
      Over.homMk (Spec.map g) (by
        change Spec.map g ≫ (U.left.fromSpecResidueField x ≫ U.hom) = p.base
        rw [← Category.assoc, hg]
        exact f.w)
    refine ⟨p.K, inferInstance, p.base, a, 𝟙 _, ?_⟩
    change F.map a.op (e.hom.app _
      (Over.homMk (U.left.fromSpecResidueField x) rfl)) = F.map (𝟙 _).op p.value
    rw [← NatTrans.naturality_apply]
    have ha : a ≫ Over.homMk (U.left.fromSpecResidueField x) rfl = f := by
      ext1
      exact hg
    change e.hom.app _ (a ≫ Over.homMk (U.left.fromSpecResidueField x) rfl) = _
    rw [ha]
    rw [op_id, F.map_id]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app (op (Over.mk p.base))) p.value

private def representedPointHomeomorph {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (e : yoneda.obj U ≅ F) : Point F ≃ₜ U.left where
  toFun := representedPoint e
  invFun := schemePointMap e.hom
  left_inv := representedPoint_leftInverse e
  right_inv := representedPoint_inverse e
  continuous_toFun := by
    change @Continuous _ _ (⨆ (T : Over S) (a : yoneda.obj T ⟶ F) (_ : IsEtale a),
      TopologicalSpace.coinduced (schemePointMap a) inferInstance) _ _
    simp only [continuous_iSup_dom]
    intro T a _
    rw [continuous_coinduced_dom]
    convert (yoneda.preimage (a ≫ e.inv)).left.continuous using 1
    funext x
    exact representedPoint_schemePointMap e a x
  continuous_invFun := by
    apply continuous_iff_coinduced_le.mpr
    exact le_iSup_of_le U (le_iSup_of_le e.hom (le_iSup_of_le (iso_isEtale e) le_rfl))

private theorem represented_mapPoint {S : Scheme.{u}}
    {F H : (Over S)ᵒᵖ ⥤ Type u} {U V : Over S}
    (e : yoneda.obj U ≅ F) (d : yoneda.obj V ≅ H) (f : F ⟶ H) (p : Point F) :
    representedPoint d (mapPoint f p) =
      (yoneda.preimage (e.hom ≫ f ≫ d.inv)).left (representedPoint e p) := by
  rw [← representedPoint_leftInverse e p]
  change representedPoint d (schemePointMap (e.hom ≫ f) _) = _
  rw [representedPoint_schemePointMap, representedPoint_inverse, Category.assoc]

private theorem represented_isClosedMap {S : Scheme.{u}}
    {F H : (Over S)ᵒᵖ ⥤ Type u} {U V : Over S}
    (e : yoneda.obj U ≅ F) (d : yoneda.obj V ≅ H) (f : F ⟶ H)
    (hf : IsClosedMap (mapPoint f)) :
    IsClosedMap (yoneda.preimage (e.hom ≫ f ≫ d.inv)).left := by
  have h := (representedPointHomeomorph d).isClosedMap.comp
    (hf.comp (representedPointHomeomorph e).symm.isClosedMap)
  convert h using 1
  funext x
  change _ = representedPoint d (mapPoint f (schemePointMap e.hom x))
  rw [represented_mapPoint, representedPoint_inverse]

private theorem property_of_yoneda {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) [P.RespectsIso] {U V : Over S} (f : U ⟶ V)
    (hf : IsRepresentableWith P (yoneda.map f)) : P f := by
  obtain ⟨W, p, q, hq, hp⟩ := hf V (𝟙 _)
  have := hq.isIso_fst_of_isIso
  let q' := yoneda.preimage q
  have hq' : yoneda.map q' = q := yoneda.map_preimage q
  have : IsIso (yoneda.map q') := hq' ▸ inferInstance
  have : IsIso q' := isIso_of_reflects_iso q' yoneda
  have h : q' ≫ f = p := by
    apply yoneda.map_injective
    simpa [Functor.map_comp, hq'] using hq.w
  exact (P.cancel_left_of_respectsIso q' f).mp (h ▸ hp)

private def productRepresentation {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {U : Over S} (e : yoneda.obj U ≅ F) : yoneda.obj (U ⨯ U) ≅ F ⨯ F :=
  asIso (prodComparison yoneda U U) ≪≫ prod.mapIso e e

private theorem represented_separated {S : Scheme.{u}} (C : AlgebraicSpace S)
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj)
    (h : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 C.obj.obj) (𝟙 C.obj.obj))) : IsSeparated U.hom := by
  let P : MorphismProperty (Over S) :=
    MorphismProperty.inverseImage (@IsClosedImmersion) (Over.forget S)
  have hh := representableWith_of_iso P h e.symm (productRepresentation e).symm
  have heq : e.hom ≫ prod.lift (𝟙 _) (𝟙 _) ≫ (productRepresentation e).inv =
      yoneda.map (prod.lift (𝟙 U) (𝟙 U)) := by
    rw [← Category.assoc, Iso.comp_inv_eq]
    apply prod.hom_ext <;>
      simp only [productRepresentation, Iso.trans_hom, asIso_hom, Category.assoc,
        prod.mapIso_hom, prod.map_fst, prod.map_snd, prodComparison_fst_assoc,
        prodComparison_snd_assoc, ← Functor.map_comp_assoc, prod.lift_fst,
        prod.lift_snd, Category.comp_id] <;> simp
  change IsRepresentableWith P
    (e.hom ≫ prod.lift (𝟙 _) (𝟙 _) ≫ (productRepresentation e).inv) at hh
  rw [heq] at hh
  have hd := property_of_yoneda P (prod.lift (𝟙 U) (𝟙 U)) hh
  constructor
  let i := (Over.prodLeftIsoPullback U U).hom
  have hi : IsIso i := inferInstance
  have hc : IsClosedImmersion (prod.lift (𝟙 U) (𝟙 U)).left := hd
  have : IsClosedImmersion ((prod.lift (𝟙 U) (𝟙 U)).left ≫ i) := inferInstance
  convert this using 1
  apply Limits.pullback.hom_ext <;>
    simp only [Category.assoc, i, Over.prodLeftIsoPullback_hom_fst,
      Over.prodLeftIsoPullback_hom_snd, Limits.pullback.diagonal_fst,
      Limits.pullback.diagonal_snd, ← Over.comp_left, prod.lift_fst, prod.lift_snd,
      Over.id_left]

private theorem represented_locallyOfFiniteType {S : Scheme.{u}} (C : AlgebraicSpace S)
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj)
    (h : MapToSchemeIsLocally (@LocallyOfFiniteType) C (Over.mk (𝟙 S))
      (automorphismSchemeStructureMap C)) : LocallyOfFiniteType U.hom := by
  have hh := h U e.hom (iso_isEtale e)
  have heq : yoneda.preimage (e.hom ≫ automorphismSchemeStructureMap C) =
      Over.homMk U.hom (by simp) := by
    apply yoneda.map_injective
    rw [yoneda.map_preimage]
    exact structure_terminal.hom_ext _ _
  simpa [heq] using hh

private theorem represented_universallyClosed {S : Scheme.{u}} (C : AlgebraicSpace S)
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj)
    (h : MapToSchemeIsUniversallyClosed C (Over.mk (𝟙 S))
      (automorphismSchemeStructureMap C)) : UniversallyClosed U.hom := by
  constructor
  intro X' Y' i₁ i₂ f' H
  let V : Over S := Over.mk i₂
  let W : Over S := Over.mk (f' ≫ i₂)
  let j₁ : W ⟶ U := Over.homMk i₁ H.w.symm
  let j₂ : W ⟶ V := Over.homMk f' rfl
  let a : V ⟶ Over.mk (𝟙 S) := Over.homMk i₂ (by simp [V])
  let t : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom (by simp)
  have HO : IsPullback j₂ j₁ a t := by
    apply IsPullback.of_map_of_faithful (Over.forget S)
    exact H
  have HP : IsPullback (yoneda.map j₁ ≫ e.hom) (yoneda.map j₂)
      (automorphismSchemeStructureMap C) (yoneda.map a) :=
    (HO.flip.map yoneda).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by exact structure_terminal.hom_ext _ _) (by simp)
  let d : yoneda.obj W ≅ Limits.pullback (automorphismSchemeStructureMap C)
      (yoneda.map a) := HP.isoPullback
  have hc := represented_isClosedMap d (Iso.refl _) (Limits.pullback.snd
    (automorphismSchemeStructureMap C) (yoneda.map a)) (h V a)
  have heq : yoneda.preimage (d.hom ≫ Limits.pullback.snd
      (automorphismSchemeStructureMap C) (yoneda.map a) ≫ (Iso.refl _).inv) = j₂ := by
    apply yoneda.map_injective
    simp only [yoneda.map_preimage, Iso.refl_inv, Category.comp_id]
    exact HP.isoPullback_hom_snd
  rw [heq] at hc
  exact hc

private abbrev sliceObject {S : Scheme.{u}} (U T : Over S) : Over T :=
  Over.mk (Over.homMk (Limits.pullback.fst T.hom U.hom) rfl :
    Over.mk (Limits.pullback.fst T.hom U.hom ≫ T.hom) ⟶ T)

private def sliceRepresentation {S : Scheme.{u}} {C : AlgebraicSpace S}
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj) (T : Over S) :
    ((Over.forget T).op ⋙ C.obj.obj).RepresentableBy (sliceObject U T) where
  homEquiv {X} :=
    { toFun q := e.hom.app _ (Over.homMk
        (q.left.left ≫ Limits.pullback.snd T.hom U.hom) (by
          change q.left.left ≫ Limits.pullback.snd T.hom U.hom ≫ U.hom = X.left.hom
          rw [← Limits.pullback.condition, ← Category.assoc]
          have hq : q.left.left ≫ Limits.pullback.fst T.hom U.hom = X.hom.left :=
            congrArg Over.Hom.left q.w
          rw [hq]
          exact X.hom.w))
      invFun z := Over.homMk (Over.homMk
        (Limits.pullback.lift X.hom.left (e.inv.app _ z).left
          (X.hom.w.trans (e.inv.app _ z).w.symm)) (by simp [sliceObject]))
        (by ext1; simp [sliceObject])
      left_inv q := by
        apply Over.OverMorphism.ext
        apply Over.OverMorphism.ext
        apply Limits.pullback.hom_ext
        · simp only [Over.homMk_left, Limits.pullback.lift_fst]
          exact congrArg Over.Hom.left q.w.symm
        · simp only [Over.homMk_left, Limits.pullback.lift_snd]
          have h := ConcreteCategory.congr_hom (e.hom_inv_id_app (op X.left))
            (Over.homMk (q.left.left ≫ Limits.pullback.snd T.hom U.hom) (by
              rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc]
              have hq : q.left.left ≫ Limits.pullback.fst T.hom U.hom = X.hom.left :=
                congrArg Over.Hom.left q.w
              rw [hq]
              exact X.hom.w))
          exact congrArg Over.Hom.left h
      right_inv z := by
        change e.hom.app _ (Over.homMk
          (Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _) _) = z
        simp only [Limits.pullback.lift_snd]
        change e.hom.app _ (e.inv.app _ z) = z
        exact ConcreteCategory.congr_hom (e.inv_hom_id_app _) z }
  homEquiv_comp a q := by
    change e.hom.app _ _ = C.obj.obj.map a.left.op (e.hom.app _ _)
    rw [← NatTrans.naturality_apply]
    congr 1

private def sliceAutEquiv {S : Scheme.{u}} {C : AlgebraicSpace S}
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj) (T : Over S) :
    Aut (Over.mk (Limits.pullback.fst T.hom U.hom)) ≃* curveAutomorphisms C T :=
  ((Over.iteratedSliceEquiv T).fullyFaithfulInverse.autMulEquivOfFullyFaithful
    (Over.mk (Limits.pullback.fst T.hom U.hom))).trans
    ((Yoneda.fullyFaithful.autMulEquivOfFullyFaithful (sliceObject U T)).trans
      (Aut.autMulEquivOfIso (sliceRepresentation e T).toIso))

private theorem sliceAutEquiv_eval {S : Scheme.{u}} {C : AlgebraicSpace S}
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj) (T : Over S)
    (α : Aut (Over.mk (Limits.pullback.fst T.hom U.hom)))
    (W : Over T) (z : C.obj.obj.obj (op W.left)) :
    (e.inv.app _ ((sliceAutEquiv e T α).hom.app (op W) z)).left =
      Limits.pullback.lift W.hom.left (e.inv.app _ z).left
        (W.hom.w.trans (e.inv.app _ z).w.symm) ≫ α.hom.left ≫
          Limits.pullback.snd T.hom U.hom := by
  change (e.inv.app _ ((sliceRepresentation e T).homEquiv
    ((sliceRepresentation e T).homEquiv.symm z ≫
      (Over.iteratedSliceEquiv T).inverse.map α.hom))).left = _
  dsimp only [sliceRepresentation, Equiv.coe_fn_mk, Equiv.symm_mk]
  rw [← types_comp_apply, e.hom_inv_id_app]
  rfl

private theorem sliceAutEquiv_natural {S : Scheme.{u}} {C : AlgebraicSpace S}
    {U : Over S} (e : yoneda.obj U ≅ C.obj.obj) {T' T : Over S} (a : T' ⟶ T)
    (α : Aut (Over.mk (Limits.pullback.fst T.hom U.hom)))
    (β : Aut (Over.mk (Limits.pullback.fst T'.hom U.hom)))
    (h : ((Over.pullback U.hom).map a).left ≫ α.hom.left =
      β.hom.left ≫ ((Over.pullback U.hom).map a).left) :
    sliceAutEquiv e T' β = curveAutomorphismBaseChange C a (sliceAutEquiv e T α) := by
  apply Iso.ext
  ext ⟨W⟩ z
  apply (e.app _).toEquiv.symm.injective
  apply Over.OverMorphism.ext
  change (e.inv.app _ ((sliceAutEquiv e T' β).hom.app (op W) z)).left =
    (e.inv.app _ ((curveAutomorphismBaseChange C a (sliceAutEquiv e T α)).hom.app
      (op W) z)).left
  rw [sliceAutEquiv_eval]
  change _ = (e.inv.app _ ((sliceAutEquiv e T α).hom.app
    (op ((Over.map a).obj W)) z)).left
  rw [sliceAutEquiv_eval]
  let l : W.left.left ⟶ Limits.pullback T'.hom U.hom :=
    Limits.pullback.lift W.hom.left (e.inv.app _ z).left
      (W.hom.w.trans (e.inv.app _ z).w.symm)
  have hl : l ≫ ((Over.pullback U.hom).map a).left =
      Limits.pullback.lift (((Over.map a).obj W).hom.left) (e.inv.app _ z).left
        (((Over.map a).obj W).hom.w.trans (e.inv.app _ z).w.symm) := by
    apply Limits.pullback.hom_ext <;> simp [l, Category.assoc]
  change l ≫ β.hom.left ≫ Limits.pullback.snd T'.hom U.hom = _
  erw [← hl]
  calc
    l ≫ β.hom.left ≫ Limits.pullback.snd T'.hom U.hom =
        l ≫ β.hom.left ≫ ((Over.pullback U.hom).map a).left ≫
          Limits.pullback.snd T.hom U.hom := by simp
    _ = _ := by rw [← reassoc_of% h]; simp only [Category.assoc]

private def automorphismPresheaf {S : Scheme.{u}} (C : AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (curveAutomorphisms C T.unop)
  map a := GrpCat.ofHom
    { toFun := curveAutomorphismBaseChange C a.unop
      map_one' := by rfl
      map_mul' _ _ := by rfl }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro α
    apply Iso.ext
    ext U x
    rfl
  map_comp a b := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro α
    apply Iso.ext
    ext U x
    rfl

/-- The automorphism functor of a proper algebraic space of dimension at most one over
a field is a separated finite-type group scheme, compatibly with every test-scheme
base change and with group operations, including on nonreduced test schemes.

Source: Stacks Project, Tag 0DSQ specialized to `(C,C)`; Tag 001P
(blueprint: lem-sfb-proper-curve-automorphism-scheme).

Proof: by lem-sfb-separated-space-dimension-one-scheme (Tag 0ADD), separatedness, local
finite type and the dimension bound make the given space a scheme, retaining its
structure morphism and all fibre products. By lem-sc-proper-dim-one-projective (Tag
0A26), that proper scheme is projective, including the empty case. A field is
Noetherian (pqf-def-locnoeth), and every scheme over it is flat (lem-pc-flat-field).
Properness supplies quasi-compactness and separatedness; pqf-lem-lft-fp-locnoeth
supplies local finite presentation, and lem-pc-separated-quasi-separated supplies
quasi-separatedness. Thus the structure map is finitely presented. The field-extension
bound `topologicalKrullDim_pullback_le_of_field` in the proved source library bounds
every geometric fibre by one, without identifying the residue field with the base. Apply
lem-sfb-projective-curve-isom-graphs with both schemes equal to obtain a separated,
finitely presented scheme representing the automorphism functor on every test scheme.
It is in particular of finite type. Transfer identity, inversion and composition along
the representing bijections. Yoneda full faithfulness (lem-galois-yoneda-fully-faithful,
Tag 001P) makes them scheme morphisms and transfers all group diagrams from the
pointwise identities. The bijections are group isomorphisms. The naturality of Isom
graphs gives the asserted restriction equation for every map of test schemes.
-/
theorem exists_proper_curve_automorphism_scheme {K : Type u} [Field K]
    (C : AlgebraicSpace (Spec (.of K)))
    (hsep : MapToSchemeIsSeparated C (Over.mk (𝟙 (Spec (.of K))))
      (automorphismSchemeStructureMap C))
    (hqc : MapIsQuasiCompact (automorphismSchemeStructureMap C))
    (hlft : MapToSchemeIsLocally (@LocallyOfFiniteType) C
      (Over.mk (𝟙 (Spec (.of K)))) (automorphismSchemeStructureMap C))
    (hclosed : MapToSchemeIsUniversallyClosed C (Over.mk (𝟙 (Spec (.of K))))
      (automorphismSchemeStructureMap C))
    (hdim : topologicalKrullDim (Point C.obj.obj) ≤ 1) :
    ∃ G : Grp (Over (Spec (.of K))),
      IsSeparated G.X.hom ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧
      ∃ θ : ∀ T : Over (Spec (.of K)), (T ⟶ G.X) ≃* curveAutomorphisms C T,
        ∀ (T' T : Over (Spec (.of K))) (a : T' ⟶ T) (g : T ⟶ G.X),
          θ T' (a ≫ g) = curveAutomorphismBaseChange C a (θ T g) := by
  -- Universal closedness and separatedness already supply properness on the scheme.
  have _ := hqc
  have habs := separated_absolute C hsep
  have hlft' : ∀ (U : Over (Spec (.of K))) (a : yoneda.obj U ⟶ C.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom := by
    intro U a ha
    have hh := hlft U a ha
    have heq : yoneda.preimage (a ≫ automorphismSchemeStructureMap C) =
        Over.homMk U.hom (by simp) := by
      apply yoneda.map_injective
      rw [yoneda.map_preimage]
      exact structure_terminal.hom_ext _ _
    simpa [heq] using hh
  obtain ⟨U, ⟨e⟩⟩ := exists_scheme_of_separated_dim_le_one C habs hlft' hdim
  have : IsSeparated U.hom := represented_separated C e habs
  have : LocallyOfFiniteType U.hom := represented_locallyOfFiniteType C e hlft
  have : UniversallyClosed U.hom := represented_universallyClosed C e hclosed
  have : IsProper U.hom := ⟨⟩
  have hd : topologicalKrullDim U.left ≤ 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (representedPointHomeomorph e).isHomeomorph]
    exact hdim
  have : IsProjective U.hom := isProjective_of_isProper_of_dim_le_one U.hom
    (by simpa only [Scheme.dim_eq_topologicalKrullDim] using hd)
  have hf : ∀ s : Spec (.of K), topologicalKrullDim
      (Limits.pullback U.hom
        (Spec.map (CommRingCat.ofHom (algebraMap
          ((Spec (.of K)).residueField s) (AlgebraicClosure
            ((Spec (.of K)).residueField s)))) ≫
          (Spec (.of K)).fromSpecResidueField s) : Scheme.{u}) ≤ 1 := by
    intro s
    exact (topologicalKrullDim_pullback_le_of_field U.hom _).trans hd
  obtain ⟨J, hJsep, hJfp, hJqc, hJqs, b, hb, _⟩ :=
    exists_projective_curve_isom_graphs U.hom U.hom hf hf
  have hr : (automorphismPresheaf C ⋙ forget GrpCat).RepresentableBy J :=
    { homEquiv := fun {T} ↦ (b T).trans (sliceAutEquiv e T).toEquiv
      homEquiv_comp := by
        intro T' T a g
        exact sliceAutEquiv_natural e a (b T g) (b T' (a ≫ g)) (hb T' T a g) }
  let := GrpObj.ofRepresentableBy J (automorphismPresheaf C) hr
  have : LocallyOfFinitePresentation J.hom := hJfp
  refine ⟨⟨J⟩, hJsep, inferInstance, hJqc, ?_⟩
  refine ⟨fun T ↦ { toEquiv := hr.homEquiv, map_mul' := ?_ }, ?_⟩
  · intro g h
    change hr.homEquiv' (CartesianMonoidalCategory.lift g h ≫ hr.homEquiv'.symm
      (hr.homEquiv' (CartesianMonoidalCategory.fst J J) *
        hr.homEquiv' (CartesianMonoidalCategory.snd J J))) =
      hr.homEquiv' g * hr.homEquiv' h
    simp only [hr.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← hr.homEquiv'_comp]
    simp
  · intro T' T a g
    exact hr.homEquiv_comp a g

end AlgebraicGeometry.AlgebraicSpace
