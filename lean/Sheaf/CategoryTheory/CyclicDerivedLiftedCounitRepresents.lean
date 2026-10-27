module

public import Sheaf.CategoryTheory.CyclicDerivedHomExactSequence
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.CyclicDerivedActionRealization
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Representation by every lift of the cyclic derived counit

Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence,
expanded in the agent-written native-derived DAG argument.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents).

The auxiliary definitions only spell out the full subcategories, the two sequence
squares, and the specified maps on their outer terms. They retain the entire native
Hom groups; no faithfulness of derived forgetting is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uX vX wX zX uY vY wY zY

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra
namespace CyclicDerivedCounit

variable {A : Type uX} [Category.{vX} A] [Abelian A]
  (P : A ⥤ A) [P.Additive] [P.IsEquivalence]
  [HasDerivedCategory.{wX} A] [HasDerivedCategory.{zX} (IsoAlgebra P)]
  (S : ObjectProperty (DerivedCategory A))

/-- The native full subcategory W = Dᵇ(A^P) ∩ U⁻¹(C).
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
the item's full-subcategory setup.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
abbrev nativeProperty : ObjectProperty (DerivedCategory (IsoAlgebra P)) :=
  DerivedCategory.TStructure.t.bounded ⊓ S.inverseImage (forget P).mapDerivedCategory

/-- Forgetting restricted to the specified full subcategories, with its actual underlying maps.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
the item's full-subcategory setup.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
abbrev underlying : (nativeProperty P S).FullSubcategory ⥤ S.FullSubcategory :=
  S.lift ((nativeProperty P S).ι ⋙ (forget P).mapDerivedCategory) (fun K ↦ K.property.2)

/-- The restricted ordinary derived action, using precisely the given invariant full subcategory.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
the item's full-subcategory setup.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
abbrev action (hP : ∀ N, S N → S (P.mapDerivedCategory.obj N)) :
    S.FullSubcategory ⥤ S.FullSubcategory :=
  S.lift (S.ι ⋙ P.mapDerivedCategory) (fun N ↦ hP N.obj N.property)

/-- The restricted canonical derived structure isomorphism, rather than a new chosen action.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
the item's induced-action convention.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
def structureIso (hP : ∀ N, S N → S (P.mapDerivedCategory.obj N))
    (K : (nativeProperty P S).FullSubcategory) :
    (action P S hP).obj ((underlying P S).obj K) ≅ (underlying P S).obj K :=
  S.isoMk ((cyclicDerivedStructure P).app K.obj)

/-- Exactness on full subcategories means preservation of their ambient distinguished triangles.
This does not add closure under cones to the stipulated isomorphism and shift closure.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
the item's exact-functor hypothesis.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
def ExactOn {C : Type uX} [Category.{vX} C] [HasShift C ℤ]
    [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    {D : Type uY} [Category.{vY} D] [HasShift D ℤ]
    [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (R : ObjectProperty C) [R.IsStableUnderShift ℤ]
    (T : ObjectProperty D) [T.IsStableUnderShift ℤ]
    (J : R.FullSubcategory ⥤ T.FullSubcategory) [J.CommShift ℤ] : Prop :=
  ∀ Δ : Triangle R.FullSubcategory,
    R.ι.mapTriangle.obj Δ ∈ distTriang C → (J ⋙ T.ι).mapTriangle.obj Δ ∈ distTriang D

variable [S.IsClosedUnderIsomorphisms] [S.IsStableUnderShift ℤ]
  {B : Type uY} [Category.{vY} B] [Abelian B]
  (Q : B ⥤ B) [Q.Additive] [Q.IsEquivalence]
  [HasDerivedCategory.{wY} B] [HasDerivedCategory.{zY} (IsoAlgebra Q)]
  (T : ObjectProperty (DerivedCategory B))
  [T.IsClosedUnderIsomorphisms] [T.IsStableUnderShift ℤ]
  (F : S.FullSubcategory ⥤ T.FullSubcategory) [F.Additive] [F.CommShift ℤ]
  (J : (nativeProperty P S).FullSubcategory ⥤ (nativeProperty Q T).FullSubcategory)
  (c : J ⋙ underlying Q T ≅ underlying P S ⋙ F)

/-- The prescribed map on ordinary degree-r Hom groups under the forgetting comparison.
Every shift of a full subcategory is identified with the ambient shift by its canonical inclusion.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
item proof Step 6, before postcomposition with the lifted counit.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
def transport (K H : (nativeProperty P S).FullSubcategory) (r : ℤ)
    (u : CyclicDerivedHom P K.obj H.obj r) :
    CyclicDerivedHom Q (J.obj K).obj (J.obj H).obj r :=
  T.ι.map (c.hom.app K) ≫
    T.ι.map (F.map (ObjectProperty.homMk
      (u ≫ (S.ι.commShiftIso r).inv.app ((underlying P S).obj H)))) ≫
    ((F ⋙ T.ι).commShiftIso r).hom.app ((underlying P S).obj H) ≫
    (T.ι.map (c.inv.app H))⟦r⟧'

/-- Compatibility with the entire normalized Hom sequence on the full subcategories.
It includes the action, forgetting, and left connecting-map squares, on every representative.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
the item's explicit sequence-compatibility assumption and proof Step 6.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
def Compatible (bX : CyclicDerivedHomBoundary P) (bY : CyclicDerivedHomBoundary Q) : Prop :=
  ∀ K H : (nativeProperty P S).FullSubcategory,
    (∀ (r : ℤ) (u : CyclicDerivedHom P K.obj H.obj r),
      transport P S Q T F J c K H r (cyclicDerivedHomAction P K.obj H.obj r u) =
        cyclicDerivedHomAction Q (J.obj K).obj (J.obj H).obj r
          (transport P S Q T F J c K H r u)) ∧
    (∀ f : K ⟶ H,
      transport P S Q T F J c K H 0 (cyclicDerivedForget P K.obj H.obj f.hom) =
        cyclicDerivedForget Q (J.obj K).obj (J.obj H).obj (J.map f).hom) ∧
    (∀ u : CyclicDerivedHom P K.obj H.obj (-1),
      (J.map (ObjectProperty.homMk
        (bX K.obj H.obj K.property.1 H.property.1 (QuotientAddGroup.mk u)))).hom =
      bY (J.obj K).obj (J.obj H).obj (J.obj K).property.1 (J.obj H).property.1
        (QuotientAddGroup.mk (transport P S Q T F J c K H (-1) u)))

/-- The ordinary adjunction comparison φ_r after identifying U(H) with G(U(L)).
Its formula is c_K followed by F(u), the shift comparison, and the shifted ordinary counit.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
item proof Steps 4--6.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
def outerMap (G : T.FullSubcategory ⥤ S.FullSubcategory) (adj : F ⊣ G)
    (L : (nativeProperty Q T).FullSubcategory) (H : (nativeProperty P S).FullSubcategory)
    (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L))
    (K : (nativeProperty P S).FullSubcategory) (r : ℤ)
    (u : CyclicDerivedHom P K.obj H.obj r) :
    CyclicDerivedHom Q (J.obj K).obj L.obj r :=
  T.ι.map (c.hom.app K) ≫
    T.ι.map (F.map (ObjectProperty.homMk
      (u ≫ (S.ι.commShiftIso r).inv.app ((underlying P S).obj H)))) ≫
    ((F ⋙ T.ι).commShiftIso r).hom.app ((underlying P S).obj H) ≫
    (T.ι.map (F.map e.hom ≫ adj.counit.app ((underlying Q T).obj L)))⟦r⟧'

/-- Representation of the full native Hom functor, with its specified two outer bijections.
The quotient formula fixes the degree-minus-one map on every representative; the invariant
formula fixes the degree-zero map on every element. The last two equations are the sequence
squares and naturality on all native morphisms, including extension morphisms.
Source: blueprint latest, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
item proof Steps 4--8.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
def Represents (G : T.FullSubcategory ⥤ S.FullSubcategory) (adj : F ⊣ G)
    (bX : CyclicDerivedHomBoundary P) (bY : CyclicDerivedHomBoundary Q)
    (L : (nativeProperty Q T).FullSubcategory) (H : (nativeProperty P S).FullSubcategory)
    (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L)) (d : J.obj H ⟶ L) : Prop :=
  (∀ K : (nativeProperty P S).FullSubcategory,
    Function.Bijective (fun u : K ⟶ H ↦ J.map u ≫ d) ∧
    ∃ (pMinus : CyclicDerivedHomCoinvariants P K.obj H.obj ≃+
        CyclicDerivedHomCoinvariants Q (J.obj K).obj L.obj)
      (pZero : CyclicDerivedHomInvariants P K.obj H.obj ≃+
        CyclicDerivedHomInvariants Q (J.obj K).obj L.obj),
      (∀ u : CyclicDerivedHom P K.obj H.obj (-1),
        pMinus (QuotientAddGroup.mk u) =
          QuotientAddGroup.mk (outerMap P S Q T F J c G adj L H e K (-1) u)) ∧
      (∀ u : CyclicDerivedHomInvariants P K.obj H.obj,
        (pZero u).val = outerMap P S Q T F J c G adj L H e K 0 u.val) ∧
      (∀ u : CyclicDerivedHomCoinvariants P K.obj H.obj,
        (J.map (ObjectProperty.homMk
          (bX K.obj H.obj K.property.1 H.property.1 u)) ≫ d).hom =
        bY (J.obj K).obj L.obj (J.obj K).property.1 L.property.1 (pMinus u)) ∧
      (∀ u : K ⟶ H,
        outerMap P S Q T F J c G adj L H e K 0
          (cyclicDerivedForget P K.obj H.obj u.hom) =
        cyclicDerivedForget Q (J.obj K).obj L.obj (J.map u ≫ d).hom)) ∧
  (∀ (K K' : (nativeProperty P S).FullSubcategory) (z : K' ⟶ K) (u : K ⟶ H),
    J.map (z ≫ u) ≫ d = J.map z ≫ (J.map u ≫ d))

private theorem homMk_add {C : Type*} [Category* C] [Preadditive C]
    {R : ObjectProperty C} {X Y : R.FullSubcategory} (f g : X.obj ⟶ Y.obj) :
    ObjectProperty.homMk (f + g) =
      (ObjectProperty.homMk f : X ⟶ Y) + ObjectProperty.homMk g := rfl

private theorem hom_add {C : Type*} [Category* C] [Preadditive C]
    {R : ObjectProperty C} {X Y : R.FullSubcategory} (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom := rfl

-- An equivariant additive equivalence identifies both outer terms of the Hom sequence.
private theorem kernel_quotient_equivs
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (t : V →+ V) (t' : W →+ W) (e : V ≃+ W)
    (he : ∀ x, e (t x) = t' (e x)) :
    (∃ k : (AddMonoidHom.id V - t).ker ≃+ (AddMonoidHom.id W - t').ker,
      ∀ x, (k x).val = e x.val) ∧
    (∃ q : V ⧸ (AddMonoidHom.id V - t).range ≃+
        W ⧸ (AddMonoidHom.id W - t').range,
      ∀ x, q (QuotientAddGroup.mk x) = QuotientAddGroup.mk (e x)) := by
  have hk (x : V) : x ∈ (AddMonoidHom.id V - t).ker ↔
      e x ∈ (AddMonoidHom.id W - t').ker := by
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      sub_eq_zero]
    rw [← he]
    exact e.injective.eq_iff.symm
  constructor
  · refine ⟨{ toFun := fun x ↦ ⟨e x, (hk x).mp x.property⟩
              invFun := fun x ↦ ⟨e.symm x, (hk (e.symm x)).mpr (by simp)⟩
              left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
              right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
              map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }, fun _ ↦ rfl⟩
  · have hr : (AddMonoidHom.id V - t).range.map e.toAddMonoidHom =
        (AddMonoidHom.id W - t').range := by
      ext y
      constructor
      · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
        exact ⟨e z, by simp [← he]⟩
      · rintro ⟨z, rfl⟩
        refine ⟨(AddMonoidHom.id V - t) (e.symm z), ⟨e.symm z, rfl⟩, ?_⟩
        simp [he]
    exact ⟨QuotientAddGroup.congr _ _ e hr, fun _ ↦ rfl⟩

-- The short five lemma as an element chase, with independent universes for the groups.
private theorem short_five_bijective
    {V M Z V' M' Z' : Type*}
    [AddCommGroup V] [AddCommGroup M] [AddCommGroup Z]
    [AddCommGroup V'] [AddCommGroup M'] [AddCommGroup Z']
    (i : V →+ M) (q : M →+ Z) (i' : V' →+ M') (q' : M' →+ Z')
    (hi' : Function.Injective i') (h : Function.Exact i q)
    (h' : Function.Exact i' q') (hq : Function.Surjective q)
    (a : V ≃+ V') (b : M →+ M') (c : Z ≃+ Z')
    (hl : ∀ v, b (i v) = i' (a v)) (hr : ∀ m, q' (b m) = c (q m)) :
    Function.Bijective b := by
  constructor
  · apply (injective_iff_map_eq_zero b).mpr
    intro m hm
    have hqm : q m = 0 := c.injective (by simpa [hm] using (hr m).symm)
    obtain ⟨v, rfl⟩ := (h m).mp hqm
    have hv : a v = 0 := hi' (by simpa [hl] using hm)
    have : v = 0 := a.injective (by simpa using hv)
    simp [this]
  · intro m'
    obtain ⟨m, hm⟩ := hq (c.symm (q' m'))
    have hz : q' (m' - b m) = 0 := by simp [hr, hm]
    obtain ⟨v', hv'⟩ := (h' _).mp hz
    refine ⟨m + i (a.symm v'), ?_⟩
    rw [map_add, hl, a.apply_symm_apply, hv']
    abel

private theorem shiftedCounit_bijective
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (V : C ⥤ D) [V.CommShift ℤ] (W : D ⥤ C) (ad : V ⊣ W)
    (X Y : C) (Z : D) (e : Y ≅ W.obj Z) (r : ℤ) :
    Function.Bijective (fun u : X ⟶ Y⟦r⟧ ↦
      V.map u ≫ (V.commShiftIso r).hom.app Y ≫
        (V.map e.hom ≫ ad.counit.app Z)⟦r⟧') := by
  -- Use the shift structure determined by this adjunction, independently of any given one.
  let := ad.rightAdjointCommShift ℤ
  have := ad.commShift_of_leftAdjoint ℤ
  let i : Y⟦r⟧ ≅ W.obj (Z⟦r⟧) :=
    (shiftFunctor C r).mapIso e ≪≫ (W.commShiftIso r).symm.app Z
  have hh : Function.Bijective (fun u : X ⟶ Y⟦r⟧ ↦
      (ad.homEquiv X (Z⟦r⟧)).symm (u ≫ i.hom)) :=
    (ad.homEquiv X (Z⟦r⟧)).symm.bijective.comp
      (by
        constructor
        · intro u v h
          exact (cancel_mono i.hom).1 h
        · intro u
          exact ⟨u ≫ i.inv, by simp⟩)
  suffices heq : (fun u : X ⟶ Y⟦r⟧ ↦
      V.map u ≫ (V.commShiftIso r).hom.app Y ≫
        (V.map e.hom ≫ ad.counit.app Z)⟦r⟧') =
      (fun u : X ⟶ Y⟦r⟧ ↦ (ad.homEquiv X (Z⟦r⟧)).symm (u ≫ i.hom)) by
    rw [heq]
    exact hh
  funext u
  simp only [Adjunction.homEquiv_counit, i, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [ad.shift_counit_app r Z]
  rw [← V.commShiftIso_hom_naturality_assoc]
  simp

omit [S.IsClosedUnderIsomorphisms] [T.IsClosedUnderIsomorphisms] [F.Additive] in
private theorem outerMap_bijective
    (G : T.FullSubcategory ⥤ S.FullSubcategory) (adj : F ⊣ G)
    (L : (nativeProperty Q T).FullSubcategory) (H : (nativeProperty P S).FullSubcategory)
    (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L))
    (K : (nativeProperty P S).FullSubcategory) (r : ℤ) :
    Function.Bijective (outerMap P S Q T F J c G adj L H e K r) := by
  let x := (underlying P S).obj K
  let y := (underlying P S).obj H
  let z := (underlying Q T).obj L
  let s : (x ⟶ y⟦r⟧) ≃ CyclicDerivedHom P K.obj H.obj r :=
    S.fullyFaithfulι.homEquiv.trans
      (Iso.homCongr (Iso.refl _) ((S.ι.commShiftIso r).app y))
  let t : (F.obj x ⟶ z⟦r⟧) ≃ CyclicDerivedHom Q (J.obj K).obj L.obj r :=
    T.fullyFaithfulι.homEquiv.trans
      (Iso.homCongr ((T.ι.mapIso (c.app K)).symm)
        ((T.ι.commShiftIso r).app z))
  have hh := (t.bijective.comp
    (shiftedCounit_bijective F G adj x y z e r)).comp s.symm.bijective
  convert hh using 1
  funext u
  simp only [outerMap, Equiv.trans_apply, Function.comp_apply, s, t,
    Iso.homCongr_apply,
    Functor.FullyFaithful.homEquiv_apply]
  have hs : s.symm u = ObjectProperty.homMk
      (u ≫ (S.ι.commShiftIso r).inv.app y) := by
    apply s.symm_apply_eq.mpr
    symm
    simp only [s, Equiv.trans_apply, Iso.homCongr_apply,
      Functor.FullyFaithful.homEquiv_apply, Iso.refl_inv]
    change 𝟙 _ ≫ (u ≫ (S.ι.commShiftIso r).inv.app y) ≫
      (S.ι.commShiftIso r).hom.app y = u
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
    exact Category.comp_id _
  change _ = (T.ι.mapIso (c.app K)).symm.inv ≫
    T.ι.map (F.map (s.symm u) ≫ (F.commShiftIso r).hom.app y ≫
      (F.map e.hom ≫ adj.counit.app z)⟦r⟧') ≫ (T.ι.commShiftIso r).hom.app z
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  erw [T.ι.commShiftIso_hom_naturality (adj.counit.app z) r]
  erw [T.ι.commShiftIso_hom_naturality_assoc (F.map e.hom) r]
  simp [Functor.commShiftIso_comp_hom_app, x, y, z, Category.assoc]


private theorem action_postcomp
    (M N N' : DerivedCategory (IsoAlgebra Q)) (d : N ⟶ N') (r : ℤ)
    (u : CyclicDerivedHom Q M N r) :
    cyclicDerivedHomAction Q M N' r
        (u ≫ ((forget Q).mapDerivedCategory.map d)⟦r⟧') =
      cyclicDerivedHomAction Q M N r u ≫
        ((forget Q).mapDerivedCategory.map d)⟦r⟧' := by
  set_option backward.isDefEq.respectTransparency false in
  change (((cyclicDerivedStructure Q).inv.app M ≫
      Q.mapDerivedCategory.map (u ≫ ((forget Q).mapDerivedCategory.map d)⟦r⟧')) ≫
        ((Q.mapDerivedCategory.commShiftIso r).hom.app _ ≫
          ((cyclicDerivedStructure Q).hom.app N')⟦r⟧')) =
    (((cyclicDerivedStructure Q).inv.app M ≫ Q.mapDerivedCategory.map u) ≫
      ((Q.mapDerivedCategory.commShiftIso r).hom.app _ ≫
        ((cyclicDerivedStructure Q).hom.app N)⟦r⟧')) ≫
          ((forget Q).mapDerivedCategory.map d)⟦r⟧'
  simp only [Functor.map_comp, Category.assoc]
  rw [Q.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp]
  have hn := (cyclicDerivedStructure Q).hom.naturality d
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp

omit [S.IsClosedUnderIsomorphisms] [T.IsClosedUnderIsomorphisms] [F.Additive] in
private theorem outerMap_postcomp
    (G : T.FullSubcategory ⥤ S.FullSubcategory) (adj : F ⊣ G)
    (L : (nativeProperty Q T).FullSubcategory) (H : (nativeProperty P S).FullSubcategory)
    (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L))
    (d : J.obj H ⟶ L)
    (hd : (underlying Q T).map d =
      c.hom.app H ≫ F.map e.hom ≫ adj.counit.app ((underlying Q T).obj L))
    (K : (nativeProperty P S).FullSubcategory) (r : ℤ)
    (u : CyclicDerivedHom P K.obj H.obj r) :
    transport P S Q T F J c K H r u ≫
        ((forget Q).mapDerivedCategory.map d.hom)⟦r⟧' =
      outerMap P S Q T F J c G adj L H e K r u := by
  have hd' := congrArg (fun f ↦ T.ι.map f) hd
  change (forget Q).mapDerivedCategory.map d.hom = _ at hd'
  simp only [transport, outerMap, hd', Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp]
  simp

private theorem forget_postcomp
    (M N N' : DerivedCategory (IsoAlgebra Q)) (f : M ⟶ N) (d : N ⟶ N') :
    cyclicDerivedForget Q M N f ≫ ((forget Q).mapDerivedCategory.map d)⟦(0 : ℤ)⟧' =
      cyclicDerivedForget Q M N' (f ≫ d) := by
  set_option backward.isDefEq.respectTransparency false in
  change ((forget Q).mapDerivedCategory.map f ≫
      (shiftFunctorZero (DerivedCategory B) ℤ).inv.app _) ≫ _ = _
  change (_ ≫ _) ≫ _ = (forget Q).mapDerivedCategory.map (f ≫ d) ≫ _
  rw [Functor.map_comp, Category.assoc]
  simpa only [Functor.id_map, Category.assoc] using
    congrArg (fun k ↦ (forget Q).mapDerivedCategory.map f ≫ k)
    (((shiftFunctorZero (DerivedCategory B) ℤ).inv.naturality
      ((forget Q).mapDerivedCategory.map d)).symm)


omit [S.IsClosedUnderIsomorphisms] [T.IsClosedUnderIsomorphisms] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem represents_from_lift [J.Additive]
    (G : T.FullSubcategory ⥤ S.FullSubcategory) (adj : F ⊣ G)
    (bX : CyclicDerivedHomBoundary P) (bY : CyclicDerivedHomBoundary Q)
    (hbX : CyclicDerivedHomBoundaryExact P bX)
    (hbY : CyclicDerivedHomBoundaryExact Q bY)
    (hbYn : CyclicDerivedHomBoundaryNatural Q bY)
    (hcompat : Compatible P S Q T F J c bX bY)
    (L : (nativeProperty Q T).FullSubcategory) (H : (nativeProperty P S).FullSubcategory)
    (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L))
    (d : J.obj H ⟶ L)
    (hd : (underlying Q T).map d =
      c.hom.app H ≫ F.map e.hom ≫ adj.counit.app ((underlying Q T).obj L)) :
    Represents P S Q T F J c G adj bX bY L H e d := by
  unfold Represents
  dsimp only [CyclicDerivedHomBoundaryExact, CyclicDerivedHomInvariants,
    CyclicDerivedHomCoinvariants, cyclicDerivedHomDefect] at hbX hbY ⊢
  constructor
  · intro K
    let phi (r : ℤ) : CyclicDerivedHom P K.obj H.obj r →+
        CyclicDerivedHom Q (J.obj K).obj L.obj r :=
      AddMonoidHom.mk' (outerMap P S Q T F J c G adj L H e K r) (by
        intro u v
        simp only [outerMap, Preadditive.add_comp, homMk_add, Functor.map_add,
          Preadditive.comp_add])
    let pe (r : ℤ) := AddEquiv.ofBijective (phi r)
      (outerMap_bijective P S Q T F J c G adj L H e K r)
    have hp (r : ℤ) (u : CyclicDerivedHom P K.obj H.obj r) :
        pe r (cyclicDerivedHomAction P K.obj H.obj r u) =
          cyclicDerivedHomAction Q (J.obj K).obj L.obj r (pe r u) := by
      change outerMap P S Q T F J c G adj L H e K r _ =
        cyclicDerivedHomAction Q (J.obj K).obj L.obj r
          (outerMap P S Q T F J c G adj L H e K r u)
      rw [← outerMap_postcomp P S Q T F J c G adj L H e d hd,
        ← outerMap_postcomp P S Q T F J c G adj L H e d hd,
        action_postcomp, (hcompat K H).1]
    obtain ⟨⟨pZero, hpZero⟩, _⟩ := kernel_quotient_equivs
      (cyclicDerivedHomAction P K.obj H.obj 0)
      (cyclicDerivedHomAction Q (J.obj K).obj L.obj 0) (pe 0) (hp 0)
    obtain ⟨_, pMinus, hpMinus⟩ := kernel_quotient_equivs
      (cyclicDerivedHomAction P K.obj H.obj (-1))
      (cyclicDerivedHomAction Q (J.obj K).obj L.obj (-1)) (pe (-1)) (hp (-1))
    change ∀ u, pMinus (QuotientAddGroup.mk u) = QuotientAddGroup.mk
      (outerMap P S Q T F J c G adj L H e K (-1) u) at hpMinus
    change ∀ u, (pZero u).val =
      outerMap P S Q T F J c G adj L H e K 0 u.val at hpZero
    have hleft (u : CyclicDerivedHomCoinvariants P K.obj H.obj) :
        (J.map (ObjectProperty.homMk
          (bX K.obj H.obj K.property.1 H.property.1 u)) ≫ d).hom =
        bY (J.obj K).obj L.obj (J.obj K).property.1 L.property.1 (pMinus u) := by
      induction u using QuotientAddGroup.induction_on with
      | H u =>
        change (J.map (ObjectProperty.homMk
          (bX K.obj H.obj K.property.1 H.property.1 (QuotientAddGroup.mk u)))).hom ≫
            d.hom = _
        rw [(hcompat K H).2.2, hpMinus]
        have hn := hbYn (J.obj K).obj (J.obj H).obj (J.obj K).obj L.obj
          (J.obj K).property.1 (J.obj H).property.1 (J.obj K).property.1 L.property.1
          (𝟙 _) d.hom (transport P S Q T F J c K H (-1) u)
        simp only [Category.id_comp, Functor.map_id,
          outerMap_postcomp P S Q T F J c G adj L H e d hd] at hn
        exact hn
    have hright (u : K ⟶ H) :
        outerMap P S Q T F J c G adj L H e K 0
          (cyclicDerivedForget P K.obj H.obj u.hom) =
        cyclicDerivedForget Q (J.obj K).obj L.obj (J.map u ≫ d).hom := by
      rw [← outerMap_postcomp P S Q T F J c G adj L H e d hd,
        (hcompat K H).2.1, forget_postcomp]
      rfl
    obtain ⟨qx, hqx, _, hex, hqxsurj⟩ := hbX K.obj H.obj K.property.1 H.property.1
    obtain ⟨qy, hqy, hiy, hey, _⟩ :=
      hbY (J.obj K).obj L.obj (J.obj K).property.1 L.property.1
    let mid : (K.obj ⟶ H.obj) →+ ((J.obj K).obj ⟶ L.obj) :=
      AddMonoidHom.mk' (fun u ↦ (J.map (ObjectProperty.homMk u)).hom ≫ d.hom) (by
        intro u v
        simp only [homMk_add, Functor.map_add, hom_add, Preadditive.add_comp])
    have hmid := short_five_bijective
      (bX K.obj H.obj K.property.1 H.property.1) qx
      (bY (J.obj K).obj L.obj (J.obj K).property.1 L.property.1) qy
      hiy hex hey hqxsurj pMinus mid pZero hleft (by
        intro u
        apply Subtype.ext
        calc
          _ = cyclicDerivedForget Q (J.obj K).obj L.obj (mid u) := hqy _
          _ = outerMap P S Q T F J c G adj L H e K 0
              (cyclicDerivedForget P K.obj H.obj u) :=
            (hright (ObjectProperty.homMk u)).symm
          _ = _ := by
            have hz := hpZero (qx u)
            rw [hqx] at hz
            exact hz.symm)
    refine ⟨?_, pMinus, pZero, hpMinus, hpZero, hleft, hright⟩
    constructor
    · intro u v huv
      apply ObjectProperty.hom_ext
      exact hmid.1 (congrArg (fun f ↦ f.hom) huv)
    · intro v
      obtain ⟨u, hu⟩ := hmid.2 v.hom
      exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩
  · intro K K' z u
    simp [J.map_comp, Category.assoc]

omit [S.IsStableUnderShift ℤ] [T.IsClosedUnderIsomorphisms] [T.IsStableUnderShift ℤ] in
private theorem realize_right_action
    [IsGrothendieckAbelian.{vX} A]
    (hS : ∀ N, S N → DerivedCategory.TStructure.t.bounded N)
    (hP : ∀ N, S N → S (P.mapDerivedCategory.obj N))
    (hQ : ∀ N, T N → T (Q.mapDerivedCategory.obj N))
    (G : T.FullSubcategory ⥤ S.FullSubcategory)
    (b : G ⋙ action P S hP ≅ action Q T hQ ⋙ G)
    (L : (nativeProperty Q T).FullSubcategory) :
    ∃ (H : (nativeProperty P S).FullSubcategory)
      (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L)),
      (structureIso P S hP H).hom ≫ e.hom =
        (action P S hP).map e.hom ≫ b.hom.app ((underlying Q T).obj L) ≫
          G.map (structureIso Q T hQ L).hom := by
  let N := G.obj ((underlying Q T).obj L)
  let v : (action P S hP).obj N ≅ N :=
    b.app ((underlying Q T).obj L) ≪≫ G.mapIso (structureIso Q T hQ L)
  obtain ⟨M, e, he, hinterval, _⟩ := exists_cyclicDerivedActionRealization P N.obj
    (hS N.obj N.property) (S.ι.mapIso v)
  have hM : DerivedCategory.TStructure.t.bounded M := by
    obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hS N.obj N.property
    have hlo' := (DerivedCategory.isGE_iff N.obj lo).mp hlo
    have hhi' := (DerivedCategory.isLE_iff N.obj hi).mp hhi
    have hvan := hinterval lo hi (fun i h ↦ h.elim (hlo' i) (hhi' i))
    exact ⟨⟨lo, (DerivedCategory.isGE_iff M lo).mpr (fun i h ↦ hvan i (Or.inl h))⟩,
      ⟨hi, (DerivedCategory.isLE_iff M hi).mpr (fun i h ↦ hvan i (Or.inr h))⟩⟩
  let H : (nativeProperty P S).FullSubcategory :=
    ⟨M, hM, S.prop_of_iso e.symm N.property⟩
  refine ⟨H, S.isoMk e, ?_⟩
  apply ObjectProperty.hom_ext
  exact he

private theorem counit_equivariant
    {C D : Type*} [Category* C] [Category* D]
    (U : C ⥤ C) (V : D ⥤ D) (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (a : F ⋙ V ≅ U ⋙ F) (b : G ⋙ U ≅ V ⋙ G)
    (hb : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans = b.hom)
    (X : C) (Y : D) (sigma : U.obj X ≅ X) (tau : V.obj Y ≅ Y)
    (e : X ≅ G.obj Y)
    (he : sigma.hom ≫ e.hom =
      U.map e.hom ≫ b.hom.app Y ≫ G.map tau.hom) :
    a.hom.app X ≫ F.map sigma.hom ≫ F.map e.hom ≫ adj.counit.app Y =
      V.map (F.map e.hom ≫ adj.counit.app Y) ≫ tau.hom := by
  have hc := mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ a.inv) Y
  rw [NatTrans.congr_app hb] at hc
  change F.map (b.hom.app Y) ≫ adj.counit.app (V.obj Y) =
    a.inv.app (G.obj Y) ≫ V.map (adj.counit.app Y) at hc
  calc
    _ = a.hom.app X ≫ F.map (sigma.hom ≫ e.hom) ≫ adj.counit.app Y := by
      simp [Functor.map_comp, Category.assoc]
    _ = a.hom.app X ≫ F.map (U.map e.hom) ≫ F.map (b.hom.app Y) ≫
        F.map (G.map tau.hom) ≫ adj.counit.app Y := by
      rw [he]; simp [Functor.map_comp, Category.assoc]
    _ = V.map (F.map e.hom) ≫ a.hom.app (G.obj Y) ≫ F.map (b.hom.app Y) ≫
        adj.counit.app (V.obj Y) ≫ tau.hom := by
      rw [← adj.counit_naturality tau.hom]
      erw [← a.hom.naturality_assoc e.hom]
      rfl
    _ = _ := by
      rw [reassoc_of% hc]
      simp [Functor.map_comp, Category.assoc]

private theorem degreeZero_invariant
    (M N : DerivedCategory (IsoAlgebra Q))
    (t : (forget Q).mapDerivedCategory.obj M ⟶ (forget Q).mapDerivedCategory.obj N)
    (ht : (cyclicDerivedStructure Q).hom.app M ≫ t =
      Q.mapDerivedCategory.map t ≫ (cyclicDerivedStructure Q).hom.app N) :
    t ≫ (shiftFunctorZero (DerivedCategory B) ℤ).inv.app _ ∈
      CyclicDerivedHomInvariants Q M N := by
  rw [AddMonoidHom.mem_ker]
  change _ - cyclicDerivedHomAction Q M N 0 _ = 0
  rw [sub_eq_zero]
  set_option backward.isDefEq.respectTransparency false in
  change _ = (((cyclicDerivedStructure Q).inv.app M ≫
    Q.mapDerivedCategory.map (t ≫ (shiftFunctorZero (DerivedCategory B) ℤ).inv.app _)) ≫
    ((Q.mapDerivedCategory.commShiftIso 0).hom.app _ ≫
      ((cyclicDerivedStructure Q).hom.app N)⟦(0 : ℤ)⟧'))
  rw [Q.mapDerivedCategory.commShiftIso_zero]
  simp only [AddMonoidHom.id_apply, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Category.comp_id, Functor.id_obj]
  erw [← (shiftFunctorZero (DerivedCategory B) ℤ).inv.naturality
    ((cyclicDerivedStructure Q).hom.app N)]
  simp only [Functor.id_map]
  rw [← reassoc_of% ht]
  simp

end CyclicDerivedCounit

open CyclicDerivedCounit

/-- Every lift of the cyclic derived counit represents the full native Hom functor.

Proof, following the agent-written expansion of the blueprint's final sentence:
1. Apply cyclic action realization to G(U(L)) with action b followed by G(θ_L).
   Its interval assertion supplies native boundedness, and isomorphism closure gives H in W_X.
2. The mate/counit identity and naturality of a show that F(e) followed by the counit
   intertwines actions. Compose with c_H and use hc. The degree-zero shift identity
   puts this map in the invariant subgroup. Surjectivity of the given Hom sequence
   supplies a native lift d, without choosing any new functor.
3. In every degree, outerMap is an additive bijection. For its set bijection use
   Mathlib's compatible shift structure on the right adjoint, constructed from F's
   shift structure; the given shift structure on G is unnecessary. Its shifted counit
   identity and naturality recover exactly the displayed outerMap formula.
4. For any native lift d, transport followed by shifted U(d) equals outerMap: the
   shifted c_H inverse cancels. Compatible and naturality of the canonical derived
   structure therefore show that outerMap intertwines the cyclic actions.
5. Restrict the degree-zero additive equivalence to ker(1-T), and use its identification
   of the ranges of 1-T to induce the degree-minus-one quotient equivalence.
6. Compatible and boundary naturality give the left sequence square on quotient
   representatives; Compatible and forgetting naturality give the right square.
   A direct additive short-five-lemma diagram chase proves the native middle map
   bijective. All native morphisms are retained throughout.
7. J.map_comp and associativity give naturality in K. The argument for representation
   uses only the underlying counit equation, and hence applies to every native lift.

Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
agent-written native-derived argument in the DAG, Steps 1--8.
(blueprint: lem-sf-cyclic-derived-lifted-counit-represents). -/
theorem cyclicDerived_liftedCounit_represents
    {A : Type uX} [Category.{vX} A] [Abelian A] [IsGrothendieckAbelian.{vX} A]
    (P : A ⥤ A) [P.Additive] [P.IsEquivalence]
    [HasDerivedCategory.{wX} A] [HasDerivedCategory.{zX} (IsoAlgebra P)]
    {B : Type uY} [Category.{vY} B] [Abelian B] [IsGrothendieckAbelian.{vY} B]
    (Q : B ⥤ B) [Q.Additive] [Q.IsEquivalence]
    [HasDerivedCategory.{wY} B] [HasDerivedCategory.{zY} (IsoAlgebra Q)]
    (S : ObjectProperty (DerivedCategory A))
    [S.IsClosedUnderIsomorphisms] [S.IsStableUnderShift ℤ]
    (hS : ∀ N, S N → DerivedCategory.TStructure.t.bounded N)
    (hP : ∀ N, S N → S (P.mapDerivedCategory.obj N))
    (hPinv : ∀ N, S (P.mapDerivedCategory.obj N) → S N)
    (T : ObjectProperty (DerivedCategory B))
    [T.IsClosedUnderIsomorphisms] [T.IsStableUnderShift ℤ]
    (hT : ∀ N, T N → DerivedCategory.TStructure.t.bounded N)
    (hQ : ∀ N, T N → T (Q.mapDerivedCategory.obj N))
    (hQinv : ∀ N, T (Q.mapDerivedCategory.obj N) → T N)
    (F : S.FullSubcategory ⥤ T.FullSubcategory) [F.Additive] [F.CommShift ℤ]
    (hF : ExactOn S T F)
    (G : T.FullSubcategory ⥤ S.FullSubcategory) [G.Additive] [G.CommShift ℤ]
    (hG : ExactOn T S G) (adj : F ⊣ G)
    (a : F ⋙ action Q T hQ ≅ action P S hP ⋙ F)
    [NatTrans.CommShift a.hom ℤ]
    (b : G ⋙ action P S hP ≅ action Q T hQ ⋙ G)
    (hb : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans = b.hom)
    (J : (nativeProperty P S).FullSubcategory ⥤ (nativeProperty Q T).FullSubcategory)
    [J.Additive] [J.CommShift ℤ] (hJ : ExactOn (nativeProperty P S) (nativeProperty Q T) J)
    (c : J ⋙ underlying Q T ≅ underlying P S ⋙ F)
    [NatTrans.CommShift c.hom ℤ]
    (hc : ∀ K : (nativeProperty P S).FullSubcategory,
      (structureIso Q T hQ (J.obj K)).hom ≫ c.hom.app K =
        (action Q T hQ).map (c.hom.app K) ≫
          a.hom.app ((underlying P S).obj K) ≫ F.map (structureIso P S hP K).hom)
    (bX : CyclicDerivedHomBoundary P) (bY : CyclicDerivedHomBoundary Q)
    (hbX : CyclicDerivedHomBoundaryExact P bX ∧ CyclicDerivedHomBoundaryNatural P bX ∧
      CyclicDerivedHomBoundaryNormalized P bX)
    (hbY : CyclicDerivedHomBoundaryExact Q bY ∧ CyclicDerivedHomBoundaryNatural Q bY ∧
      CyclicDerivedHomBoundaryNormalized Q bY)
    (hcompat : Compatible P S Q T F J c bX bY)
    (L : (nativeProperty Q T).FullSubcategory) :
    (∃ (H : (nativeProperty P S).FullSubcategory)
      (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L)),
      (structureIso P S hP H).hom ≫ e.hom =
        (action P S hP).map e.hom ≫ b.hom.app ((underlying Q T).obj L) ≫
          G.map (structureIso Q T hQ L).hom ∧
      ∃ d : J.obj H ⟶ L,
        (underlying Q T).map d =
          c.hom.app H ≫ F.map e.hom ≫ adj.counit.app ((underlying Q T).obj L)) ∧
    (∀ (H : (nativeProperty P S).FullSubcategory)
      (e : (underlying P S).obj H ≅ G.obj ((underlying Q T).obj L)),
      (structureIso P S hP H).hom ≫ e.hom =
        (action P S hP).map e.hom ≫ b.hom.app ((underlying Q T).obj L) ≫
          G.map (structureIso Q T hQ L).hom →
      ∀ d : J.obj H ⟶ L,
        (underlying Q T).map d =
          c.hom.app H ≫ F.map e.hom ≫ adj.counit.app ((underlying Q T).obj L) →
        Represents P S Q T F J c G adj bX bY L H e d) := by
  -- These hypotheses are retained verbatim; the Hom-sequence argument needs less.
  have _ := hPinv
  have _ := hT
  have _ := hQinv
  have _ := hF
  have _ := hG
  have _ := hJ
  constructor
  · obtain ⟨H, e, he⟩ := realize_right_action P S Q T hS hP hQ G b L
    refine ⟨H, e, he, ?_⟩
    let t : (underlying Q T).obj (J.obj H) ⟶ (underlying Q T).obj L :=
      c.hom.app H ≫ F.map e.hom ≫ adj.counit.app ((underlying Q T).obj L)
    have ht : (structureIso Q T hQ (J.obj H)).hom ≫ t =
        (action Q T hQ).map t ≫ (structureIso Q T hQ L).hom := by
      have hε := counit_equivariant (action P S hP) (action Q T hQ) F G adj a b hb
        ((underlying P S).obj H) ((underlying Q T).obj L)
        (structureIso P S hP H) (structureIso Q T hQ L) e he
      dsimp only [t]
      rw [← Category.assoc, ← Category.assoc, hc H]
      simp only [Category.assoc]
      rw [hε]
      simp only [Functor.map_comp, Category.assoc]
    let t' := T.ι.map t
    have ht' : (cyclicDerivedStructure Q).hom.app (J.obj H).obj ≫ t' =
        Q.mapDerivedCategory.map t' ≫ (cyclicDerivedStructure Q).hom.app L.obj := by
      have hx := congrArg (fun f ↦ T.ι.map f) ht
      simp only [Functor.map_comp] at hx
      exact hx
    have hinv := degreeZero_invariant Q (J.obj H).obj L.obj t' ht'
    obtain ⟨q, hq, _, _, hsurj⟩ := hbY.1 (J.obj H).obj L.obj
      (J.obj H).property.1 L.property.1
    obtain ⟨d, hd⟩ := hsurj ⟨_, hinv⟩
    refine ⟨ObjectProperty.homMk d, ?_⟩
    apply ObjectProperty.hom_ext
    apply (cancel_mono ((shiftFunctorZero (DerivedCategory B) ℤ).inv.app _)).1
    exact (hq d).symm.trans (congrArg Subtype.val hd)
  · intro H e _ d hd
    exact represents_from_lift P S Q T F J c G adj bX bY hbX.1 hbY.1 hbY.2.1
      hcompat L H e d hd

end CategoryTheory.Endofunctor.IsoAlgebra
