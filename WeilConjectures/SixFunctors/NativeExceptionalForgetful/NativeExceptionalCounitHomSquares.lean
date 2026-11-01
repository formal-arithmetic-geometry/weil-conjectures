/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalOrdinaryCounit

/-! # Native exceptional counit and the two outer Hom squares

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence; native left-model proof, Steps 1--2.
(blueprint: lem-sf-native-exceptional-counit-hom-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

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

private theorem action_postcomp
    {A : Type*} [Category* A] [Abelian A]
    (Q : A ⥤ A) [Q.Additive] [Q.IsEquivalence]
    [HasDerivedCategory A] [HasDerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra Q)]
    (M N N' : DerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra Q)) (d : N ⟶ N') (r : ℤ)
    (u : CyclicDerivedHom Q M N r) :
    cyclicDerivedHomAction Q M N' r
        (u ≫ ((forget Q).mapDerivedCategory.map d)⟦r⟧') =
      cyclicDerivedHomAction Q M N r u ≫
        ((forget Q).mapDerivedCategory.map d)⟦r⟧' := by
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

private theorem forget_postcomp
    {A : Type*} [Category* A] [Abelian A]
    (Q : A ⥤ A) [Q.Additive] [Q.IsEquivalence]
    [HasDerivedCategory A] [HasDerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra Q)]
    (M N N' : DerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra Q)) (f : M ⟶ N) (d : N ⟶ N') :
    cyclicDerivedForget Q M N f ≫ ((forget Q).mapDerivedCategory.map d)⟦(0 : ℤ)⟧' =
      cyclicDerivedForget Q M N' (f ≫ d) := by
  change ((forget Q).mapDerivedCategory.map f ≫
      (shiftFunctorZero (DerivedCategory A) ℤ).inv.app _) ≫ _ = _
  change (_ ≫ _) ≫ _ = (forget Q).mapDerivedCategory.map (f ≫ d) ≫ _
  rw [Functor.map_comp, Category.assoc]
  simpa only [Functor.id_map, Category.assoc] using
    congrArg (fun k ↦ (forget Q).mapDerivedCategory.map f ≫ k)
    (((shiftFunctorZero (DerivedCategory A) ℤ).inv.naturality
      ((forget Q).mapDerivedCategory.map d)).symm)

private theorem boundary_postcomp
    {A : Type*} [Category* A] [Abelian A]
    (Q : A ⥤ A) [Q.Additive] [Q.IsEquivalence]
    [HasDerivedCategory A] [HasDerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra Q)]
    (b : CyclicDerivedHomBoundary Q) (hb : CyclicDerivedHomBoundaryNatural Q b)
    (M N N' : DerivedCategory (CategoryTheory.Endofunctor.IsoAlgebra Q))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N)
    (hN' : DerivedCategory.TStructure.t.bounded N')
    (d : N ⟶ N') (v : CyclicDerivedHom Q M N (-1)) :
    b M N hM hN (QuotientAddGroup.mk v) ≫ d =
      b M N' hM hN' (QuotientAddGroup.mk
        (v ≫ ((forget Q).mapDerivedCategory.map d)⟦(-1 : ℤ)⟧')) := by
  have hi : (forget Q).mapDerivedCategory.map (𝟙 M) ≫ v ≫
        ((forget Q).mapDerivedCategory.map d)⟦(-1 : ℤ)⟧' =
      v ≫ ((forget Q).mapDerivedCategory.map d)⟦(-1 : ℤ)⟧' :=
    (congrArg (fun w ↦ w ≫ v ≫ ((forget Q).mapDerivedCategory.map d)⟦(-1 : ℤ)⟧')
      ((forget Q).mapDerivedCategory.map_id M)).trans (Category.id_comp _)
  exact (Category.id_comp _).symm.trans
    ((hb M N M N' hM hN hM hN' (𝟙 M) d v).trans
      (congrArg (fun w ↦ b M N' hM hN' (QuotientAddGroup.mk w)) hi))

set_option maxHeartbeats 800000 in
-- The dependent geometric comparisons require more elaboration steps than the default.
/-- The normalized geometric counit has a native lift, and its maps on the two outer
terms of the cyclic Hom sequence are additive equivalences commuting with the boundary
and forgetting maps. No bijection on native Hom sets is asserted here.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence; Steps 1--2 of
lem-sf-native-exceptional-left-models.
(blueprint: lem-sf-native-exceptional-counit-hom-squares).

Proof: native_exceptional_ordinary_counit supplies the comparison a, the native
exceptional-image object H, its ordinary identification e, and the invariant ordinary
counit carrier t. Surjectivity onto degree-zero invariants in the supplied exact
cyclic Hom sequence lifts t to a native morphism d. Naturality of the specified
realization and its full faithfulness give the required common-stage counit equation.
The ordinary graded adjunction bijections are additive because counitHomTransport is
an additive functorial formula. The action clause of counitHomTransport_compatible
and equivariance of postcomposition by the native d make these bijections equivariant.
Restrict in degree zero to the kernel of 1-T and descend in degree minus one to the
quotient by its image, obtaining pZero and pMinus. On quotient representatives the
boundary clause of counitHomTransport_compatible followed by boundary naturality
under d gives the left square; quotient induction extends it to every class. The
forgetting clause and naturality of the zero-shift comparison give the right square.
No native right adjoint or faithfulness of derived forgetting is used. On empty
schemes the same groups and maps are zero; identity compactifications retain the
same unit-normalized formulas. -/
theorem native_exceptional_counit_hom_squares (R : Family l D)
    (X Y : Space D) (VX : ForgetModel D l R X) (VY : ForgetModel D l R Y)
    (f₀ : X.base ⟶ Y.base)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀))
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryExact _ bX ∧ CyclicDerivedHomBoundaryNatural _ bX ∧
      CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryExact _ bY ∧ CyclicDerivedHomBoundaryNatural _ bY ∧
      CyclicDerivedHomBoundaryNormalized _ bY) :
    ∃ a : nativeShriek D l f₀ ⋙ VY.functor ≅
        VX.functor ⋙ (S.ring.operation c .closed).F,
      ∀ L : W D l Y, ∃ (H : W D l X)
        (e : VX.functor.obj H ≅ (S.ring.operation c .closed).G.obj (VY.functor.obj L))
        (d : (nativeShriek D l f₀).obj H ⟶ L),
        VY.functor.map d = a.hom.app H ≫ (S.ring.operation c .closed).F.map e.hom ≫
          (S.ring.operation c .closed).adjunction.counit.app (VY.functor.obj L) ∧
        ∀ K : W D l X,
          ∃ (pMinus : CyclicDerivedHomCoinvariants
                (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj ≃+
              CyclicDerivedHomCoinvariants
                (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
                ((nativeShriek D l f₀).obj K).obj L.obj)
            (pZero : CyclicDerivedHomInvariants
                (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj ≃+
              CyclicDerivedHomInvariants
                (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
                ((nativeShriek D l f₀).obj K).obj L.obj),
            (∀ z,
              ((nativeShriek D l f₀).map (ObjectProperty.homMk
                (bX K.obj H.obj K.property.1 H.property.1 z)) ≫ d).hom =
              bY ((nativeShriek D l f₀).obj K).obj L.obj
                ((nativeShriek D l f₀).obj K).property.1 L.property.1 (pMinus z)) ∧
            (∀ (v : K ⟶ H)
              (z : CyclicDerivedHomInvariants
                (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj),
              z.val = cyclicDerivedForget _ K.obj H.obj v.hom →
              (pZero z).val = cyclicDerivedForget _
                ((nativeShriek D l f₀).obj K).obj L.obj
                ((nativeShriek D l f₀).map v ≫ d).hom) := by
  classical
  have ordinary := native_exceptional_ordinary_counit D l R X Y VX VY f₀ S c
  let a := ordinary.choose
  have ha := ordinary.choose_spec
  refine ⟨a, ?_⟩
  intro L
  have ordinaryL := ha L
  let H := ordinaryL.choose
  have ordinaryH := ordinaryL.choose_spec
  let e := ordinaryH.choose
  have ordinaryE := ordinaryH.choose_spec
  let t := ordinaryE.choose
  have ht := ordinaryE.choose_spec.1
  have hinv := ordinaryE.choose_spec.2.1
  have hbij := ordinaryE.choose_spec.2.2
  let PY := WeilSheaf.frobeniusPullback D.k₀ l Y.base.left
  have sequenceY := hbY.1 ((nativeShriek D l f₀).obj H).obj L.obj
    ((nativeShriek D l f₀).obj H).property.1 L.property.1
  have hq := sequenceY.choose_spec.1
  have hsurj := sequenceY.choose_spec.2.2.2
  have lift := hsurj ⟨_, hinv⟩
  let d₀ := lift.choose
  have hd₀ := lift.choose_spec
  let d : (nativeShriek D l f₀).obj H ⟶ L := ObjectProperty.homMk d₀
  have hd : WeilComplex.forget.map d = t := by
    apply (cancel_mono ((shiftFunctorZero _ ℤ).inv.app (WeilComplex.forget.obj L))).1
    exact (hq d₀).symm.trans (congrArg Subtype.val hd₀)
  refine ⟨H, e, d, ?_, ?_⟩
  · let ff : (rho D l R Y).FullyFaithful := Classical.choice
      ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
        (R.data (geometric D Y)).fully_faithful)
    apply ff.map_injective
    apply (cancel_mono (VY.realization.hom.app L)).1
    calc
      _ = VY.realization.hom.app ((nativeShriek D l f₀).obj H) ≫
          (counitOrdinaryTransport D l R Y).map (WeilComplex.forget.map d) :=
        VY.realization.hom.naturality d
      _ = VY.realization.hom.app ((nativeShriek D l f₀).obj H) ≫
          (counitOrdinaryTransport D l R Y).map t := by rw [hd]
      _ = _ := (congrArg
          (fun w ↦ VY.realization.hom.app ((nativeShriek D l f₀).obj H) ≫ w) ht).trans
        ((VY.realization.app ((nativeShriek D l f₀).obj H)).hom_inv_id_assoc _)
  · intro K
    have compatibility := counitHomTransport_compatible D l f₀ bX bY hbX.2 hbY.2 K H
    have hact := compatibility.1
    have hforget := compatibility.2.1
    have hboundary := compatibility.2.2
    let phi (r : ℤ) :
        CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj r →+
        CyclicDerivedHom PY ((nativeShriek D l f₀).obj K).obj L.obj r :=
      AddMonoidHom.mk' (fun v ↦ counitHomTransport D l f₀ K H r v ≫ t⟦r⟧') (by
        intro v w
        simp only [counitHomTransport, Functor.map_add,
          Preadditive.comp_add, Preadditive.add_comp])
    let pe (r : ℤ) := AddEquiv.ofBijective (phi r) (hbij K r)
    have hp (r : ℤ) (v :
        CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj r) :
        pe r (cyclicDerivedHomAction _ K.obj H.obj r v) =
          cyclicDerivedHomAction PY ((nativeShriek D l f₀).obj K).obj L.obj r (pe r v) := by
      change counitHomTransport D l f₀ K H r _ ≫ t⟦r⟧' =
        cyclicDerivedHomAction PY _ _ r (counitHomTransport D l f₀ K H r v ≫ t⟦r⟧')
      have hdRaw : (forget PY).mapDerivedCategory.map d.hom = t := hd
      calc
        _ = counitHomTransport D l f₀ K H r _ ≫
            ((forget PY).mapDerivedCategory.map d.hom)⟦r⟧' :=
          congrArg (fun w ↦ counitHomTransport D l f₀ K H r _ ≫ w⟦r⟧') hdRaw.symm
        _ = cyclicDerivedHomAction PY _ _ r (counitHomTransport D l f₀ K H r v) ≫
            ((forget PY).mapDerivedCategory.map d.hom)⟦r⟧' :=
          congrArg (fun w ↦ w ≫ ((forget PY).mapDerivedCategory.map d.hom)⟦r⟧') (hact r v)
        _ = cyclicDerivedHomAction PY _ _ r
            (counitHomTransport D l f₀ K H r v ≫
              ((forget PY).mapDerivedCategory.map d.hom)⟦r⟧') :=
          (action_postcomp PY _ _ _ d.hom r _).symm
        _ = _ := congrArg (fun w ↦ cyclicDerivedHomAction PY _ _ r
          (counitHomTransport D l f₀ K H r v ≫ w⟦r⟧')) hdRaw
    have kernel := (kernel_quotient_equivs
      (cyclicDerivedHomAction _ K.obj H.obj 0)
      (cyclicDerivedHomAction PY ((nativeShriek D l f₀).obj K).obj L.obj 0) (pe 0) (hp 0)).1
    let pZero := kernel.choose
    have hpZero := kernel.choose_spec
    have cokernel := (kernel_quotient_equivs
      (cyclicDerivedHomAction _ K.obj H.obj (-1))
      (cyclicDerivedHomAction PY ((nativeShriek D l f₀).obj K).obj L.obj (-1))
      (pe (-1)) (hp (-1))).2
    let pMinus := cokernel.choose
    have hpMinus := cokernel.choose_spec
    change ∀ v, pMinus (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (counitHomTransport D l f₀ K H (-1) v ≫ t⟦(-1 : ℤ)⟧') at hpMinus
    change ∀ v, (pZero v).val = counitHomTransport D l f₀ K H 0 v.val ≫ t⟦(0 : ℤ)⟧'
      at hpZero
    refine ⟨pMinus, pZero, ?_, ?_⟩
    · intro z
      refine QuotientAddGroup.induction_on z ?_
      intro v
      have hdRaw : (forget PY).mapDerivedCategory.map d.hom = t := hd
      have hn' :
          bY ((nativeShriek D l f₀).obj K).obj ((nativeShriek D l f₀).obj H).obj
              ((nativeShriek D l f₀).obj K).property.1
              ((nativeShriek D l f₀).obj H).property.1
              (QuotientAddGroup.mk (counitHomTransport D l f₀ K H (-1) v)) ≫ d.hom =
            bY ((nativeShriek D l f₀).obj K).obj L.obj
              ((nativeShriek D l f₀).obj K).property.1 L.property.1
              (QuotientAddGroup.mk (counitHomTransport D l f₀ K H (-1) v ≫
                ((forget PY).mapDerivedCategory.map d.hom)⟦(-1 : ℤ)⟧')) :=
        boundary_postcomp PY bY hbY.2.1 _ _ _ _ _ _ d.hom _
      have hz := (congrArg (fun w ↦ QuotientAddGroup.mk
        (counitHomTransport D l f₀ K H (-1) v ≫ w⟦(-1 : ℤ)⟧')) hdRaw).trans
          (hpMinus v).symm
      exact (congrArg (fun w ↦ w ≫ d.hom) (hboundary v)).trans
        (hn'.trans (congrArg (bY ((nativeShriek D l f₀).obj K).obj L.obj
          ((nativeShriek D l f₀).obj K).property.1 L.property.1) hz))
    · intro v z hz
      have hdRaw : (forget PY).mapDerivedCategory.map d.hom = t := hd
      calc
        _ = counitHomTransport D l f₀ K H 0 z.val ≫ t⟦(0 : ℤ)⟧' := hpZero z
        _ = counitHomTransport D l f₀ K H 0
            (cyclicDerivedForget _ K.obj H.obj v.hom) ≫ t⟦(0 : ℤ)⟧' :=
          congrArg (fun w ↦ counitHomTransport D l f₀ K H 0 w ≫ t⟦(0 : ℤ)⟧') hz
        _ = cyclicDerivedForget PY ((nativeShriek D l f₀).obj K).obj
            ((nativeShriek D l f₀).obj H).obj ((nativeShriek D l f₀).map v).hom ≫
              t⟦(0 : ℤ)⟧' :=
          congrArg (fun w ↦ w ≫ t⟦(0 : ℤ)⟧') (hforget v)
        _ = cyclicDerivedForget PY ((nativeShriek D l f₀).obj K).obj
            ((nativeShriek D l f₀).obj H).obj ((nativeShriek D l f₀).map v).hom ≫
              ((forget PY).mapDerivedCategory.map d.hom)⟦(0 : ℤ)⟧' :=
          congrArg (fun w ↦ cyclicDerivedForget PY ((nativeShriek D l f₀).obj K).obj
            ((nativeShriek D l f₀).obj H).obj ((nativeShriek D l f₀).map v).hom ≫
              w⟦(0 : ℤ)⟧') hdRaw.symm
        _ = _ := forget_postcomp PY _ _ _ ((nativeShriek D l f₀).map v).hom d.hom

end WeilConjectures.NativeExceptionalForgetful
