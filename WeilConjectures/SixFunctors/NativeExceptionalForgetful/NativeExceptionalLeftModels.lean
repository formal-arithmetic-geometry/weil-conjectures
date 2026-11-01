/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
import WeilConjectures.WeilSheaf.Localization
import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalCounitHomSquares
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomExactSequence

/-! # NativeExceptionalLeftModels

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

private theorem underlying_constructible (R : Family l D) (T : Space D) (K : W D l T) :
    boundedConstructible l (geometric D T).base.left (R.data (geometric D T)).realization
      ((U D l R T).obj K) := by
  let e := (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingEquiv
  let : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  have : IsIso (closureMap D T) := by
    dsimp only [closureMap]
    infer_instance
  let V := (WeilComplex.forget.obj K)
  have hV := ((WeilComplex.forgetBoundedConstructibleAdic D.k₀ l T.base.left).obj K).property
  have hPull := ProEtale.bounded_homologyProperty_mapDerivedCategory_adicUpperStar
    (inv (closureMap D T)) hV.1 hV.2
  let push := ProEtale.adicLowerStar l (closureMap D T)
  let transport := push.rightDerivedFunctorIsoMapDerivedCategory.app V ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.adicUpperStarIsoLowerStarInv l (asIso (closureMap D T)).symm).symm).app V
  exact ⟨_, hPull, ⟨(sectionDerived l (geometric D T).base.left
    (R.data (geometric D T)).realization).mapIso transport.symm⟩⟩

private theorem forget_models (R : Family l D) :
    Nonempty (∀ T : Space D, ForgetModel D l R T) := by
  classical
  have hm (T : Space D) : Nonempty (ForgetModel D l R T) := by
    let ff : (rho D l R T).FullyFaithful := Classical.choice
      ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
        (R.data (geometric D T)).fully_faithful)
    let := ff.full
    let := ff.faithful
    have hU : ∀ K, (rho D l R T).essImage ((U D l R T).obj K) := by
      intro K
      exact ((R.data (geometric D T)).image _).mp (underlying_constructible D l R T K)
    exact ⟨{ functor := Functor.essImage.liftFunctor (U D l R T) (rho D l R T) hU
             realization := Functor.essImage.liftFunctorCompIso _ _ hU }⟩
  exact ⟨fun T ↦ Classical.choice (hm T)⟩

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

/-- The ordinary derived forgetful functors factor through the common-stage
constructible categories. The normalized left comparison admits representing counit lifts.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, exceptional
adjunction sentence; native comparison proof Steps 1--2.
(blueprint: lem-sf-native-exceptional-left-models).

Proof: use the exact native forgetting comparison to test bounded constructibility
on the underlying complex. Transport along closureMap, an isomorphism over the model,
preserves this predicate. The essential-image assertion and full faithfulness of
Family.data lift each U to the common-stage category, on all derived morphisms.
For the chosen native compactification, compose the open/proper forgetful comparison
with the inverse of the scalar-normalized compact-support realization. The latter is
normalized by the integral proper mate and open unit. Closure transport and
compactification refinement identify this with the operation of any specified
coefficient system and compactification. Lift the resulting natural isomorphism
through the fully faithful realization on the target. Retain this normalized left
comparison a. Native open/proper forgetting identifies the Grothendieck fixed-pair
hearts and the exact Frobenius action. The scalar counit lemma gives an invertible
Frobenius mate and its invariant counit. The normalized cyclic derived Hom sequence
is compatible with exact open and right-derived proper images by its finite
composite functoriality theorem. Apply cyclicDerived_liftedCounit_represents on the
bounded constructible full subcategories. Its degree -1 coinvariant and degree 0
invariant maps are the ordinary adjunction bijections, so the short exact sequences
give the bijection on full native Hom sets. Transport H, e and d through the closure
and realization identifications. No native right adjoint is used. Empty schemes and
identity compactifications use the same exact comparisons. -/
theorem native_exceptional_left_models (R : Family l D) :
    ∃ model : ∀ T : Space D, ForgetModel D l R T,
      ∀ (X Y : Space D) (f₀ : X.base ⟶ Y.base)
        [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
        (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)),
      ∃ a : nativeShriek D l f₀ ⋙ (model Y).functor ≅
          (model X).functor ⋙ (S.ring.operation c .closed).F,
        ∀ L : W D l Y, ∃ (H : W D l X)
          (e : (model X).functor.obj H ≅
            (S.ring.operation c .closed).G.obj ((model Y).functor.obj L))
          (d : (nativeShriek D l f₀).obj H ⟶ L),
          (model Y).functor.map d = a.hom.app H ≫
            (S.ring.operation c .closed).F.map e.hom ≫
            (S.ring.operation c .closed).adjunction.counit.app ((model Y).functor.obj L) ∧
          ∀ K : W D l X,
            Function.Bijective (fun v : K ⟶ H ↦ (nativeShriek D l f₀).map v ≫ d) := by
  classical
  obtain ⟨model⟩ := forget_models D l R
  refine ⟨model, ?_⟩
  intro X Y f₀ _ _ _ S c
  let PX := WeilSheaf.frobeniusPullback D.k₀ l X.base.left
  let PY := WeilSheaf.frobeniusPullback D.k₀ l Y.base.left
  obtain ⟨bX, hbX, _⟩ :=
    CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedHomBoundary PX
  obtain ⟨bY, hbY, _⟩ :=
    CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedHomBoundary PY
  obtain ⟨a, hlifts⟩ := native_exceptional_counit_hom_squares D l R X Y
    (model X) (model Y) f₀ S c bX bY hbX hbY
  refine ⟨a, ?_⟩
  intro L
  obtain ⟨H, e, d, hd, hsquares⟩ := hlifts L
  refine ⟨H, e, d, hd, ?_⟩
  intro K
  obtain ⟨pMinus, pZero, hleft, hright⟩ := hsquares K
  obtain ⟨qx, hqx, _, hex, hqxsurj⟩ := hbX.1 K.obj H.obj K.property.1 H.property.1
  obtain ⟨qy, hqy, hiy, hey, _⟩ := hbY.1
    ((nativeShriek D l f₀).obj K).obj L.obj
    ((nativeShriek D l f₀).obj K).property.1 L.property.1
  let mid : (K.obj ⟶ H.obj) →+ (((nativeShriek D l f₀).obj K).obj ⟶ L.obj) :=
    AddMonoidHom.mk' (fun u ↦
      ((nativeShriek D l f₀).map (ObjectProperty.homMk u) ≫ d).hom) (by
        intro u v
        change (((nativeShriek D l f₀).map
          ((ObjectProperty.homMk u : K ⟶ H) + ObjectProperty.homMk v)) ≫ d).hom = _
        rw [Functor.map_add, Preadditive.add_comp]
        rfl)
  have hmid := short_five_bijective
    (bX K.obj H.obj K.property.1 H.property.1) qx
    (bY ((nativeShriek D l f₀).obj K).obj L.obj
      ((nativeShriek D l f₀).obj K).property.1 L.property.1) qy
    hiy hex hey hqxsurj pMinus mid pZero hleft (by
      intro u
      apply Subtype.ext
      exact (hqy (mid u)).trans
        (hright (ObjectProperty.homMk u) (qx u) (hqx u)).symm)
  constructor
  · intro u v huv
    apply ObjectProperty.hom_ext
    exact hmid.1 (congrArg (fun f ↦ f.hom) huv)
  · intro v
    obtain ⟨u, hu⟩ := hmid.2 v.hom
    exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩

end WeilConjectures.NativeExceptionalForgetful
