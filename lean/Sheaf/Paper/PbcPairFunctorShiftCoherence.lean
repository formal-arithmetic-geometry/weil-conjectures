/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Paper.CommonStageCalculus
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Integer-shift coherence for a prescribed pair-category functor

Source: blueprint main-20261015, proper base change, proof of
`prop-weil-pbc-descent-functors`, exactness sentence; the finite-stage shift calculation
is expanded in the DAG (blueprint: lem-weil-pbc-pair-functor-shift-coherence).

The explicit predicate `StageSystem.Morphism.PairFunctorShiftCoherenceSpec` packages
the full statement; `pbcPairFunctorShiftCoherence` specializes it to the PBC systems.

The finite-stage family and its associator equation are bundled using the existing
`StageSystem.Morphism`. The functor `G` is prescribed independently, with its object and
representative formulas as hypotheses. The conclusion supplies its coherent integer-shift
comparisons, their precise components, and the identity inclusion comparison commuting with
shifts. It uses the canonical common-stage shifts and assumes no triangle preservation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c u v w a b a' b'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.StageSystem.Morphism

/-- The explicit shift-coherence conclusion for prescribed pair-functor formulas.
This packages the formulas of the node using the existing stage-system and shift notions;
it introduces no replacement category, functor, shift, or comparison.
Source: blueprint main-20261015, proper base change, descent-functors proof, exactness sentence
(blueprint: lem-weil-pbc-pair-functor-shift-coherence). -/
def PairFunctorShiftCoherenceSpec
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    {D : I → Type a'} [∀ i, Category.{b'} (D i)]
    (U : StageSystem C) (V : StageSystem D)
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    [∀ {i j : I} (h : i ≤ j), (U.T h).Additive]
    [∀ {i j : I} (h : i ≤ j), (V.T h).Additive]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (U.T h).CommShift ℤ]
    [∀ {i j : I} (h : i ≤ j), (V.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (U.assoc h h').hom ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (V.assoc h h').hom ℤ]
    (A : U.Morphism V) [∀ i, (A.Φ i).Additive] [∀ i, (A.Φ i).CommShift ℤ] : Prop :=
  (∀ (i : I) (K : C i), HEq ((A.β (le_refl i)).hom.app K) (𝟙 ((A.Φ i).obj K))) →
  (∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (A.β h).hom ℤ) →
  ∀ (G : U.PairCategory ⥤ V.PairCategory) [G.Additive],
    (∀ X, G.obj X = ⟨X.stage, (A.Φ X.stage).obj X.obj⟩) →
    (∀ (X Y : U.PairCategory) (M : I) (hX : X.stage ≤ M) (hY : Y.stage ≤ M)
      (f : X.toStage hX ⟶ Y.toStage hY),
      HEq (G.map (PairCategory.mkHom M hX hY f))
        (PairCategory.mkHom (S := V)
          (X := ⟨X.stage, (A.Φ X.stage).obj X.obj⟩)
          (Y := ⟨Y.stage, (A.Φ Y.stage).obj Y.obj⟩)
          M hX hY ((A.β hX).hom.app X.obj ≫ (A.Φ M).map f ≫
            (A.β hY).inv.app Y.obj))) →
    ∃ q : G.CommShift ℤ,
      (fun [_hq : G.CommShift ℤ] ↦
        (∀ (n : ℤ) (X : U.PairCategory),
          HEq ((G.commShiftIso n).hom.app X)
            ((V.ι X.stage).map (((A.Φ X.stage).commShiftIso n).hom.app X.obj))) ∧
        ∀ i : I, ∃ κ : U.ι i ⋙ G ≅ A.Φ i ⋙ V.ι i,
          (∀ K : C i, HEq (κ.hom.app K) (𝟙 ((V.ι i).obj ((A.Φ i).obj K)))) ∧
            NatTrans.CommShift κ.hom ℤ) (_hq := q)


-- The stagewise construction is the shift part of PbcDescentFunctors,
-- reused here without its distinguished-triangle hypotheses.
section
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type a} [∀ i, Category.{b} (C i)]
  {D : I → Type a'} [∀ i, Category.{b'} (D i)]
  {S : StageSystem C} {S' : StageSystem D}

section StageShift
variable [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S'.assoc h h').hom ℤ]
  (F : StageSystem.Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]
  (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)

private def shiftHom (n : ℤ) : Hom
    ((pbcStageShift S n).comp F) (F.comp (pbcStageShift S' n)) where
  τ i := ((F.Φ i).commShiftIso n).hom
  comm {i j} h K := by
    have := hβ h
    simpa [Morphism.comp, pbcStageShift, Functor.commShiftIso_comp_hom_app,
      Category.assoc] using (NatTrans.shift_app_comm (F.β h).hom n K)

private def shiftIso (n : ℤ) :
    (pbcPairShift S n) ⋙ F.functor ≅ F.functor ⋙ (pbcPairShift S' n) :=
  (functorCompIso (pbcStageShift S n) F).symm ≪≫
    NatIso.ofComponents
      (F := ((pbcStageShift S n).comp F).functor)
      (G := (F.comp (pbcStageShift S' n)).functor)
      (fun K ↦ (S'.ι K.stage).mapIso (((F.Φ K.stage).commShiftIso n).app K.obj))
      (fun f ↦ (descNatTrans (shiftHom F hβ n)).naturality f) ≪≫
    functorCompIso F (pbcStageShift S' n)

end StageShift

section ExactShift
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type a} [∀ i, Category.{b} (C i)]
  {D : I → Type a'} [∀ i, Category.{b'} (D i)]
  {S : StageSystem C} {S' : StageSystem D}
  [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S'.assoc h h').hom ℤ]
  (F : StageSystem.Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]
  (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)

set_option backward.isDefEq.respectTransparency false in
private theorem shiftIso_hom_app (n : ℤ) (K : S.PairCategory) :
    (shiftIso F hβ n).hom.app K =
      (S'.ι K.stage).map (((F.Φ K.stage).commShiftIso n).hom.app K.obj) := by
  simp only [shiftIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Morphism.functorCompIso_inv_app, Morphism.functorCompIso_hom_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom,
    Category.comp_id]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def descendedCommShift : F.functor.CommShift ℤ where
  commShiftIso := shiftIso F hβ
  commShiftIso_zero := by
    ext K
    simp only [shiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    change (S'.ι K.stage).map (((F.Φ K.stage).commShiftIso (0 : ℤ)).hom.app K.obj) =
      F.functor.map ((S.ι K.stage).map
        ((shiftFunctorZero (C K.stage) ℤ).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        ((shiftFunctorZero (D K.stage) ℤ).inv.app ((F.Φ K.stage).obj K.obj))
    erw [Morphism.functor_map_ι]
    simpa only [Functor.CommShift.isoZero_hom_app, Functor.map_comp] using
      congrArg ((S'.ι K.stage).map)
      (congr_app (congrArg Iso.hom ((F.Φ K.stage).commShiftIso_zero ℤ)) K.obj)
  commShiftIso_add n m := by
    ext K
    simp only [Functor.CommShift.isoAdd_hom_app, shiftIso_hom_app]
    change (S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso (n + m)).hom.app K.obj) =
      F.functor.map ((S.ι K.stage).map
        ((shiftFunctorAdd (C K.stage) n m).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso m).hom.app ((shiftFunctor (C K.stage) n).obj K.obj)) ≫
      (pbcPairShift S' m).map ((S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso n).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        ((shiftFunctorAdd (D K.stage) n m).inv.app ((F.Φ K.stage).obj K.obj))
    erw [Morphism.functor_map_ι]
    erw [(pbcStageShift S' m).functor_map_ι]
    simpa only [Functor.CommShift.isoAdd_hom_app, Functor.map_comp, pbcStageShift] using
      congrArg ((S'.ι K.stage).map)
      (congr_app (congrArg Iso.hom ((F.Φ K.stage).commShiftIso_add n m)) K.obj)

set_option backward.isDefEq.respectTransparency false in
private theorem inclusionComp_commShift (i : I) :
    letI := descendedCommShift F hβ
    NatTrans.CommShift (F.ιCompFunctorIso i).hom ℤ := by
  let _ := descendedCommShift F hβ
  constructor
  intro n
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  change F.functor.map (𝟙 _) ≫ (shiftIso F hβ n).hom.app ((S.ι i).obj K) ≫
      (shiftFunctor S'.PairCategory n).map (𝟙 _) =
    𝟙 _ ≫ ((S'.ι i).map (((F.Φ i).commShiftIso n).hom.app K) ≫ 𝟙 _)
  simp only [shiftIso_hom_app, Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

end ExactShift
end

set_option backward.isDefEq.respectTransparency false in
private theorem pairFunctorShiftCoherence
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type a} [∀ i, Category.{b} (C i)]
    {D : I → Type a'} [∀ i, Category.{b'} (D i)]
    (U : StageSystem C) (V : StageSystem D)
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    [∀ {i j : I} (h : i ≤ j), (U.T h).Additive]
    [∀ {i j : I} (h : i ≤ j), (V.T h).Additive]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (U.T h).CommShift ℤ]
    [∀ {i j : I} (h : i ≤ j), (V.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (U.assoc h h').hom ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (V.assoc h h').hom ℤ]
    (A : U.Morphism V) [∀ i, (A.Φ i).Additive] [∀ i, (A.Φ i).CommShift ℤ] :
    PairFunctorShiftCoherenceSpec U V A := by
  intro _hunit hβ G _hG hobj hmap
  have hG : G = A.functor := by
    apply Functor.hext hobj
    intro X Y f
    induction f using StageSystem.PairCategory.hom_induction with
    | h M hX hY f => exact hmap X Y M hX hY f
  subst G
  let q := descendedCommShift A hβ
  refine ⟨q, ?_, ?_⟩
  · intro n X
    exact heq_of_eq (shiftIso_hom_app A hβ n X)
  · intro i
    refine ⟨A.ιCompFunctorIso i, ?_, ?_⟩
    · intro K
      exact HEq.rfl
    · exact inclusionComp_commShift A hβ i

end CategoryTheory.StageSystem.Morphism

namespace AlgebraicGeometry.Scheme

/-- Integer-shift comparisons descend to any additive functor with the prescribed formulas.
The fields of `A` are the functors `Φ_E`, the isomorphisms `β_{F/E}`, and exactly their
associator coherence equation. In `PairFunctorShiftCoherenceSpec`, the stage `CommShift`
instances encode the given natural isomorphisms `s_{E,n}` and their zero and addition
equations. Its second premise is the
displayed compatibility with the scalar comparisons. Heterogeneous equalities express arrows with
endpoints identified by the given object formula, without imposing definitional equality.

Source: blueprint main-20261015, proper base change,
`prop-weil-pbc-descent-functors.proof.md`, exactness sentence; explicit shift calculation
in the DAG (blueprint: lem-weil-pbc-pair-functor-shift-coherence).

Proof: (1) At repeated fields, the unit equations for scalar associators and compatibility
with shifts make the scalar shift comparison idempotent, hence identity. Together with
`β_{E/E} = 1`, this gives `G[E,v] = [E,Φ_E(v)]`; same-stage composition and identity are
represented by the corresponding stage operations (finite-stage pair category and scalar
extension nodes). (2) Iterate the common-stage shift formula, using inverse comparisons for
negative integers. A representative shifts to `σ_source ≫ u[n] ≫ σ_target⁻¹`. The inclusion
comparisons have identity components; zero and addition identifications at `(E,K)` are the
images of the corresponding stage identifications (common-stage calculus).
(3) Represent an arbitrary arrow at `M`. The assumed `β`/shift equation rewrites the two
endpoint composites. Postcomposition by the invertible target `β[n]σ` reduces their equality
to naturality of the stage comparison at `u`; cancel this isomorphism and pass to classes.
This proves naturality of `[E,s_{E,n,K}]`. (4) Its inverse is `[E,s_{E,n,K}⁻¹]`; same-stage
composition gives both inverse equations, and the naturality equation gives inverse
naturality. (5) The zero equation can be computed entirely at `E` and is the stage zero
equation. (6) Likewise, represent all arrows of the addition equation at `E` and apply the
stage addition equation. This works for arbitrary integers, including opposite integers,
using the canonical addition identification. (7) Both inclusion composites send `v` to
`[E,Φ_E(v)]`, so identity components form their natural isomorphism. Their composite shift
comparisons are both `[E,s_{E,n,K}]`; the inclusion comparisons and shifted identities are
identities. This proves its shift compatibility. None of these steps uses distinguished
triangles. -/
theorem pbcPairFunctorShiftCoherence
    (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) (S : Scheme.{v}) [IsNoetherian T] [IsNoetherian S]
    (hTdim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
    (hSdim : ∃ d : ℕ, topologicalKrullDim S ≤ d)
    (hTl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (hSl : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    (A : StageSystem.Morphism (pbcScalarSystem l Ω T hTdim hTl)
      (pbcScalarSystem l Ω S hSdim hSl))
    [∀ E, (A.Φ E).Additive] [∀ E, (A.Φ E).CommShift ℤ] :
    StageSystem.Morphism.PairFunctorShiftCoherenceSpec
      (pbcScalarSystem l Ω T hTdim hTl) (pbcScalarSystem l Ω S hSdim hSl) A := by
  exact StageSystem.Morphism.pairFunctorShiftCoherence _ _ A

end AlgebraicGeometry.Scheme
