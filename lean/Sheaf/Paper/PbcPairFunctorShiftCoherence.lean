/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Paper.CommonStageCalculus
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Triangulated.Functor

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
  sorry

end AlgebraicGeometry.Scheme
