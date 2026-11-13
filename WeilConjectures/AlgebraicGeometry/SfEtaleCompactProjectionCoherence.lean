/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionForward
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc

/-! # Ordinary etale compact-support projection coherence

The inverse projections are those of the supplied open/proper factorizations.
The compositor is the explicit graph comparison, not an unspecified isomorphism.
All objects belong to the ordinary unbounded derived categories; no qc or
Noetherian hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u u'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
open scoped CategoryTheory.Functor

private theorem inverse_projection_associativity
    {C : Type*} [Category C] {A B D E H I : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ≅ E) (d : A ≅ H)
    (e : H ⟶ I) (f : I ⟶ E) [IsIso a] [IsIso b] [IsIso e]
    (h : a ≫ b ≫ c.hom = d.hom ≫ e ≫ f) :
    inv e ≫ d.inv = f ≫ c.inv ≫ inv b ≫ inv a := by
  apply (cancel_epi e).1
  apply (cancel_epi d.hom).1
  simp only [IsIso.hom_inv_id_assoc, d.hom_inv_id]
  rw [← reassoc_of% h]
  simp only [c.hom_inv_id_assoc,
    IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]

namespace AlgebraicGeometry.Etale

attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory projectionMapOfCompactification
  DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian

open Lean Elab Tactic Meta

private theorem compactProjectionProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

private theorem compactTensor_obj_obj
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (M N : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((derivedTensor B X).obj M).obj N = M ⊗ N := rfl

-- Normalize only the tensor object APIs; unfolding the full derived monoidal
-- construction would force expensive comparisons of its concrete instances.
private meta def compactProjectionReduceObj (e : Expr) : MetaM Expr := do
  if !e.getAppFn.isConstOf ``Functor.obj then return e
  let args := e.getAppArgs
  let F := args[args.size - 2]!
  let N := args.back!
  if !F.getAppFn.isConstOf ``Functor.obj then return e
  let argsF := F.getAppArgs
  let T := argsF[argsF.size - 2]!
  let M := argsF.back!
  let argsT := T.getAppArgs
  let B := argsT[0]!
  if T.getAppFn.isConstOf ``derivedTensor then
    let some X ← argsT.findM? (fun a ↦ do
      return (← inferType a).getAppFn.isConstOf ``Scheme) |
        throwError "no scheme argument of derivedTensor"
    let h ← mkAppM ``compactTensor_obj_obj #[B, X, M, N]
    return (← inferType h).appArg!
  if T.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek ||
      T.getAppFn.isConstOf ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar then
    let some _c ← argsT.findM? (fun a ↦ do
      return (← inferType a).getAppFn.isConstOf ``Compactification) |
        throwError "no compactification argument"
    let thm := if T.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek then
      ``derivedTensorRightDerivedLowerShriek_obj_obj else
      ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    let xs := argsT ++ #[M, N]
    let h := mkAppN (mkConst thm T.getAppFn.constLevels!) xs
    let _ ← inferType h
    return (← inferType h).appArg!
  return e

-- Build ordinary congruence and proof-irrelevance proofs, checked by the kernel.
private meta partial def compactProjectionCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  let an ← compactProjectionReduceObj a
  let bn ← compactProjectionReduceObj b
  if an != a || bn != b then return ← compactProjectionCongrHEq an bn
  if ← isProp (← inferType a) then
    let hp ← compactProjectionCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``compactProjectionProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← compactProjectionCongrHEq argsA[i]! argsB[i]!
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  else
    throwError m!"Different heads: {a} versus {b}"

private theorem generic_inverse_monoidal
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (P Q : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    [∀ M P, IsIso (((projectionMapOfCompactification B c).app M).app P)] :
    inv (((projectionMapOfCompactification B c).app M).app (P ⊗ Q)) ≫
      (α_ ((rightDerivedLowerShriekOfCompactification B c).obj M) P Q).inv =
      (rightDerivedLowerShriekOfCompactification B c).map
        ((M ◁ (leftDerivedUpperStarTensorIso B f P Q).hom) ≫
          (α_ M ((upperStar B f).leftDerivedFunctor.obj P)
            ((upperStar B f).leftDerivedFunctor.obj Q)).inv) ≫
      inv (((projectionMapOfCompactification B c).app
        (M ⊗ (upperStar B f).leftDerivedFunctor.obj P)).app Q) ≫
      (inv (((projectionMapOfCompactification B c).app M).app P)) ▷ Q := by
  have h := projectionMapOfCompactification_assoc B c M P Q
  rw [← leftDerivedUpperStarTensorIso_hom] at h
  have ha : IsIso
      ((((projectionMapOfCompactification B c).app M).app P) ▷ Q) := by
    infer_instance
  let := ha
  have hi := inverse_projection_associativity
    ((((projectionMapOfCompactification B c).app M).app P) ▷ Q)
    (((projectionMapOfCompactification B c).app
      (M ⊗ (upperStar B f).leftDerivedFunctor.obj P)).app Q)
    ((rightDerivedLowerShriekOfCompactification B c).mapIso
      (α_ M ((upperStar B f).leftDerivedFunctor.obj P)
        ((upperStar B f).leftDerivedFunctor.obj Q)))
    (α_ ((rightDerivedLowerShriekOfCompactification B c).obj M) P Q)
    (((projectionMapOfCompactification B c).app M).app (P ⊗ Q))
    ((rightDerivedLowerShriekOfCompactification B c).map
      (M ◁ (leftDerivedUpperStarTensorIso B f P Q).hom)) h
  rw [MonoidalCategory.inv_whiskerRight] at hi
  simpa only [Functor.mapIso_inv, Functor.map_comp, Category.assoc] using hi

private theorem generic_inverse_associativity
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (P Q : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    [∀ M P, IsIso (((projectionMapOfCompactification B c).app M).app P)] :
    inv (((projectionMapOfCompactification B c).app M).app
        (((derivedTensor B Y).obj P).obj Q)) ≫
      (derivedTensorAssociator B Y
        ((rightDerivedLowerShriekOfCompactification B c).obj M) P Q).inv =
    (rightDerivedLowerShriekOfCompactification B c).map
        ((((derivedTensor B X).obj M).map
          (leftDerivedUpperStarTensorIso B f P Q).hom) ≫
        (derivedTensorAssociator B X M
          ((L(upperStar B f)).obj P)
          ((L(upperStar B f)).obj Q)).inv) ≫
      inv (((projectionMapOfCompactification B c).app
        (((derivedTensor B X).obj M).obj ((L(upperStar B f)).obj P))).app Q) ≫
      ((derivedTensor B Y).map
        (inv (((projectionMapOfCompactification B c).app M).app P))).app Q := by
  have h := generic_inverse_monoidal B c M P Q
  simp only [derivedTensor_map_app, derivedTensor_obj_map, derivedTensorAssociator_eq]
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "no inverse projection identity"
    let eq ← compactProjectionCongrHEq target
      (← Lean.instantiateMVars d.type)
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[eq]
    let pf ← Lean.Meta.mkAppM ``Eq.mpr #[eq, d.toExpr]
    (← Lean.Elab.Tactic.getMainGoal).assign pf

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

attribute [local instance 20000] Etale.sheafBraidedCategory

/-- The inverse of the canonical compactification projection morphism. -/
noncomputable def sfEtaleCompactProjectionInverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (P : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj P)) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj P :=
  @inv _ _ _ _ (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app P)
    ((sfEtaleAmbientAdjointProjection A c).2 M P)

/-- Inverse projection is natural in its first argument. -/
theorem sfEtaleCompactProjectionInverse_naturality_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : DerivedCategoryModule A X} (a : M ⟶ N) (P : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map a).app
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj P)) ≫
      sfEtaleCompactProjectionInverse A c N P =
    sfEtaleCompactProjectionInverse A c M P ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a)).app P := by
  let (M : DerivedCategoryModule A X) (P : DerivedCategoryModule A Y) :
      IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app P) :=
    (sfEtaleAmbientAdjointProjection A c).2 M P
  unfold sfEtaleCompactProjectionInverse
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (NatTrans.congr_app
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).naturality a) P).symm

/-- Inverse projection is natural in its second argument. -/
theorem sfEtaleCompactProjectionInverse_naturality_right
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) {P Q : DerivedCategoryModule A Y} (b : P ⟶ Q) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((L(upperStar (ModuleCat.{u + 1} A) f)).map b)) ≫
      sfEtaleCompactProjectionInverse A c M Q =
    sfEtaleCompactProjectionInverse A c M P ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).map b := by
  let (M : DerivedCategoryModule A X) (P : DerivedCategoryModule A Y) :
      IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app P) :=
    (sfEtaleAmbientAdjointProjection A c).2 M P
  unfold sfEtaleCompactProjectionInverse
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).naturality b).symm

/-- Tensor associativity for the specified inverse projection. -/
theorem sfEtaleCompactProjectionInverse_associativity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (P Q : DerivedCategoryModule A Y) :
    sfEtaleCompactProjectionInverse A c M
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj P).obj Q) ≫
      (derivedTensorAssociator (ModuleCat.{u + 1} A) Y
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) P Q).inv =
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f P Q).hom) ≫
        (derivedTensorAssociator (ModuleCat.{u + 1} A) X M
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj P)
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj Q)).inv) ≫
      sfEtaleCompactProjectionInverse A c
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj P)) Q ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (sfEtaleCompactProjectionInverse A c M P)).app Q := by
  let (N : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
      IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app N).app L) :=
    (sfEtaleAmbientAdjointProjection A c).2 N L
  unfold sfEtaleCompactProjectionInverse
  exact generic_inverse_associativity (ModuleCat.{u + 1} A) c M P Q

private theorem inverse_graph_projection_square
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (t : A ⟶ F) (e : F ⟶ G) (d : G ⟶ E)
    [IsIso a] [IsIso e] [IsIso d]
    (h : t ≫ e ≫ d = a ≫ b ≫ c) :
    inv a ≫ t = b ≫ c ≫ inv d ≫ inv e := by
  apply (cancel_epi a).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem inverse_projection_wrapper
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    sfEtaleCompactProjectionInverse A c M K = inv (sfCompactProjection A c M K) := rfl

section CompositionProof

set_option backward.isDefEq.respectTransparency true
attribute [-instance] ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local irreducible] projectionMapOfCompactification derivedTensor
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

/-- Composition coherence for the graph-normalized compositor and inverse
projections. -/
theorem sfEtaleCompactProjectionInverse_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g))
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    sfEtaleCompactProjectionInverse A ch M K ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z).map
        ((sfGraphCompactSupportCompIso A f g cf cg ch).hom.app M)).app K =
    (sfGraphCompactSupportCompIso A f g cf cg ch).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((L(upperStar (ModuleCat.{u + 1} A) (f ≫ g))).obj K)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (sfEtaleCompactProjectionInverse A cf M
          ((L(upperStar (ModuleCat.{u + 1} A) g)).obj K)) ≫
      sfEtaleCompactProjectionInverse A cg
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) K := by
  rw [inverse_projection_wrapper, inverse_projection_wrapper, inverse_projection_wrapper]
  have h := sfEtaleCompactProjectionForward_composition A f g cf cg ch M K
  dsimp only at h
  rw [(rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map_inv]
  apply inverse_graph_projection_square
  exact h

end CompositionProof

end AlgebraicGeometry.Etale
