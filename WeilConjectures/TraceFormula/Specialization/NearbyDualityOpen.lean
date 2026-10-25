/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.TraceFormula.Specialization.NearbyDuality

/-!

# Nearby duality and open restriction: the concrete inputs

The compatibility of the duality map of nearby cycles with open restriction (blueprint
`det-tf-nearby-duality-proper` (2)) is the abstract identity
`CategoryTheory.Verdier.nearbyDualityMap_restrict_natTrans`. This file proves its concrete inputs
for trait models:
* the duality map of `(G, μ_G, e)` for a lax monoidal `G` is the internal-hom comparison of `G`
  followed by `e` (`CategoryTheory.Verdier.nearbyDualityMap_eq_ihomComparison`), so for an open
  immersion it is invertible by
  `ProEtale.CondensedRing.isIso_ihomComparison_boundedConstructibleUpperStar_of_isOpenImmersion`;
* the lax tensor map of nearby cycles on bounded constructible complexes is natural
  (`NearbyCyclesModel.boundedConstructibleTensorMap_natural`);
* the restricted pullback exchange is monoidal, in the lax form used there
  (`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_tensor`), from the ambient
  monoidality `NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`.

The remaining inputs are the invertibility of the pullback exchange for open immersions
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`) and the compatibility of the
dualizing maps with open restriction
(`NearbyCyclesModel.NearbyDualizingData.map_θ_comp_dualizingComplexUpperStarIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

namespace Verdier

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]

/-- For a lax monoidal functor `G` and `e : G W ⟶ W'`, the duality map of `(G, μ_G, e)` is the
comparison `G [X, W] ⟶ [G X, G W] ⟶ [G X, W']` of internal homs followed by `e`. -/
lemma nearbyDualityMap_eq_ihomComparison (G : C ⥤ D) [G.LaxMonoidal] {W : C} {W' : D}
    (e : G.obj W ⟶ W') (X : C) :
    nearbyDualityMap (Functor.LaxMonoidal.μ G) e X =
      (Functor.LaxMonoidal.ihomComparison G X).natTrans.app W ≫ (ihom (G.obj X)).map e := by
  apply uncurry_injective
  rw [uncurry_nearbyDualityMap, uncurry_natural_right, uncurry_eq, Category.assoc,
    Functor.LaxMonoidal.ihomComparison_ev_assoc]

omit [MonoidalClosed C] in
/-- An exchange `α : F' Ψ_X ⟶ Ψ_U F` between strong monoidal functors which is monoidal in the
oplax form `Ψ_U(δ_F) ∘ α ∘ F'(μ_X) = μ_U ∘ (α ⊗ α) ∘ δ_{F'}` is monoidal in the lax form. -/
lemma lax_of_oplax_aux {C' U U' : Type*} [Category* C'] [MonoidalCategory C'] [Category* U]
    [MonoidalCategory U] [Category* U'] [MonoidalCategory U'] {ΨX : C ⥤ C'} {ΨU : U ⥤ U'}
    {F : C ⥤ U} {F' : C' ⥤ U'} [F.Monoidal] [F'.Monoidal]
    (μX : ∀ A B : C, ΨX.obj A ⊗ ΨX.obj B ⟶ ΨX.obj (A ⊗ B))
    (μU : ∀ A B : U, ΨU.obj A ⊗ ΨU.obj B ⟶ ΨU.obj (A ⊗ B))
    (α : ∀ A : C, F'.obj (ΨX.obj A) ⟶ ΨU.obj (F.obj A)) (A B : C)
    (h : F'.map (μX A B) ≫ α (A ⊗ B) ≫ ΨU.map (Functor.OplaxMonoidal.δ F A B) =
      Functor.OplaxMonoidal.δ F' _ _ ≫ (α A ⊗ₘ α B) ≫ μU _ _) :
    (α A ⊗ₘ α B) ≫ μU _ _ ≫ ΨU.map (Functor.LaxMonoidal.μ F A B) =
      Functor.LaxMonoidal.μ F' _ _ ≫ F'.map (μX A B) ≫ α (A ⊗ B) := by
  rw [← Category.id_comp ((α A ⊗ₘ α B) ≫ _), ← Functor.Monoidal.μ_δ F', Category.assoc,
    ← reassoc_of% h, ← ΨU.map_comp, Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id,
    Category.comp_id]

end Verdier

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

omit [Fact (ringChar k).Prime] [Fact (ringChar k').Prime] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] in
/-- The lax tensor map of nearby cycles on bounded constructible complexes is natural. -/
lemma boundedConstructibleTensorMap_natural
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    {A A' B B' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (x : A ⟶ A') (y : B ⟶ B') :
    ((boundedConstructibleNearbyCycles hP).map x ⊗ₘ (boundedConstructibleNearbyCycles hP).map y) ≫
        boundedConstructibleTensorMap hP A' B' =
      boundedConstructibleTensorMap hP A B ≫ (boundedConstructibleNearbyCycles hP).map (x ⊗ₘ y) :=
  ObjectProperty.hom_ext _ (M.tensorMap_natural _ x.hom y.hom)

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} (φ : N.Hom M j.left j'.left)

/-- The restricted pullback exchange is `NearbyCyclesModel.liftExchange` of the ambient one. -/
lemma Hom.boundedConstructiblePullbackExchange_eq_liftExchange'
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    (hN : N.PreservesBoundedConstructible Λ) (hM : M.PreservesBoundedConstructible Λ) :
    φ.boundedConstructiblePullbackExchange ℓ hN hM =
      liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) (φ.pullbackExchange Λ)
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ j' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj Λ ℓ j K.obj K.property) :=
  rfl

/-- The comparison `μ` of the restricted pullback is that of the ambient derived pullback. -/
lemma μ_boundedConstructibleUpperStar_hom {Z W : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom] (f : Z ⟶ W)
    (A B : Dᵇc(W.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
      A B).hom = Functor.LaxMonoidal.μ L((f.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A.obj B.obj :=
  rfl

/-- The monoidality of `NearbyCyclesModel.liftExchange` of an arbitrary transformation
`α : Ψ_M ⋙ Lj'^* ⟶ Lj^* ⋙ Ψ_N`, deduced from that of `α`; the transformation is kept abstract so
that the kernel never unfolds the pullback exchange. -/
private lemma liftExchange_tensor_aux
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (α : M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
        L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙ N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (hα : ∀ A B, L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
        (M.tensorMap (Profinite.padicAlgClRingObj ℓ) A B) ≫ α.app (A ⊗ B) ≫
          (N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
            (Functor.OplaxMonoidal.δ L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) A B) =
      Functor.OplaxMonoidal.δ L((j'.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) _ _ ≫
        (α.app A ⊗ₘ α.app B) ≫ N.tensorMap (Profinite.padicAlgClRingObj ℓ) _ _)
    (β : boundedConstructibleNearbyCycles hM ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j' ⟶
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
          boundedConstructibleNearbyCycles hN)
    (hβ : β = liftExchange (PY := boundedConstructible _) (PX := boundedConstructible _)
        (PY' := boundedConstructible _) (PX' := boundedConstructible _) α
        (fun K ↦ hM K.obj K.property) (fun K ↦ hN K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ j' K.obj K.property)
        (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ j K.obj K.property))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (β.app A ⊗ₘ β.app B) ≫ boundedConstructibleTensorMap hN _ _ ≫
        (boundedConstructibleNearbyCycles hN).map (Functor.LaxMonoidal.μ
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j')
          _ _ ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
          (boundedConstructibleTensorMap hM A B) ≫ β.app (A ⊗ B) := by
  subst hβ
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    μ_boundedConstructibleUpperStar_hom, ObjectProperty.tensorHom_hom', liftExchange_app_hom]
  exact Verdier.lax_of_oplax_aux (M.tensorMap _) (N.tensorMap _) (fun A ↦ α.app A) A.obj B.obj
    (hα A.obj B.obj)

/-- **The pullback exchange is monoidal on bounded constructible complexes**: the restriction of
`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`, in the lax form. -/
lemma Hom.boundedConstructiblePullbackExchange_tensor
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app A ⊗ₘ
        (φ.boundedConstructiblePullbackExchange ℓ hN hM).app B) ≫
        boundedConstructibleTensorMap hN _ _ ≫
          (boundedConstructibleNearbyCycles hN).map (Functor.LaxMonoidal.μ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j')
          _ _ ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
          (boundedConstructibleTensorMap hM A B) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hN hM).app (A ⊗ B) :=
  liftExchange_tensor_aux hN hM (φ.pullbackExchange _)
    (φ.map_tensorMap_comp_pullbackExchange_app _) _
    (φ.boundedConstructiblePullbackExchange_eq_liftExchange' hN hM) A B

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
