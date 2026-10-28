/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Topology.Algebra.ProPHaarIntegral
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapRingObjMap
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Fibrewise `ℓ`-adic Haar integration

Let `G` be a compact totally disconnected group all of whose open normal subgroups have index
invertible in `ℤ_[ℓ]` (e.g. a pro-`p` group for a prime `p ≠ ℓ`, see `ProPGroup.isUnit_index`),
and let `∫_G : C(G, ℤ_[ℓ]) → ℤ_[ℓ]` be its normalized Haar integral
(`ProPGroup.haarIntegralOfIsUnit`). This file constructs the fibrewise integral
```
C(T × G, ℤ_[ℓ]) → C(T, ℤ_[ℓ]),   f ↦ (t ↦ ∫_G f(t, ·))
```
for topological spaces `T`, the first step towards an `ℓ`-adic Haar trace for pro-étale torsors
under `G`.

The integral is `1`-Lipschitz for the sup norm (`ProPGroup.norm_haarIntegralOfIsUnit_le`), hence
continuous on `C(G, ℤ_[ℓ])` with its compact-open topology. Since `f ↦ f(t, ·)` is the
continuous map `ContinuousMap.curry f : C(T, C(G, ℤ_[ℓ]))`, the fibrewise integral is continuous
in `t`.

## Main definitions and results

* `ProPGroup.fibreHaarIntegral`: the `ℤ_[ℓ]`-linear map `C(T × G, ℤ_[ℓ]) → C(T, ℤ_[ℓ])`.
* `ProPGroup.fibreHaarIntegral_comp_prodMap`: naturality in `T`.
* `ProPGroup.fibreHaarIntegral_comp_fst`: it is a retraction of `f ↦ f ∘ pr₁`.
* `Profinite.fibreHaarIntegralNatTrans`: the natural transformation
  `C(- × G, ℤ_[ℓ]) ⟶ C(-, ℤ_[ℓ])` of functors `Profiniteᵒᵖ ⥤ ModuleCat ℤ_[ℓ]`, with section
  `Profinite.compFstNatTrans`.
* `Profinite.haarIntegralCondensedMap`: for `G : Type`, the morphism of condensed abelian groups
  `C(-, C(G, ℤ_[ℓ])) ⟶ C(-, ℤ_[ℓ])` given by postcomposition with `∫_G`; on sections over `S`
  it is the fibrewise integral under `C(S × G, ℤ_[ℓ]) ≃ C(S, C(G, ℤ_[ℓ]))`
  (`Profinite.haarIntegralCondensedMap_app_curry`). It is a retraction of the morphism induced
  by the constant functions `ℤ_[ℓ] → C(G, ℤ_[ℓ])`
  (`Profinite.continuousMapRingObjMap_const_comp_haarIntegralCondensedMap`).
-/

@[expose] public section

universe u

open CategoryTheory Filter Topology

namespace ProPGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {ℓ : ℕ} [Fact ℓ.Prime]

/-- The Haar integral is bounded by the sup norm. -/
theorem norm_haarIntegralOfIsUnit_le
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (f : C(G, ℤ_[ℓ])) : ‖haarIntegralOfIsUnit hG f‖ ≤ ‖f‖ :=
  le_of_tendsto (tendsto_cosetAverage_haarIntegralOfIsUnit hG f).norm
    (Eventually.of_forall fun U =>
      Subgroup.norm_cosetAverage_le (hG U) (norm_nonneg f) fun x => f.norm_coe_le_norm x)

/-- The Haar integral is continuous on `C(G, ℤ_[ℓ])` with the compact-open topology. -/
theorem continuous_haarIntegralOfIsUnit
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    Continuous (haarIntegralOfIsUnit hG) :=
  AddMonoidHomClass.continuous_of_bound (haarIntegralOfIsUnit hG) 1 fun f => by
    simpa using norm_haarIntegralOfIsUnit_le hG f

/-- The fibrewise Haar integral `C(T × G, ℤ_[ℓ]) → C(T, ℤ_[ℓ])`,
`f ↦ (t ↦ ∫_G f(t, g) dg)`. -/
noncomputable def fibreHaarIntegral
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (T : Type*) [TopologicalSpace T] : C(T × G, ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] C(T, ℤ_[ℓ]) where
  toFun f := ⟨fun t => haarIntegralOfIsUnit hG (f.curry t),
    (continuous_haarIntegralOfIsUnit hG).comp f.curry.continuous⟩
  map_add' f f' := ContinuousMap.ext fun t =>
    map_add (haarIntegralOfIsUnit hG) (f.curry t) (f'.curry t)
  map_smul' c f := ContinuousMap.ext fun t =>
    map_smul (haarIntegralOfIsUnit hG) c (f.curry t)

theorem fibreHaarIntegral_apply
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    {T : Type*} [TopologicalSpace T] (f : C(T × G, ℤ_[ℓ])) (t : T) :
    fibreHaarIntegral hG T f t = haarIntegralOfIsUnit hG (f.curry t) :=
  rfl

/-- The fibrewise Haar integral is natural in `T`. -/
theorem fibreHaarIntegral_comp_prodMap
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T'] (φ : C(T', T))
    (f : C(T × G, ℤ_[ℓ])) :
    fibreHaarIntegral hG T' (f.comp (φ.prodMap (ContinuousMap.id G))) =
      (fibreHaarIntegral hG T f).comp φ :=
  rfl

/-- The fibrewise Haar integral of a function independent of `g ∈ G` is the function itself. -/
theorem fibreHaarIntegral_comp_fst
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    {T : Type*} [TopologicalSpace T] (f : C(T, ℤ_[ℓ])) :
    fibreHaarIntegral hG T (f.comp ContinuousMap.fst) = f :=
  ContinuousMap.ext fun t => haarIntegralOfIsUnit_const hG (f t)

end ProPGroup

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The functor `T ↦ C(T, ℤ_[ℓ])` from profinite sets to `ℤ_[ℓ]`-modules, with restriction by
precomposition. -/
noncomputable def continuousMapModulePresheaf : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u} ℤ_[ℓ] where
  obj T := ModuleCat.of ℤ_[ℓ] C(T.unop, ℤ_[ℓ])
  map f := ModuleCat.ofHom (ContinuousMap.compRightAlgHom ℤ_[ℓ] ℤ_[ℓ] f.unop.hom.hom).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

variable (G : Type u) [TopologicalSpace G]

/-- The functor `T ↦ C(T × G, ℤ_[ℓ])` from profinite sets to `ℤ_[ℓ]`-modules, with restriction
by precomposition with `φ × id_G`. -/
noncomputable def continuousMapProdModulePresheaf : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u} ℤ_[ℓ] where
  obj T := ModuleCat.of ℤ_[ℓ] C(T.unop × G, ℤ_[ℓ])
  map f := ModuleCat.ofHom (ContinuousMap.compRightAlgHom ℤ_[ℓ] ℤ_[ℓ]
    (f.unop.hom.hom.prodMap (ContinuousMap.id G))).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Pulling back along the projection `T × G → T`: the natural transformation
`C(-, ℤ_[ℓ]) ⟶ C(- × G, ℤ_[ℓ])`, `f ↦ f ∘ pr₁`. -/
noncomputable def compFstNatTrans :
    continuousMapModulePresheaf.{u} ℓ ⟶ continuousMapProdModulePresheaf ℓ G where
  app T := ModuleCat.ofHom (ContinuousMap.compRightAlgHom ℤ_[ℓ] ℤ_[ℓ]
    (ContinuousMap.fst : C(T.unop × G, T.unop))).toLinearMap
  naturality _ _ _ := rfl

variable [Group G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {ℓ G}

/-- The fibrewise Haar integration as a natural transformation `C(- × G, ℤ_[ℓ]) ⟶ C(-, ℤ_[ℓ])`
of functors `Profiniteᵒᵖ ⥤ ModuleCat ℤ_[ℓ]`. -/
noncomputable def fibreHaarIntegralNatTrans
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    continuousMapProdModulePresheaf.{u} ℓ G ⟶ continuousMapModulePresheaf ℓ where
  app T := ModuleCat.ofHom (ProPGroup.fibreHaarIntegral hG T.unop)
  naturality _ _ _ := rfl

lemma fibreHaarIntegralNatTrans_app_apply
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (T : Profinite.{u}ᵒᵖ) (f : C(T.unop × G, ℤ_[ℓ])) :
    (fibreHaarIntegralNatTrans hG).app T f = ProPGroup.fibreHaarIntegral hG T.unop f :=
  rfl

/-- The fibrewise Haar integration is a retraction of the pullback along `T × G → T`. -/
lemma compFstNatTrans_comp_fibreHaarIntegralNatTrans
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    compFstNatTrans.{u} ℓ G ≫ fibreHaarIntegralNatTrans hG = 𝟙 _ := by
  ext T f
  exact ProPGroup.fibreHaarIntegral_comp_fst hG f

end Profinite

namespace Profinite

variable {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The Haar integral `∫_G : C(G, ℤ_[ℓ]) → ℤ_[ℓ]` induces, by postcomposition, a morphism of
condensed abelian groups `C(-, C(G, ℤ_[ℓ])) ⟶ C(-, ℤ_[ℓ])`. -/
noncomputable def haarIntegralCondensedMap
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    continuousMapRingObj.{u} C(G, ℤ_[ℓ]) ⟶ continuousMapRingObj ℤ_[ℓ] :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun a := ULift.up ⟨fun s => ProPGroup.haarIntegralOfIsUnit hG (a.down s),
            (ProPGroup.continuous_haarIntegralOfIsUnit hG).comp a.down.continuous⟩
          map_zero' := ULift.ext _ _ (ContinuousMap.ext fun _ =>
            map_zero (ProPGroup.haarIntegralOfIsUnit hG))
          map_add' a b := ULift.ext _ _ (ContinuousMap.ext fun s =>
            map_add (ProPGroup.haarIntegralOfIsUnit hG) (a.down s) (b.down s)) }
     naturality _ _ _ := rfl }⟩

lemma haarIntegralCondensedMap_app_apply
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, C(G, ℤ_[ℓ]))) :
    (haarIntegralCondensedMap hG).hom.app S a =
      ULift.up ⟨fun s => ProPGroup.haarIntegralOfIsUnit hG (a.down s),
        (ProPGroup.continuous_haarIntegralOfIsUnit hG).comp a.down.continuous⟩ :=
  rfl

/-- On sections over `S`, under `C(S × G, ℤ_[ℓ]) → C(S, C(G, ℤ_[ℓ]))`, `f ↦ f.curry`, the
morphism `haarIntegralCondensedMap` is the fibrewise Haar integral. -/
lemma haarIntegralCondensedMap_app_curry
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (S : Profinite.{u}ᵒᵖ) (f : C(S.unop × G, ℤ_[ℓ])) :
    (haarIntegralCondensedMap hG).hom.app S (ULift.up f.curry) =
      ULift.up (ProPGroup.fibreHaarIntegral hG S.unop f) :=
  rfl

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The constant functions `ℤ_[ℓ] → C(G, ℤ_[ℓ])` form a continuous ring homomorphism. -/
lemma continuous_algebraMap_continuousMap :
    Continuous (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ])) :=
  (ContinuousMap.const' : C(ℤ_[ℓ], C(G, ℤ_[ℓ]))).continuous

/-- The Haar integral is a retraction of the morphism of condensed rings
`ℤ_[ℓ]̲ ⟶ C(-, C(G, ℤ_[ℓ]))` induced by the constant functions. -/
lemma continuousMapRingObjMap_const_comp_haarIntegralCondensedMap
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    continuousMapRingObjMap.{u} (algebraMap ℤ_[ℓ] C(G, ℤ_[ℓ]))
        continuous_algebraMap_continuousMap ≫ haarIntegralCondensedMap hG = 𝟙 _ := by
  ext S a
  refine ULift.ext _ _ (ContinuousMap.ext fun s => ?_)
  exact ProPGroup.haarIntegralOfIsUnit_const hG (a.down s)

end Profinite
