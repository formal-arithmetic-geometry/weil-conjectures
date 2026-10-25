/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityMap
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap

/-!

# Nearby cycles commute with Verdier duality

Let `M` be a trait model over the base (`NearbyCyclesModel.IsTraitModelOfBase`) of a separated
`k`-scheme `X` of finite type, over the strictly henselian trait `S = Spec k'⟦t⟧`, with special
fibre the `k'`-scheme `X'`. Its nearby cycles `Ψ = Li^* Rj_* Lε^*` carry the lax tensor map
`μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` (`NearbyCyclesModel.tensorMap`), which restricts to bounded
constructible complexes (`NearbyCyclesModel.boundedConstructibleTensorMap`), and the dualizing map
`θ_M = β_a(ℚ̄_ℓ) : Ψ ω_X ⟶ ω_{X'}` (`NearbyCyclesModel.nearbyDualizingData`, blueprint
`det-nearby-exchange-maps`). The **duality map** (`NearbyCyclesModel.nearbyDualityMap`)
```
δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K
```
is the adjoint of `θ_M ∘ Ψ(ev) ∘ μ_Ψ` (`CategoryTheory.Verdier.nearbyDualityMap`).

**Gabber's theorem** (Illusie, *Autour du théorème de monodromie locale*, Thm. 4.2; blueprint
`sk-prop-tf-nearby-duality-foundation`) says that `δ_{M,K}` is an isomorphism for every bounded
constructible `K` (`NearbyCyclesModel.isIso_nearbyDualityMap`). Here `D_X` is relative to `k`; it is
identified with the duality relative to `Ω` on the geometric generic fibre since `ε` is a base
change of fields, and this identification is part of `θ_M`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

/-- The lax tensor map `μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` of nearby cycles
(`NearbyCyclesModel.tensorMap`) on bounded constructible complexes. -/
noncomputable def boundedConstructibleTensorMap
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles hP).obj A ⊗ (boundedConstructibleNearbyCycles hP).obj B ⟶
      (boundedConstructibleNearbyCycles hP).obj (A ⊗ B) :=
  ObjectProperty.homMk (M.tensorMap (Profinite.padicAlgClRingObj ℓ) A.obj B.obj)

variable (ℓ) [IsSepClosed k'] [Algebra k k'] {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The **duality map** `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K` of a trait model `M` over the base
(blueprint `sk-prop-tf-nearby-duality-foundation`): the adjoint of `θ_M ∘ Ψ(ev) ∘ μ_Ψ`, with `θ_M`
the dualizing map `β_a(ℚ̄_ℓ)` (`NearbyCyclesModel.nearbyDualizingData`). -/
noncomputable def nearbyDualityMap (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
        (verdierDual ℓ (toPoint X) K) ⟶
      verdierDual ℓ (toPoint X') ((boundedConstructibleNearbyCycles
        (h.preservesBoundedConstructible ℓ)).obj K) :=
  Verdier.nearbyDualityMap (boundedConstructibleTensorMap (h.preservesBoundedConstructible ℓ))
    ((nearbyDualizingData k k' ℓ).θ h) K

/-- **Gabber's theorem: nearby cycles commute with Verdier duality** (Illusie, *Autour du
théorème de monodromie locale*, Thm. 4.2; SGA 7 XIII; blueprint
`sk-prop-tf-nearby-duality-foundation`). For a trait model `M` over the base of a separated
`k`-scheme `X` of finite type, over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably
closed), the duality map `δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K`, adjoint to `θ_M ∘ Ψ(ev) ∘ μ_Ψ` with the
dualizing map `θ_M = β_a(ℚ̄_ℓ)` of blueprint `det-nearby-exchange-maps`, is an isomorphism for
every bounded constructible `K`. There is no Tate twist: the duality on the geometric generic fibre
is relative to `Ω`, the one on the special fibre relative to `k'`. The blueprint node is stated for
finite `ℓ`-primary coefficients and `D^b_ctf`; for bounded constructible `ℚ̄_ℓ`-complexes the
canonical map is the limit of the finite ones (Bhatt–Scholze, §6.8).

Unfinished. The blueprint proof reduces, by open restriction and compactification, to proper
models, where global duality kills `RΓ` of the cone of `δ`, and concludes by generic slicing and
finite support. Its formal ingredients are proved: `CategoryTheory.Verdier.nearbyDualityMap_proper`,
`CategoryTheory.Verdier.nearbyDualityMap_restrict`,
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` (blueprint
`det-tf-nearby-duality-proper`) and `CategoryTheory.invariantsDualIso` (blueprint
`det-tf-invariants-duality`), and for open restriction the concrete inputs of
`WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen`. Instantiating the abstract
compatibilities on `Dᵇc` is blocked by an elaboration problem: the hypotheses stated for the
concrete functors and those obtained by instantiating the abstract statements differ in instance
terms (the monoidal structure of `Dᵇc(X)⟦ℚ̄_ℓ⟧` is reachable by two instance paths) and are only
identified after unfolding the condensed coefficient rings, which exceeds the heartbeat limits.
Compactification of trait models over `S`, generic slicing (`det-tf-nearby-duality-slice`) and
finite support are not formalised. -/
theorem isIso_nearbyDualityMap (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (nearbyDualityMap ℓ h K) :=
  sorry

/-- **Nearby cycles commute with Verdier duality**: for a trait model `M` over the base,
`Ψ(D_X K) ≅ D_{X'}(Ψ K)` for every bounded constructible `K`, the duality being relative to `k` on
`X` and to `k'` on the special fibre. -/
theorem nonempty_nearbyCycles_verdierDual_iso (h : M.IsTraitModelOfBase k q g)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
        (verdierDual ℓ (toPoint X) K) ≅
      verdierDual ℓ (toPoint X') ((boundedConstructibleNearbyCycles
        (h.preservesBoundedConstructible ℓ)).obj K)) :=
  have := isIso_nearbyDualityMap ℓ h K
  ⟨asIso (nearbyDualityMap ℓ h K)⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
