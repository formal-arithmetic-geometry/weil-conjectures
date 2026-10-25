/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityMap
public import WeilConjectures.TraceFormula.Specialization.NearbyKunneth

/-!

# Nearby cycles commute with Verdier duality

Let `M` be a model of finite type over the strictly henselian trait `S = Spec k'⟦t⟧` of a
separated `k`-scheme `X` of finite type, with special fibre the `k'`-scheme `X'`, whose geometric
generic fibre is the base change `X_Ω` of `X` to `Ω` and whose identification `ε : X_Ω ⟶ X` factors
through the total space. Its nearby cycles `Ψ = Li^* Rj_* Lε^*` carry the lax tensor map
`μ_Ψ : Ψ A ⊗ Ψ B ⟶ Ψ (A ⊗ B)` (`NearbyCyclesModel.tensorMap`), which restricts to bounded
constructible complexes (`NearbyCyclesModel.boundedConstructibleTensorMap`). For a dualizing map
`θ : Ψ ω_X ⟶ ω_{X'}` the duality map
```
δ_K : Ψ D_X K ⟶ D_{X'} Ψ K
```
is the adjoint of `θ ∘ Ψ(ev) ∘ μ_Ψ` (`CategoryTheory.Verdier.nearbyDualityMap`).

**Gabber's theorem** (Illusie, *Autour du théorème de monodromie locale*, Thm. 4.2; blueprint
`sk-prop-tf-nearby-duality-foundation`) says that for the dualizing map `θ_X = β_{a_X}(ℚ̄_ℓ)` of the
exceptional exchange, `δ_K` is an isomorphism for every bounded constructible `K`. Here `D_X` is
relative to `k`; it is identified with the duality relative to `Ω` on the geometric generic fibre
since `ε` is a base change of fields, and this identification is absorbed into `θ`.

The exceptional exchange `β` is not available for nearby-cycles models: it requires the
compact-support exchange `ν_f`, built from relative compactifications over the trait (blueprint
`det-nearby-exchange-maps`). So the theorem is stated with the dualizing map existentially
quantified (`NearbyCyclesModel.exists_isIso_nearbyDualityMap`), and it remains unproven; see its
docstring. The formal parts of the blueprint proof (compatibility of `δ` with proper direct images
and open restrictions, normalization on the trait, and the finite-group core of the invariants
step) are `CategoryTheory.Verdier.nearbyDualityMap_proper`,
`CategoryTheory.Verdier.nearbyDualityMap_restrict`,
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` and
`CategoryTheory.invariantsDualIso`.

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

variable (ℓ) [IsSepClosed k'] [Algebra k k']

/-- **Gabber's theorem: nearby cycles commute with Verdier duality** (Illusie, *Autour du
théorème de monodromie locale*, Thm. 4.2; SGA 7 XIII; blueprint
`sk-prop-tf-nearby-duality-foundation`). Let `M` be a model of finite type over the strictly
henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed) of a separated `k`-scheme `X` of finite
type, with special fibre `X'`, such that
* the identification `ε : 𝒳_Ω ⟶ X` factors through the total space, `ε = j ≫ e` (so the complexes
  `Lε^* K` come from the generic fibre `𝒳_η`, the setting of SGA 7 XIII);
* the geometric generic fibre is the base change `X ×_k Spec Ω` along `Spec Ω ⟶ S ⟶ Spec k`, with
  `ε` the first projection (so `Lε^* D_{X/k} ≅ D_{𝒳_Ω/Ω} Lε^*` on bounded constructible complexes,
  Verdier duality commuting with extension of the base field).

Then there is a dualizing map `θ : Ψ ω_{X/k} ⟶ ω_{X'/k'}` for which the duality map
`δ_K : Ψ D_X K ⟶ D_{X'} Ψ K`, adjoint to `θ ∘ Ψ(ev) ∘ μ_Ψ`, is an isomorphism for every bounded
constructible `K`: namely `θ = θ_𝒳 ∘ Ψ(Lε^* ω_X ≅ ω_{𝒳_Ω})` with `θ_𝒳 = β_{a_𝒳}(ℚ̄_ℓ)` the
dualizing map of the exceptional exchange (blueprint `det-nearby-exchange-maps` (5)). There is no
Tate twist: the duality on the geometric generic fibre is relative to `Ω`, the one on the special
fibre relative to `k'`. The blueprint node is stated for finite `ℓ`-primary coefficients and
`D^b_ctf`; for bounded constructible `ℚ̄_ℓ`-complexes the canonical map is the limit of the finite
ones (Bhatt–Scholze, §6.8).

Unfinished. The proof of the blueprint (open locality and compactification, compatibility of
`δ` with proper direct image and global duality, generic slicing with the twist `ℚ̄_ℓ(1)[2]`,
invariants under the wild inertia `P`, finite support and induction on the dimension) needs the
compact-support exchange `ν_f` for nearby cycles over the trait, which is not formalised: it
requires relative compactifications of the total spaces over the trait together with the proper
and open exchanges, and the deformation to the normal cone of a point is not proper over the
trait even for proper `X`. Its formal ingredients are proved:
`CategoryTheory.Verdier.nearbyDualityMap_proper`,
`CategoryTheory.Verdier.nearbyDualityMap_restrict`,
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` (blueprint
`det-tf-nearby-duality-proper`) and `CategoryTheory.invariantsDualIso`,
`CategoryTheory.uncurry_invariantsDualIso_hom` (blueprint `det-tf-invariants-duality`, finite
group case). -/
theorem exists_isIso_nearbyDualityMap {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
    (hε : ∃ e : M.total ⟶ X.left, M.j ≫ e = M.ε)
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    ∃ θ : (boundedConstructibleNearbyCycles hP).obj (dualizingComplex ℓ (toPoint X)) ⟶
        dualizingComplex ℓ (toPoint X'),
      ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        IsIso (Verdier.nearbyDualityMap (boundedConstructibleTensorMap hP) θ K) :=
  sorry

/-- **Nearby cycles commute with Verdier duality**: under the hypotheses of
`NearbyCyclesModel.exists_isIso_nearbyDualityMap`, `Ψ(D_X K) ≅ D_{X'}(Ψ K)` for every bounded
constructible `K`, the duality being relative to `k` on `X` and to `k'` on the special fibre. -/
theorem nonempty_nearbyCycles_verdierDual_iso {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
    (hε : ∃ e : M.total ⟶ X.left, M.j ≫ e = M.ε)
    (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k'))
    (hP : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Nonempty ((boundedConstructibleNearbyCycles hP).obj (verdierDual ℓ (toPoint X) K) ≅
      verdierDual ℓ (toPoint X') ((boundedConstructibleNearbyCycles hP).obj K)) := by
  obtain ⟨θ, hθ⟩ := exists_isIso_nearbyDualityMap ℓ hM hε hgen hP
  have := hθ K
  exact ⟨asIso (Verdier.nearbyDualityMap (boundedConstructibleTensorMap hP) θ K)⟩

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
