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
constructible `K` (`NearbyCyclesModel.isIso_nearbyDualityMap`, reduced by open locality to affine
total spaces, `NearbyCyclesModel.isIso_nearbyDualityMap_of_isAffine`). Here `D_X` is relative
to `k`; it is identified with the duality relative to `Ω` on the geometric generic fibre since `ε`
is an open immersion into a base change of fields, and this identification is part of `θ_M`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

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
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    [IsEllAdicFinitenessCoefficient ℓ Λ] (hP : M.PreservesBoundedConstructible Λ)
    (A B : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleNearbyCycles hP).obj A ⊗ (boundedConstructibleNearbyCycles hP).obj B ⟶
      (boundedConstructibleNearbyCycles hP).obj (A ⊗ B) :=
  ObjectProperty.homMk (M.tensorMap Λ A.obj B.obj)

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

/-- **Gabber's theorem for affine total spaces** (Illusie, *Autour du théorème de monodromie
locale*, Thm. 4.2; SGA 7 XIII; blueprint `sk-prop-tf-nearby-duality-foundation`). For a trait
model `M` over the base of a separated `k`-scheme `X` of finite type, over the strictly henselian
trait `S = Spec k'⟦t⟧` (`k'` separably closed), whose total space is affine, the duality map
`δ_{M,K} : Ψ D_X K ⟶ D_{X'} Ψ K`, adjoint to `θ_M ∘ Ψ(ev) ∘ μ_Ψ` with the dualizing map
`θ_M = β_a(ℚ̄_ℓ)` of blueprint `det-nearby-exchange-maps`, is an isomorphism for every bounded
constructible `K`. There is no Tate twist: the duality on the geometric generic fibre is relative
to `Ω`, the one on the special fibre relative to `k'`. The blueprint node is stated for finite
`ℓ`-primary coefficients and `D^b_ctf`; for bounded constructible `ℚ̄_ℓ`-complexes the canonical
map is the limit of the finite ones (Bhatt–Scholze, §6.8). The general case is reduced to this one
by open locality (`NearbyCyclesModel.isIso_nearbyDualityMap`).

Unfinished. The remaining steps of the blueprint proof are the compactification of the affine
total space over `S` (with extension by zero of `K`), the compatibility of `δ` with proper direct
image and global duality (formal part `CategoryTheory.Verdier.nearbyDualityMap_proper`,
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper`), generic slicing with the twist
`ℚ̄_ℓ(1)[2]` (`det-tf-nearby-duality-slice`, with the finite-group core
`CategoryTheory.invariantsDualIso`) and the finite-support induction. -/
theorem isIso_nearbyDualityMap_of_isAffine (h : M.IsTraitModelOfBase k q g) [IsAffine M.total]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) : IsIso (nearbyDualityMap ℓ h K) :=
  sorry

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
