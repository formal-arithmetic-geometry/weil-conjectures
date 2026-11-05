/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Trivial lisse sheaves on a connected scheme

On a connected scheme `V` a locally finite continuous function `V → ℚ̄_ℓ` is constant, `ℚ̄_ℓ`
being totally disconnected (`PadicAlgCl.locallyFiniteFunctionsEquiv`). Hence a morphism
`ℚ̄_ℓ,V^ι ⟶ ℚ̄_ℓ,V^κ` of trivial lisse sheaves is a `κ × ι` matrix over `ℚ̄_ℓ`, compatibly with
composition (`AlgebraicGeometry.ProEtale.AdicSheaf.freeHomEquiv`): this is the full faithfulness,
on trivial representations, of the correspondence between lisse sheaves and continuous
`π₁`-representations (Bhatt–Scholze, §7).
-/

@[expose] public section

universe u

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

/-- A locally finite function on a preconnected space is constant. -/
lemma locallyFiniteFunctions_apply_eq [PreconnectedSpace T] (f : locallyFiniteFunctions l T)
    (x y : T) : f.1 x = f.1 y :=
  (isPreconnected_univ.image f.1 f.1.continuous.continuousOn).subsingleton
    ⟨x, trivial, rfl⟩ ⟨y, trivial, rfl⟩

lemma locallyFiniteFunctions_eq_algebraMap [PreconnectedSpace T] (f : locallyFiniteFunctions l T)
    (x : T) : f = algebraMap (PadicAlgCl l) (locallyFiniteFunctions l T) (f.1 x) :=
  Subtype.ext (ContinuousMap.ext fun y ↦ locallyFiniteFunctions_apply_eq f y x)

variable (l T) in
/-- On a connected space the locally finite functions are the constants. -/
noncomputable def locallyFiniteFunctionsEquiv [ConnectedSpace T] :
    locallyFiniteFunctions l T ≃ₐ[PadicAlgCl l] PadicAlgCl l :=
  (AlgEquiv.ofBijective (Algebra.ofId (PadicAlgCl l) (locallyFiniteFunctions l T))
    ⟨fun a b h ↦ by
      have x : T := Classical.arbitrary T
      simpa using congrArg (fun f : locallyFiniteFunctions l T ↦ f.1 x) h,
    fun f ↦ ⟨f.1 (Classical.arbitrary T),
      (locallyFiniteFunctions_eq_algebraMap f _).symm⟩⟩).symm

end PadicAlgCl

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.AdicSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

variable {l : ℕ} [Fact l.Prime] {V : Scheme.{u}} [ConnectedSpace V]
  {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]

end AlgebraicGeometry.ProEtale.AdicSheaf
