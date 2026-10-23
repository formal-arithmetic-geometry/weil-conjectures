/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-!

# Stalks of the pushforward along a finite étale morphism

Let `f : X ⟶ Y` be a finite étale morphism and `ȳ : P ⟶ Y` a geometric point, that is `P` is
the spectrum of a separably closed field `Ω`. For a module object `F` on `X_proét`, the stalk
`ȳ^* f_* F` of the pushforward is the product of the stalks `x̄^* F` over the points
`x̄ : P ⟶ X` over `ȳ` (`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`). The projection to
the factor of `x̄` is `ȳ^* f_* F = (x̄ ≫ f)^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F`, through the counit
of `f^* ⊣ f_*` (`ProEtale.CondensedRing.stalkLowerStarProj`).

The statements are made for a scheme `P` with an isomorphism `P ≅ Spec Ω` rather than for
`Spec Ω` itself, so that they apply to `Spec (AlgebraicClosure k)` with the ring structure of
`AlgebraicClosure k` found by instance search; the two ring structures on `AlgebraicClosure k`
(as a commutative ring and through its field structure) agree only up to unfolding.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Fibre

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y P : Scheme.{u}} (f : X ⟶ Y) (y : P ⟶ Y)

/-- The `P`-valued points `x̄ : P ⟶ X` over a `P`-valued point `ȳ : P ⟶ Y`. -/
abbrev FibrePoints : Type u :=
  {x : P ⟶ X // x ≫ f = y}

/-- A finite morphism has finitely many geometric points over a geometric point. -/
theorem finite_fibrePoints [IsFinite f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (eP : P ≅ Spec (.of Ω)) : Finite (FibrePoints f y) :=
  have : Finite (f.GeometricFiber (eP.inv ≫ y)) := inferInstance
  Finite.of_injective
    (fun x : FibrePoints f y ↦ (⟨eP.inv ≫ x.1, by rw [Category.assoc, x.2]⟩ :
      f.GeometricFiber (eP.inv ≫ y)))
    fun a b h ↦ Subtype.ext (by
      simpa using congrArg (fun z : f.GeometricFiber (eP.inv ≫ y) ↦ eP.hom ≫ z.1) h)

variable {f y}

/-- The projection `ȳ^* f_* F ⟶ x̄^* F` of the stalk of the pushforward at `ȳ` to the stalk at a
point `x̄` over `ȳ`: the composite `ȳ^* f_* F = (x̄ ≫ f)^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F` of the
composition isomorphism and the counit of `f^* ⊣ f_*`. -/
noncomputable def stalkLowerStarProj {x : P ⟶ X} (hx : x ≫ f = y)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (y)^*⟦Λ⟧.obj ((f)_*⟦Λ⟧.obj F) ⟶ (x)^*⟦Λ⟧.obj F :=
  eqToHom (by rw [← hx]) ≫ (upperStarComp Λ x f).hom.app _ ≫
    (x)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ f).counit.app F)

variable (f y)

/-- **The stalk of a finite étale pushforward** at a geometric point `ȳ : P ⟶ Y`,
`P ≅ Spec Ω` with `Ω` separably closed: `ȳ^* f_* F` is the product of the stalks `x̄^* F` over the
points `x̄ : P ⟶ X` over `ȳ`, with the projections `stalkLowerStarProj`. -/
theorem isLimit_stalkLowerStarFan [IsFinite f] [Etale f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (eP : P ≅ Spec (.of Ω))
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty (IsLimit (Fan.mk ((y)^*⟦Λ⟧.obj ((f)_*⟦Λ⟧.obj F))
      fun x : FibrePoints f y ↦ stalkLowerStarProj Λ x.2 F)) :=
  sorry

end Fibre

end AlgebraicGeometry.ProEtale.CondensedRing
