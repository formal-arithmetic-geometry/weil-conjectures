/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!

# Stalks of the pushforward along a finite étale morphism

Let `f : X ⟶ Y` be a finite étale morphism and `ȳ : Spec Ω ⟶ Y` a geometric point, `Ω`
separably closed. For a module object `F` on `X_proét`, the stalk `ȳ^* f_* F` of the pushforward
is the product of the stalks `x̄^* F` over the geometric points `x̄ : Spec Ω ⟶ X` over `ȳ`
(`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`). The projection to the factor of `x̄` is
`ȳ^* f_* F = (x̄ ≫ f)^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F`, through the counit of `f^* ⊣ f_*`
(`ProEtale.CondensedRing.stalkLowerStarProj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Fibre

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The geometric points `x̄ : Spec Ω ⟶ X` over a geometric point `ȳ : Spec Ω ⟶ Y`. -/
abbrev GeometricFibre : Type u :=
  {x : Spec (.of Ω) ⟶ X // x ≫ f = y}

/-- A finite morphism has finitely many geometric points over a geometric point. -/
instance finite_geometricFibre [IsFinite f] [IsSepClosed Ω] : Finite (GeometricFibre f y) :=
  sorry

variable {f y}

/-- The projection `ȳ^* f_* F ⟶ x̄^* F` of the stalk of the pushforward at `ȳ` to the stalk at a
point `x̄` over `ȳ`: the composite `ȳ^* f_* F = (x̄ ≫ f)^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F` of the
composition isomorphism and the counit of `f^* ⊣ f_*`. -/
noncomputable def stalkLowerStarProj {x : Spec (.of Ω) ⟶ X} (hx : x ≫ f = y)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (y)^*⟦Λ⟧.obj ((f)_*⟦Λ⟧.obj F) ⟶ (x)^*⟦Λ⟧.obj F :=
  eqToHom (by rw [← hx]) ≫ (upperStarComp Λ x f).hom.app _ ≫
    (x)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ f).counit.app F)

variable (f y)

/-- **The stalk of a finite étale pushforward** at a geometric point `ȳ`, `Ω` separably closed:
`ȳ^* f_* F` is the product of the stalks `x̄^* F` over the geometric points `x̄` over `ȳ`, with the
projections `stalkLowerStarProj`. -/
theorem isLimit_stalkLowerStarFan [IsFinite f] [Etale f] [IsSepClosed Ω]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty (IsLimit (Fan.mk ((y)^*⟦Λ⟧.obj ((f)_*⟦Λ⟧.obj F))
      fun x : GeometricFibre f y ↦ stalkLowerStarProj Λ x.2 F)) :=
  sorry

end Fibre

end AlgebraicGeometry.ProEtale.CondensedRing
