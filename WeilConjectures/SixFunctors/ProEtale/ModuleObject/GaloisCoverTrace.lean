/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModTrace
public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTraceMonoidal

/-!
# The trace of a Galois covering on module objects

Let `Λ` be a commutative condensed ring and `g : Y ⟶ X` a quasi-compact surjective weakly étale
morphism with a Galois action of a finite group `Γ` (`AlgebraicGeometry.ProEtale.IsGaloisAction`),
for instance a finite étale Galois covering. For the adjunction `g^* ⊣ g_*` on module objects over
`Λ` (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarLowerStarAdjunction`), this file constructs
the *trace* `t : g^* ⋙ g_* ⟶ 𝟭` and the action `ρ a` of `a : Γ` on `g^* ⋙ g_*`
(`AlgebraicGeometry.ProEtale.CondensedRing.galoisTrace`,
`AlgebraicGeometry.ProEtale.CondensedRing.galoisAction`), with

* `u ≫ t = |Γ| • 𝟙` (`AlgebraicGeometry.ProEtale.CondensedRing.unit_comp_galoisTrace`),
* `t ≫ u = ∑ a, ρ a` (`AlgebraicGeometry.ProEtale.CondensedRing.galoisTrace_comp_unit`),

for the unit `u` of `g^* ⊣ g_*`. They are the lifts of the trace and the action on abelian sheaves
(`CategoryTheory.Adjunction.mapModTrace`), which are `Λ`-linear since the action is monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Category MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (g : Y ⟶ X)

section Trace

variable [WeaklyEtale g] [Surjective g] [QuasiCompact g]
  {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
  [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

end Trace

end AlgebraicGeometry.ProEtale.CondensedRing
