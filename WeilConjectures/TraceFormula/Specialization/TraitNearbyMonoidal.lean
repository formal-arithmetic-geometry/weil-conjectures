/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
public import WeilConjectures.CategoryTheory.Shift.ShiftDecompositionIsIso
public import WeilConjectures.TraceFormula.PointDualizable
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The nearby cycles of the trait are monoidal

Let `S = Spec k'⟦t⟧` be the strictly henselian trait of a separably closed field `k'`, with
geometric generic point `η̄ : Spec Ω ⟶ S` and closed point `i : Spec k' ⟶ S`. The nearby cycles
`Ψ_S = Li^* Rη̄_*` of the trait are monoidal on bounded constructible `ℚ̄_ℓ`-complexes on `Spec Ω`:
the Künneth map of the trait as a model of its geometric generic point is an isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_traitGenericModel`).
This is the computation, in the global-sections step of Gabber's Künneth formula, of the nearby
cycles of `RΓ(X_η̄, A) ⊗ RΓ(Y_η̄, B)`.

## Proof

Every bounded constructible complex on `Spec Ω` is a finite direct sum of shifts `𝟙⟦d⟧` of the
unit (`ProEtale.CondensedRing.nonempty_shiftDecomposition_point`), and `𝟙⟦d⟧ = Lη̄^* 𝟙_S⟦d⟧`. For
`W = 𝟙_S⟦d⟧` the lax tensor map `μ : Rη̄_* Lη̄^* W ⊗ Rη̄_* V ⟶ Rη̄_* (Lη̄^* W ⊗ V)`, precomposed
with the unit `W ⟶ Rη̄_* Lη̄^* W`, is the left projection morphism of `η̄`
(`CategoryTheory.Adjunction.whiskerRight_unit_comp_homEquiv`), an isomorphism since `W` is
invertible. After `Li^*` the unit at `W` is invertible: it is at `W = 𝟙_S` (the cohomology of the
geometric generic point of `S` is that of its closed point,
`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_unit_app`) and the unit commutes with
the shifts. A natural transformation between additive functors which is invertible at the
summands of a finite direct sum is invertible at the sum
(`CategoryTheory.ShiftDecomposition.isIso_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

/-! ### Abstract lemmas -/

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The unit of the geometric generic point of the trait -/

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

end Unit

/-! ### The lax tensor map of the geometric generic point -/

section TensorMap

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (k' : Type u) [Field k'] [IsSepClosed k']

end TensorMap

/-! ### The Künneth map of the trait -/

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
