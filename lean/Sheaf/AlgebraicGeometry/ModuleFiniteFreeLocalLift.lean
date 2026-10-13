/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # Local finite free lifting

Source: Stacks Project, Modules, Tags 01B5 and 01B8.
(blueprint: lem-weil-pbc-module-finite-free-local-lift).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type target of an epimorphism admits, near each point, a finite free
map to the source whose composite is still an epimorphism.

Source: Stacks Project, Modules, Definition 01B5 and Lemma 01B8.
(blueprint: lem-weil-pbc-module-finite-free-local-lift).

Proof: On K choose finite local generators for H using its finite type hypothesis.
Each generator lifts locally through p, since an epimorphism of module sheaves
is locally surjective. Intersect the finitely many lifting neighbourhoods.
The lifts define a map from the finite free sheaf, and its composite with p is
precisely the restricted generating map, hence epi. Restriction preserves free
sheaves and epimorphisms. The slice over V and its further slice over U give
exactly the displayed restriction functor. With no generators use the zero map
from the free sheaf on Fin 0: the target is zero on the chosen neighbourhood.
There is no point to consider on empty K. No finite presentation is required. -/
theorem exists_finite_free_local_lift
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (p : G ⟶ H.over V) [Epi p] (x : K) :
    ∃ (U : X.Opens) (hUK : U ≤ K), (x : X) ∈ U ∧ ∃ (n : ℕ)
      (l : free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n)) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hUK.trans hKV))).obj G),
      Epi (l ≫ (overMap (moduleRings X.toRingedSpace)
        (homOfLE (hUK.trans hKV))).map p) := by sorry

end AlgebraicGeometry.Scheme.Modules
