/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Filtered presentations by finite constructible complex hearts

Source: blueprint latest, sec-six-functors-basics/sk-prop-ind-heart,
sk-prop-ind-heart.proof.md, filtered-colimit heart construction, and the finite-complex
formulation of lem-sfb-finite-complex-heart-filtered-approximation
(blueprint: def-sfb-finite-constructible-complex-heart-presentations).

The complexes have arbitrary module differentials. Their zeroth cohomology modules
are the finite stages; arrows of the filtered presentation are arbitrary module maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- A cochain complex with finite support and finite constant scalar-model constructible
terms. No condition is imposed on its actual module-sheaf differentials.
Source: finite-complex formulation of lem-sfb-finite-complex-heart-filtered-approximation,
second paragraph (blueprint: def-sfb-finite-constructible-complex-heart-presentations). -/
def IsFiniteConstantConstructibleComplex
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) : Prop :=
  (∃ s : Finset ℤ, ∀ n : ℤ, n ∉ s → IsZero (K.X n)) ∧
    ∀ n : ℤ, IsConstantModelConstructible Λ X (K.X n)

/-- The replete class of zeroth cohomology modules of finite constructible complexes.
No constructibility condition is imposed on the resulting cohomology module.
Source: finite-complex formulation of lem-sfb-finite-complex-heart-filtered-approximation,
definition of N_K (blueprint: def-sfb-finite-constructible-complex-heart-presentations). -/
def finiteConstructibleComplexHearts :
    ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  fun N ↦ ∃ K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ,
    IsFiniteConstantConstructibleComplex Λ X K ∧ Nonempty (N ≅ K.homology 0)

/-- The replete class of small filtered ambient colimits of the modules N_K.
Mathlib's `ObjectProperty.ind` uses diagrams of modules, so no lift of their arrows
to chain maps is required. The indexing universe is `u + 1`, shared by all presentations.
Source: finite-complex formulation of lem-sfb-finite-complex-heart-filtered-approximation,
definition of I_X (blueprint: def-sfb-finite-constructible-complex-heart-presentations). -/
def indFiniteConstructibleComplexHearts :
    ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ObjectProperty.ind.{u + 1} (finiteConstructibleComplexHearts Λ X)

end AlgebraicGeometry.ProEtale
