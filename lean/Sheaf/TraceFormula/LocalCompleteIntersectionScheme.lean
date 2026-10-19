/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion

/-!
# Schemes locally complete intersection over a field

Source: Stacks Project, Algebra, Definition 10.135.1 (Tag 00S9), and
Morphisms, Tags 01UG/01UF (blueprint: def-trf-local-complete-intersection-scheme-over-field).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The local-complete-intersection condition after the field extension `φ`, expressed on
an affine cover of `X`. The base-changed charts have coordinate rings `Ω ⊗[k] Γ(X, U i)`;
thus this is the affine-cover formulation of the same scheme condition, even when `Ω`
lives in a larger universe than `X`. No scalar-extension scheme is chosen.
Source: Stacks Project, Morphisms, Tag 01UG (lemma-local-complete-intersection),
Schemes, Tags 01JR/01JQ (base change of affine opens), and Algebra, Tag 00SJ
(blueprint: def-trf-local-complete-intersection-scheme-over-field). -/
def IsLocalCompleteIntersectionOverExtension (k : Type u) [Field k]
    (X : Scheme.{u}) (structureMap : X ⟶ Spec (CommRingCat.of k))
    (Ω : Type (max u v)) [Field Ω] (φ : k →+* Ω) : Prop :=
  letI : Algebra k Ω := φ.toAlgebra
  ∃ (ι : Type u) (U : ι → X.Opens),
    (⨆ i, U i) = ⊤ ∧
      (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, let e : U i ≤ structureMap ⁻¹ᵁ ⊤ := by simp
        letI : Algebra k Γ(X, U i) :=
          (((structureMap.appLE ⊤ (U i) e).hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra)
        ∃ hft : Algebra.FiniteType Ω (Ω ⊗[k] Γ(X, U i)),
          letI := hft
          Algebra.IsLocalCompleteIntersection Ω (Ω ⊗[k] Γ(X, U i)))

end AlgebraicGeometry
