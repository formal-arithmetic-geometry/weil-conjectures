/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.NNReal.Defs

/-! # Contractive extension from admissible scalar values

Source: Weil blueprint, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), scalar tame-kernel
finite-field projection input (blueprint: lem-sfb-contractive-extension-from-admissible-values).
This conditional scalar-extension auxiliary and its proof are agent-formulated;
the argument is absent from the blueprint itself. The external Ingleton reference
remains WANTED in the DAG source.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace LinearMap

/-- A contractive scalar-valued linear functional extends from any subspace if
every contractive partial functional admits all the scalar-value constraints
for each vector outside its domain. The scalar absolute value and vector norm
are the given nonnegative-real-valued functions, with their axioms explicit.

Source: Weil blueprint, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), agent scalar-extension
expansion (blueprint: lem-sfb-contractive-extension-from-admissible-values).
The following is the agent-formulated proof recorded in the DAG, not printed in
the blueprint; the external Ingleton scalar-extension reference remains WANTED.

Proof:
1. Fix W and f. For any bounded partial extension g on U containing W and any
   x outside U, the scalar-value hypothesis gives b with |b - g(z)| ≤ ‖x - z‖
   for every z in U.
2. Every vector of U + Kx has a unique expression u + a • x: an equality with
   unequal coefficients would imply x belongs to U. Define
   G(u + a • x) = g(u) + a * b. Additivity and scalar compatibility follow by
   adding expressions and scaling them, and the coefficient zero gives G|_U = g.
3. When a = 0 the bound is that of g. Otherwise put z = -a⁻¹ • u in U.
   Then u + a • x = a • (x - z) and G(u + a • x) = a * (b - g(z)).
   Multiplicativity, the constraint at z, and norm homogeneity give
   |G(u + a • x)| ≤ |a| * ‖x - z‖ = ‖u + a • x‖.
4. For nonnegative r and s, max(r,s) ≤ r+s, by considering r ≤ s or s ≤ r.
   Thus both given ultrametric inequalities imply ordinary triangle inequalities;
   the other absolute-value and norm axioms are already explicit hypotheses.
5. Apply lem-sfb-bounded-extension-zorn with C = 1. Step 4 supplies its triangle
   inequalities, 1 > 0 its constant hypothesis, and the bound on f its initial
   bound. Steps 1--3 give every required one-vector extension of every bounded
   partial extension containing W. Its global conclusion gives h extending f
   with |h(v)| ≤ 1 * ‖v‖ = ‖v‖. This uses no completeness, compactness,
   closedness, or dimension hypothesis.
-/
theorem exists_contractive_extension_of_admissible_values
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (scalarAbs : K → NNReal) (vectorNorm : V → NNReal)
    (habs_zero : ∀ a : K, scalarAbs a = 0 ↔ a = 0)
    (habs_one : scalarAbs 1 = 1)
    (habs_mul : ∀ a b : K, scalarAbs (a * b) = scalarAbs a * scalarAbs b)
    (habs_add : ∀ a b : K, scalarAbs (a + b) ≤ max (scalarAbs a) (scalarAbs b))
    (hnorm_zero : ∀ y : V, vectorNorm y = 0 ↔ y = 0)
    (hnorm_smul : ∀ (a : K) (y : V), vectorNorm (a • y) = scalarAbs a * vectorNorm y)
    (hnorm_add : ∀ y z : V, vectorNorm (y + z) ≤ max (vectorNorm y) (vectorNorm z))
    (hadmissible : ∀ (U : Submodule K V) (g : U →ₗ[K] K),
      (∀ z : U, scalarAbs (g z) ≤ vectorNorm (z : V)) →
      ∀ x : V, x ∉ U → ∃ b : K,
        ∀ z : U, scalarAbs (b - g z) ≤ vectorNorm (x - (z : V)))
    (W : Submodule K V) (f : W →ₗ[K] K)
    (hf : ∀ w : W, scalarAbs (f w) ≤ vectorNorm (w : V)) :
    ∃ h : V →ₗ[K] K, (∀ w : W, h (w : V) = f w) ∧
      ∀ y : V, scalarAbs (h y) ≤ vectorNorm y := by
  sorry

end LinearMap
