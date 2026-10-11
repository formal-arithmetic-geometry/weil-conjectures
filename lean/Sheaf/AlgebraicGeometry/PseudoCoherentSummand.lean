/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.PseudoCoherentComplex

/-! # Pseudo-coherence is preserved by direct summands

Source: literature/stacks-project/cohomology.tex, Tag 08CE
(blueprint: lem-pc-pseudo-coherent-summand).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If a pseudo-coherent object of `D(𝒪_X)` is isomorphic to a binary biproduct,
both summands are pseudo-coherent. Source: Stacks Project, Cohomology of Sheaves,
Tag 08CE, with More on Algebra, Tag 064X (blueprint: lem-pc-pseudo-coherent-summand).

Proof:
1. By the local definition `def-pur-pseudo-coherent-complex`, work on affine opens
   `U = Spec R`. Restriction preserves the decomposition and pseudo-coherence of `K`.
   A local bounded-above finite-free representative gives quasi-coherent cohomology
   for `K`. The cohomology of each summand is an image of an idempotent on the
   corresponding cohomology of `K`, hence is quasi-coherent as well.
2. Use `lem-pc-affine-qcoh-derived-equivalence` to represent the restrictions of `L`
   and `M` by sheafifications of module complexes `P` and `Q`. Additivity identifies
   the restriction of `K` with the sheafification of `P ⊕ Q`.
3. By `lem-pc-affine-pseudo-coherent-criterion`, `P ⊕ Q` has a bounded-above finite-free
   representative. The last clause of `lem-pc-ring-pseudo-coherent-summand` gives such
   representatives for both `P` and `Q`. Apply the affine criterion again to conclude
   pseudo-coherence of both restrictions.
4. These local representatives witness pseudo-coherence of `L` and `M` on `X` by
   `def-pur-pseudo-coherent-complex`. The same argument permits either summand to be zero.
-/
theorem pseudoCoherent_of_isIso_biproduct (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L M : schemeDerivedCategory X)
    (h : Nonempty (K ≅ L ⊞ M))
    (hK : IsPseudoCoherent X K) :
    IsPseudoCoherent X L ∧ IsPseudoCoherent X M := by
  sorry

end AlgebraicGeometry.Scheme
