/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Binary direct sums of quasi-coherent modules

Source: Stacks Project, Modules, Lemma 01BF; Schemes, Lemma 01ID and Section 01LA
(blueprint: lem-weil-pbc-quasi-coherent-module-direct-sum).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

local instance {X : Scheme.{u}} : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The binary direct sum of quasi-coherent modules on a scheme is quasi-coherent.
The biproduct is the sectionwise binary sum, up to its canonical isomorphism: evaluation
preserves finite limits, and binary products of modules are their binary direct sums.
Its canonical inclusions and projections are `biprod.inl`, `biprod.inr`, `biprod.fst`,
and `biprod.snd`.

Source: Stacks Project, Modules, Lemma 01BF; Schemes, Lemma 01ID and Section 01LA
(blueprint: lem-weil-pbc-quasi-coherent-module-direct-sum).

Proof:
1. A matching family of pairs is a matching family in each summand. Gluing in each
   sheaf gives unique gluing in the sectionwise sum. The inclusions and projections
   satisfy the biproduct identities, so this sum is also a coproduct
   (`def-weil-sheaf-of-modules-category`, `def-weil-additive-category`,
   `def-weil-pbc-category-colimit`).
2. On each affine open U = Spec R, restrict the summands. By the affine tilde/global
   sections equivalence, they are the tilde modules of their sections M₁ and M₂
   (`lem-weil-pbc-module-restriction-open-immersion-colimits`,
   `lem-weil-pbc-affine-tilde-gamma-adjunction`).
3. Restriction and tilde preserve coproducts. Their universal properties identify the
   restricted sum with the tilde module of M₁ ⊕ M₂; the comparison morphisms are inverse
   because their composites agree on both coprojections (the same two lemmas and
   `def-weil-pbc-category-colimit`).
4. Affine opens cover X, so this identification gives the affine-local condition of
   quasi-coherence (`def-pc-scheme`, `pqf-def-coherent`). -/
theorem isQuasicoherent_biprod {X : Scheme.{u}} (F₁ F₂ : X.Modules)
    [F₁.IsQuasicoherent] [F₂.IsQuasicoherent] :
    (F₁ ⊞ F₂).IsQuasicoherent := by
  sorry

end

end AlgebraicGeometry.Scheme.Modules
