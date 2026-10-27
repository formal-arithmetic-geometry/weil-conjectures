/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Integral birational morphisms onto normal integral schemes

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal),
including its integral variant (blueprint: lem-trf-integral-birational-normal-isomorphism).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An integral birational morphism onto a normal integral scheme is an isomorphism.

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal),
the integral variant (blueprint: lem-trf-integral-birational-normal-isomorphism).

Proof:
1. For a nonempty affine open `U` of `T`, integrality makes `V = p⁻¹(U)` affine.
   The generic-point equality makes `V` nonempty. By
   [lem-sc-integral-function-field-affine-fraction], the section rings `A` and `B`
   are domains with fraction fields `k(T)` and `k(Z)`. Naturality of germs gives
   `β u = φ α`, where `u : A → B` is the integral section map and `φ` is the
   transported generic stalk map. Thus `u` is injective, and we may regard
   `A ⊆ B ⊆ k(T)` using `α` and `φ⁻¹ β`.
2. For each maximal ideal of `A`, [lem-weil-pbc-affine-open-stalk-localization](c)
   identifies the localization with the corresponding local ring of `T`, which
   is a normal domain. By [lem-weil-pbc-normal-domain-of-local-normal], `A` is
   integrally closed in `k(T)`.
3. Each `b ∈ B` satisfies a monic equation over `A` by
   [def-weil-finite-integral-morphism]. The same equation in `k(T)` puts `b` in
   `A` by [def-weil-pbc-normal-ring]. Thus `u` is surjective and hence an
   isomorphism. By [lem-sc-affine-global-sections-iso], `V → U` is an isomorphism.
4. The inverses on nonempty affine opens agree on overlaps, since each is the
   inverse of the same restricted isomorphism. By [lem-weil-pbc-scheme-morphism-gluing]
   they glue to `s : T → Z`. The uniqueness clause gives `p s = id` on the affine
   cover of `T` and `s p = id` on its inverse-image cover of `Z`. Thus `p` is an
   isomorphism. No affine-overlap assumption or finite subcover is used.
-/
theorem isIso_of_integral_birational_normal
    {Z T : Scheme.{u}} [IsIntegral Z] [IsIntegral T]
    (p : Z ⟶ T) [IsIntegralHom p]
    (hgeneric : p (genericPoint Z) = genericPoint T)
    (hbirational : Function.Bijective
      ((T.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
        p.stalkMap (genericPoint Z) : T.functionField ⟶ Z.functionField))
    (hnormal : ∀ t : T,
      IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t)) :
    IsIso p := by
  sorry

end AlgebraicGeometry
