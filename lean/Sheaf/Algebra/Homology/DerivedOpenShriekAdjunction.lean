/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Derived extension-by-zero and restriction adjunction

Source: literature/stacks-project/cohomology.tex, Tag 08BT (used in Tag 08BW);
literature/stacks-project/derived.tex, Tags 015F and 09T5
(blueprint: lem-sc-derived-open-shriek-derived-adjunction).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace AlgebraicGeometry

/-- For an open subspace `U` of a ringed space `X`, the exact functors extension by zero
`j_! = extensionByZeroPresheaf ⋙ sheafification` and restriction
`j⁻¹ = SheafOfModules.overFunctor (moduleRings X) U`, applied termwise to complexes, induce
functors `Functor.mapDerivedCategory` on the unbounded derived categories, and these are
adjoint: `j_! ⊣ j⁻¹` on `D(O_U)` and `D(O_X)`. The adjunction's `homEquiv` is the natural
bijection `Hom_{D(O_X)}(j_! A, B) ≃ Hom_{D(O_U)}(A, B|_U)` for every `A` and `B`. The
exactness and additivity of `j_!` passed to `mapDerivedCategory` are the proofs supplied by
`open_restriction_adjunction_exact` (proof terms, so the functor is the canonical one).

Source: literature/stacks-project/cohomology.tex, Tag 08BT (used in Tag 08BW);
literature/stacks-project/derived.tex, Tags 015F and 09T5
(blueprint: lem-sc-derived-open-shriek-derived-adjunction).

Proof: (1) Put A = Mod(O_X), B = Mod(O_U), F = restriction and G = extension by
zero. Both are exact and additive, with G left adjoint to F, by
`lem-sc-derived-open-restriction-adjunction-exact`. Apply
`lem-weil-pbc-exact-functor-derived-factorization` to each: termwise application
preserves quasi-isomorphisms and descends along the localization Q, giving the two
natural factorization isomorphisms. Every transition in the ind-system for
F and in the pro-system for G is consequently an isomorphism. Those systems are
therefore essentially constant, so RF and LG are defined everywhere and computed
termwise (Tag 015F). (2) Apply `lem-pc-derived-adjoint-functors` (Tag 09T5) to this
adjoint pair of functors between the abelian module categories. Its derived
adjunction supplies the Hom bijection, functorial in both derived objects, and
the factorization for F identifies the right-hand object with restriction to U. -/
theorem derived_open_shriek_adjunction (X : RingedSpace.{u}) (U : Opens X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))] :
    Nonempty
      (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1 ⊣
        (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory) := by
  sorry

end AlgebraicGeometry
