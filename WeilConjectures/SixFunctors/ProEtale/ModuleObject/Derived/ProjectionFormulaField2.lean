/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Projection formula with rational coefficients

Source: `literature/blueprint/latest/blueprint/part-six-operations/`
`sec-constructibility-upper-shriek/sec-ladic-summary/sec-late-coefficients/`
`sk-thm-sf-pf-field/_section.md` (blueprint: sk-thm-sf-pf-field).

The statement records the tensor closure and proper projection formula for the
localizing closures of bounded constructible finite-Tor complexes.  The coefficient
hypothesis is the two rational cases: a finite subextension of `ℚ_ℓ` or the
finite-subextension-valued algebraic closure.  The map is the canonical module-object
projection map supplied by `def-sfb-module-object-projection-map`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Tensor closure and the proper projection formula for rational coefficients.

Source: blueprint
`part-six-operations/sec-constructibility-upper-shriek/sec-ladic-summary/`
`sec-late-coefficients/sk-thm-sf-pf-field/_section.md`, with its standing convention
that the base field has prime characteristic p different from `ℓ` and is finite or
algebraically closed.

The first clause says that the localizing closure of `Dctf` is closed under the
ambient derived tensor product.  The second clause says that, for every proper
morphism, the canonical projection map is an isomorphism for arbitrary objects in
the two localizing closures.  The coefficient is represented by a finite intermediate
extension or by the finite-subextension-valued algebraic closure; the displayed
isomorphism hypothesis fixes the coefficient ring object used by the categories.

Proof steps recorded by the blueprint proof document:

1. For every standing scheme, identify `Dctf` with the bounded constructible category
   and identify its localizing closure with the closure of that category.
2. Derived tensor is exact in each variable and preserves all small direct sums by its
   closed structure and left-adjoint property.
3. For locally closed immersions, use the open and closed base-change isomorphisms and
   coefficient cartesianness to rewrite extension-by-zero pullbacks on a fibre product.
4. Apply the immersion projection formula twice to express the tensor of two extended
   lisse modules as one extension by zero of a tensor on the fibre product.
5. After a common pro-etale cover the lisse modules are finite free, so their tensor is
   flat and the resulting extension by zero is bounded constructible.
6. Finite-cone dévissage of the coefficient heart, together with exactness, gives
   tensor closure of bounded constructible objects.
7. Minimality of the localizing closure extends tensor closure from the heart to both
   arbitrary localizing inputs, one variable at a time.
8. For a proper morphism, proper direct image and inverse image preserve the localizing
   closures, exactness, and direct sums by the proper-image and base-change results.
9. The map is the specified canonical module-object projection transformation, whose
   shift and connecting-triangle compatibilities are supplied by rational dévissage.
10. The bounded proper projection formula and determination by localizing subcategories
    give the isomorphism for every localizing object in the first input.
11. Repeat determination in the second input; the resulting isomorphism is the stated
    canonical map for all `M` and `N` in the two localizing closures.
-/
theorem projectionFormulaRational
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (hk : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ (A B : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left))),
      localizingClosureProEtale Λ X.left A →
      localizingClosureProEtale Λ X.left B →
      localizingClosureProEtale Λ X.left
        (((derivedTensor Λ X.left).obj A).obj B)) ∧
    (∀ (p : X ⟶ Y) [IsProper p.left]
      (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left)))
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ Y.left))),
      localizingClosureProEtale Λ X.left M →
      localizingClosureProEtale Λ Y.left N →
      IsIso (moduleObjectProjectionMap Λ p.left M N)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

end
