/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedCoheratorAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The affine derived coherator comparisons

Source: Stacks Project, Derived Categories of Schemes, Tag 08D9 (3),
`perfect-lemma-affine-coherator`
(blueprint: lem-sfb-affine-derived-coherator).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine scheme, the actual unit of the normalized derived coherator
adjunction is invertible on every object, and its actual counit is invertible
on every object with quasi-coherent cohomology. The categories are unbounded;
no Noetherian hypothesis is required.

Source: Stacks Project, Tag 08D9 (3), `perfect-lemma-affine-coherator`
(blueprint: lem-sfb-affine-derived-coherator).

Proof:
1. Write X = Spec A. The tilde/global-sections adjunction restricted to
   quasi-coherent sheaves is an additive equivalence by clauses (2) and (3) of
   `lem-weil-pbc-affine-tilde-gamma-adjunction`. Both categories are abelian by
   `lem-sfb-qcoh-grothendieck-generators`. Transporting kernel and cokernel
   universal properties through the equivalence proves both functors exact.
2. Apply `lem-weil-pbc-exact-functor-derived-factorization` to these two exact
   functors. Clause (2) of `lem-weil-pbc-localization-universal-property` lifts
   their termwise unit and counit isomorphisms and inverse identities. This gives
   quasi-inverse equivalences on the unbounded derived categories.
3. Exactness of the quasi-coherent inclusion identifies the cohomology of its
   termwise image with the inclusion of cohomology, so it lands in D_QCoh.
   By `lem-pc-affine-qcoh-derived-equivalence` and the localization universal
   property, its composite with the derived tilde equivalence is the affine
   derived equivalence. Thus the derived inclusion is fully faithful and every
   E in D_QCoh is isomorphic to an object I(B).
4. For the specified adjunction of `lem-sfb-scheme-derived-coherator-adjunction`,
   apply `lem-sp-adjunction-unit-fully-faithful-left` to obtain invertibility
   of its actual unit at every B.
5. The triangle identity says d(I(B)) composed with I(e(B)) is the identity.
   Hence d(I(B)) is the inverse of I(e(B)). For v : I(B) ≅ E, counit naturality
   expresses d(E) as v composed with d(I(B)) and the inverse of I(C(v)).
   Every factor is invertible, giving the assertion for arbitrary unbounded E. -/
theorem affineDerivedCoherator_comparisons (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    (d : DerivedCoheratorAdjunctionData
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) :
    (∀ B : @DerivedCategory
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory _
        d.abelian d.derivedCategory,
      IsIso (d.derivedAdjunction.unit.app B)) ∧
    (∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      IsIso (d.derivedAdjunction.counit.app E)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
