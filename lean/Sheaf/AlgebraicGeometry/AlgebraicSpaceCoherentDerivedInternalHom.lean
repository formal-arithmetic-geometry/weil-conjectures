/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.BoundedAboveCoherentRHom

/-! # Coherent derived internal Hom on locally Noetherian algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0D0S;
Spaces Cohomology, Tag 07UB (blueprint: lem-sfb-space-coherent-derived-internal-hom).

We use the existing equivalent small affine ringed model and its K-injective derived
internal Hom. On a locally Noetherian algebraic space, coherence is precisely the
existing finite-presentation predicate for module sheaves, by Tag 07UB.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Derived internal Hom from a bounded above coherent object into a bounded below
coherent object has coherent cohomology and is bounded below.
Source: Stacks Project, Tags 0D0S and 07UB
(blueprint: lem-sfb-space-coherent-derived-internal-hom).

Proof:
1. Choose global upper and lower cohomology bounds a and b for K and L. On any
Noetherian affine etale chart U = Spec A, exact module restriction preserves these
bounds and coherent cohomology (lem-pur-site-restriction-module-adjunction-exact).
By lem-sfb-affine-etale-derived-module-realization the restrictions are associated
to E,F in D(A); the cohomology and sections comparisons give finite cohomology
modules and the same upper and lower bounds.
2. By lem-weil-pbc-ringed-internal-hom-exact-restriction, restriction of RHom(K,L)
is RHom of the restrictions. By lem-sfb-affine-etale-derived-hom-realization this
is the associated sheaf complex of RHom_A(E,F).
3. Apply lem-trf-bounded-above-coherent-rhom. Its cohomology modules are finite and
vanish in degrees r < b-a. The affine realization cohomology comparison proves
coherence on every Noetherian affine etale chart, hence finite presentation by 07UB.
4. The bound b-a is independent of the chart. Pulling an affine etale atlas back
to any etale object and refining by affine opens makes every section of the lower
cohomology sheaves zero locally. The sheaf separatedness axiom makes it zero
globally. This includes the empty algebraic space. -/
theorem coherent_derivedInternalHom {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    [HasDerivedCategory.{w} X.SmallModules] (K L : X.DerivedModules)
    (hK : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.SmallModules i).obj K).IsFinitePresentation)
    (hL : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.SmallModules i).obj L).IsFinitePresentation)
    (hKbounded : ∃ a : ℤ, ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj K))
    (hLbounded : ∃ b : ℤ, ∀ i : ℤ, i < b →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules i).obj L)) :
    (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.SmallModules i).obj
      (X.derivedHom.obj (op K, L))).IsFinitePresentation) ∧
    (∃ c : ℤ, ∀ i : ℤ, i < c → IsZero
      ((DerivedCategory.homologyFunctor X.SmallModules i).obj
        (X.derivedHom.obj (op K, L)))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
