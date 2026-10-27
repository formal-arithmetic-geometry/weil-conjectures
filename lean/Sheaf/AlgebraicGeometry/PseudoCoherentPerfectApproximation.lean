module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex

import Sheaf.AlgebraicGeometry.SupportedPerfectApproximation
import Sheaf.AlgebraicGeometry.AffineSupportedPerfectApproximation
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh

/-! # Perfect approximations to pseudo-coherent complexes on qcqs schemes

Source: Stacks Project, Derived Categories of Schemes, Tag 08ES,
`theorem-approximation`, specialized to full support in Tags 08EM and 08EN
(blueprint: lem-sfb-pseudocoherent-perfect-approximation).

The approximating object has quasi-coherent cohomology and is perfect. The cohomology
map at the chosen degree is an epimorphism of sheaves of modules.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact quasi-separated scheme, every pseudo-coherent derived object has,
for each integer a, a perfect approximation with quasi-coherent cohomology, inducing
cohomology isomorphisms above a and an epimorphism at a.
Source: Stacks Project, Derived Categories of Schemes, Tag 08ES,
`theorem-approximation`, with T=X in Tags 08EM and 08EN
(blueprint: lem-sfb-pseudocoherent-perfect-approximation).

Proof:
1. For each quasi-compact open W, let A(W) be
   def-sfb-supported-perfect-approximation-property. The affine lemma
   lem-sfb-affine-supported-perfect-approximation proves A(W) for affine W,
   including the empty scheme.
2. For quasi-compact U and affine V, quasi-separatedness makes U intersect V
   quasi-compact (pqf-lem-qs-intersection-qc). Apply
   lem-sfb-supported-perfect-approximation-open-step to U union V and A(U).
   The induction principle lem-sc-invert-s-cohomology-induction gives A(X).
3. By lem-sc-pseudo-coherent-qcoh, E has quasi-coherent cohomology. In A(X), take
   T=X; its empty complement is retrocompact. For the resulting integer r, take
   m=a. Pseudo-coherence (def-pur-pseudo-coherent-complex) makes E
   (a-r)-pseudo-coherent. The support hypotheses outside X are vacuous. Hence A(X)
   gives a perfect P and a map P -> E inducing isomorphisms above a and an
   epimorphism at a.
4. By lem-sc-perfect-qcoherent, P has quasi-coherent cohomology, so it defines an
   object of schemeDerivedQCohCategory X. No Noetherian, separated, ample-line-bundle
   or base-ring hypothesis enters the argument. -/
theorem exists_perfect_approximation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (a : ℤ) :
    ∃ (P : schemeDerivedQCohCategory X) (u : P.obj ⟶ E),
      IsPerfect X P.obj ∧
      (∀ i : ℤ, a < i →
        IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).map u)) ∧
      Epi ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) a).map u) := by
  sorry

end AlgebraicGeometry.Scheme
