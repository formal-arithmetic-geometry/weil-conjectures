/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.SmoothPurityTowerGluingData

/-! # Finite levels of a normalized smooth tower adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Finite exceptional adjunctions and their coefficient-mate equations for an already
constructed smooth tower adjunction with normalized chart counits.
Source: blueprint det-sp-tower-gluing, Levels
(blueprint: lem-sp-tower-chart-adjunction-levels).

Proof:
1. Apply reduction-exceptional to the fixed coefficient-independent compactification
at every positive exponent n+1. Compact-support preservation gives its left
restriction to finite constructible finite-Tor objects. Retain the realization of
the finite exceptional functor, unit, and counit. The compact-support calculus
gives the specified evaluation comparison and finite scalar preservation on X,Y.
2. For each K the chart comparisons and their counit equations give the hypotheses
of evaluated representability. Its finite-cover induction applies to EVERY finite
ctf test object, not just those which lift to a tower. Thus the evaluated tower
right object with its evaluated counit represents the finite compact-support Hom
functor. Compare it with the finite exceptional adjunction by transposing both
counits. Injectivity makes the resulting arrows inverse.
3. Evaluate the tower counit naturality equation for K -> L. The finite transpose
is injective, so these comparison isomorphisms are natural in K. Evaluate the
tower triangle identity to identify its unit with the finite unit. These give
exactly comparison, counit, and unit in Levels, without claiming that derived
evaluation is faithful.
4. The finite direct-image coefficient comparison is invertible on each finite
right-adjoint value by reduction-direct-image. Reduction-exceptional identifies
its counit mate with the exceptional coefficient comparison and proves that mate
invertible. This applies to every finite input K_n, not merely evaluated ones.
5. Apply reduction-transpose to each tower pair and the counit-preserving finite
comparisons from steps 2--3. Its transported reduction equation, after cancelling
the comparison inverse, is precisely Levels.reduction. Its comparison is
coefficientMate by its defining counit transpose. Equal indices use the tensor
unitor and triple indices the fixed ordinary scalar associator. All fields now
refer to the same finite adjunctions and evaluation comparisons; bundle them.
The empty source and dimension zero require no altered hypotheses or formulas. -/
theorem tower_chart_adjunction_levels
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G)
    (charts : Charts l E b o q k X Y
      ⟨inferInstance, inferInstance, inferInstance⟩ f d
      (CondensedRing.compactificationOverField f) hF G adj) :
    Nonempty (Levels l E b o q (CondensedRing.compactificationOverField f) hF G adj) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
