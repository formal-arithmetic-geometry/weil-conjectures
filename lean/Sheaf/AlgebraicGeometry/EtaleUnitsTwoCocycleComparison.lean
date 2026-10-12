/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker N3
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsTwoCocycles
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules

/-!
# Etale unit cohomology computed by continuous inhomogeneous cocycles

Source: Stacks Project, Tags 04JQ, 03QU, 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-units-two-cocycle-comparison).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Explicit continuous inhomogeneous two-cocycle classes compute the second etale
cohomology of units over a field. This theorem does not use Mathlib's homogeneous
continuous cochain complex.

Proof: choose the algebraic closure of the separable closure as a geometric residue
field. Apply `abelianSheaves_equiv_discreteGModules`. A germ of an etale regular function
at this point has value in a finite separable extension of `K`; conversely every such
value is a section over the spectrum of that extension. Restricting to invertible
functions identifies the multiplicative stalk with separable-closure units. The action
formula on germs identifies its Galois action with the action in `galoisUnitsTopRep`.
This includes imperfect fields: purely inseparable elements of the geometric residue
field do not occur in the etale neighbourhoods.
Under the stalk equivalence, sections over `Spec K` are invariant germs, and the
identification is natural in the abelian sheaf. An equivalence between abelian categories
is exact and preserves injectives. Transport an injective resolution and apply this
natural identification termwise. It identifies sheaf cohomology with the right derived
functors of invariants on discrete continuous Galois modules.
For a profinite group these derived invariants are computed by continuous inhomogeneous
cochains: continuous cochains preserve short exact sequences of discrete modules (lift
locally constant maps on finite clopen partitions); continuous coinduction embeds each
module and is acyclic in positive degrees by the insertion contracting homotopy.
Consequently the cochain delta-functor is effaceable and agrees with derived invariants,
by uniqueness of universal delta-functors, extending the identity on invariants.
Taking degree two gives the kernel of the displayed two-cocycle differential modulo
the image of the displayed one-cochain differential. Equality of two classes is thus
exactly `galoisUnitsTwoCocycleRel`, whose quotient is the left side. Finally remove the
canonical universe lift in `gmSheaf` by its additive, equivariant inverse; the same maps
on cochains give inverse maps on cohomology. Forgetting the additive structure gives the
asserted equivalence of types.

Source: Stacks Project, Lemmas 04JQ and 03QU, Example 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-units-two-cocycle-comparison). -/
theorem nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup
    (K : Type u) [Field K] :
    Nonempty (Field.GaloisUnitsTwoCocycleClasses K ≃
      (Spec (.of K)).CohomologicalBrauerGroup) := by sorry

end AlgebraicGeometry.Scheme
