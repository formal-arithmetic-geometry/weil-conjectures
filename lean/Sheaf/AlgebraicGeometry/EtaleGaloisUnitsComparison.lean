/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker P2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.FieldTheory.GaloisUnitsCohomology
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules

/-!
# Degree-two comparison for the multiplicative sheaf over a field

Source: Stacks Project, Lemmas 04JQ and 03QU, Example 03QV (2), and Section 0DVG.
(blueprint: lem-sc-etale-galois-units-comparison).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Second continuous Galois cohomology of separable-closure units computes the second
etale cohomology of the multiplicative group over a field.

Proof: choose a geometric point with algebraically closed residue field containing the
separable closure. Its stalk functor is an exact equivalence between abelian etale
sheaves on `Spec K` and discrete modules with continuous absolute Galois action. The
stalk of `gmSheaf` is the unit group of the separable closure with its natural action:
etale neighbourhoods of the point see precisely finite separable extensions. Under
this equivalence, global sections are invariants. An exact equivalence preserves
injectives, so applying invariants to the transported injective resolution identifies
the right derived functors of sections and invariants in every degree. The continuous
cochain resolution computes derived invariants for discrete modules over a profinite
group; the homogeneous cochain model is the one in `Field.GaloisUnitsH2`. Take degree
two and forget the group structures. Here the Galois group is compact Hausdorff, so
the compact-open exponential law identifies the iterated continuous maps used by
Mathlib with continuous maps on finite powers of the group. The homogeneous and
inhomogeneous complexes agree by the usual change of variables. Topological-module
homology has the underlying algebraic kernel modulo image, so its topology does not
change the cohomology classes. Universe lifts in `gmSheaf` only lift the
coefficient group, and their canonical equivalences induce the same cohomology.

Source: Stacks Project, Lemmas 04JQ and 03QU, Example 03QV (2), and Section 0DVG.
The source's geometric point uses an algebraic closure; its multiplicative stalk is
still separable-closure units even when the base field is imperfect.
(blueprint: lem-sc-etale-galois-units-comparison). -/
theorem nonempty_equiv_galoisUnitsH2_cohomologicalBrauerGroup (K : Type u) [Field K] :
    Nonempty (Field.GaloisUnitsH2 K ≃ (Spec (.of K)).CohomologicalBrauerGroup) := by sorry

end AlgebraicGeometry.Scheme
