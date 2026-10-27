## What changed

Filled both theorem bodies in `Sheaf.Paper.ContinuousQbarLisseHeartClosure`, preserving
both signatures and the assertion predicate verbatim. Private proved helpers identify finite
constant local models with finite free local models and assemble ambient closure from a
triangulated class stable under standard truncations. The coefficient check specializes the
proved `Profinite.semihereditary_continuous_coefficients_admissible` theorem to a field;
all ideals are projective. The immersion clause uses the Noetherian topology on a subspace.

The scalar-model comparison imports `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
with `import all` to reuse its proved scalar-field and finite-free comparison helpers.
Additional private proof imports supply semihereditary admissibility, full faithfulness of
the degree-zero derived inclusion, and its distinguished triangle for a short exact sequence.
The node proof and dependencies now describe this route. No statement or definition repair,
new public declaration, new node, source-library edit, or consumer adaptation is made.

## Proved and sorry left

Closed the two original holes, with no holes added or split off:

- `AlgebraicGeometry.ProEtale.continuousQbar_lisse_heart_closure`.
- `AlgebraicGeometry.ProEtale.continuousQbar_lisse_heart_closure_of_immersion`.

No `sorry` remains in the delivered module. Existing dependency holes are unchanged. In
particular the proof applies the published `tAdmissible_dualizable_truncations` and
`condensed_dualizable_stable` declarations as required by this stage.

The generic local-model comparison and categorical closure argument compiled separately.
The delivery command checks the complete module, its axioms, and the packet preflight.

## No longer needed

Removed these direct proof imports:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`: the general truncation
  theorem already states its criterion in the internal-module category.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: the more specific
  `DerivedCategory.SingleTriangle` import supplies the triangle actually used.
- `Mathlib.LinearAlgebra.FreeModule.PID`.
- `Mathlib.LinearAlgebra.Dimension.Free`.
- `Mathlib.RingTheory.Flat.Basic`.

The last three direct imports are replaced by the existing general continuous admissibility
theorem and the scalar-model comparison API. The field-flat node
`lem-weil-pbc-module-over-field-flat` is no longer a direct dependency: admissibility now
comes from `lem-sfb-semihereditary-topological-coefficients-admissible`.

Removed `def-weil-pbc-internal-abelian-sheaf-module-equivalence` from direct proof dependencies
and the existing top-level tool-use approvals. It remains a transitive dependency of the
general truncation theorem. No global module withdrawal or unit-route pruning is proposed.
Every retained dependency is still used for the field local models, Noetherian topology,
t-admissible heart criterion, stable dualizable class, or ambient triangle assembly.

## Where the brief, the DAG or earlier work was wrong

The t-admissible truncation theorem already operates in the internal-module category, so
its existing comparison supplies the planned ordinary/internal transport without another
transport here. The general semihereditary continuous-coefficient theorem makes a separate
section-ring reconstruction and direct t-admissibility calculation unnecessary.

Constructing the local-model cover while the continuous coefficient ring is concrete caused
expensive definitional equality. The finite-free-to-model argument needs no field assumption,
so it is proved first for an arbitrary internal coefficient ring. Local irreducibility of
pullback and scalar extension, as in the existing comparison module, prevents implementation
expansion. No exported definition or statement changes are needed.

The immersion proof needs an explicit `IsNoetherian X` instance assembled from the given
`IsLocallyNoetherian X` and `CompactSpace X` before Mathlib infers its Noetherian topology.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
