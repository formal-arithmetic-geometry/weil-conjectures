## What changed

Repaired and proved `AlgebraicGeometry.Scheme.proEtaleProjectionMateData` in
`Sheaf.Paper.ProEtaleProjectionMateData`. The former statement quantified over
arbitrary independent source/target `CommShift` structures. The corrected theorem
constructs those structures jointly with exactness and the normalized natural mate.
Every mathematical conclusion of the unchanged parent theorem is retained.

The proof constructs the existing `ProjectionRestriction.Global` model and applies
`proEtaleProjectionGlobalComparison`. Currying the model's second-variable tensor
shift equation and composing it with the adjunction unit/counit gives an explicitly
shift-compatible model mate. Both shift structures and exactness transport through
the comparison isomorphisms. Cancelling the target comparison identifies its
components with the specified native mates.

For the unit component, the proof constructs a rank-one strict-perfect package on
the degree-zero coefficient ring complex, chooses a K-injective representative of
E, and applies the existing `SignedProjectionResolution.normalization`. Its two
inverse identities prove `IsIso`; no new comparison or arbitrary object is chosen.
The package and zero off-degree terms work equally for the zero ring and empty scheme.

Adapted the sole consumer `Sheaf.Paper.ProEtaleProjectionMateExact` (unclaimed): its
original signature and docstring stay verbatim, and its proof applies the corrected
data theorem. The shared source library and all public imports remain unchanged.
Updated the two corresponding DAG proof routes, the item's corrected statement and
its `statement_change` citer audit. Change record:
`coord/changes/proetale-projection-mate-compatible-shifts-d7.md`.

Private proof imports added: `RingedProjectionGlobalModel`,
`ProEtaleProjectionGlobalComparison`, `RingedProjectionTensorExact`,
`SignedProjectionResolutionNormalization`, and Mathlib's triangulated adjunction API.
All imported project statements already have DAG nodes. No new node or hole is added.

The repaired item and its sole direct consumer compile cleanly together on the
project server in 12.5 and 6.3 seconds, respectively.

## Proved and sorry left

The corrected `AlgebraicGeometry.Scheme.proEtaleProjectionMateData` has a complete
Lean proof. Its former arbitrary-shift statement is false and is not claimed proved:
this is a statement repair, not a proof of that former statement. The one original
hole is removed by the repaired proof; zero holes are added and zero remain in either
delivered module. `AlgebraicGeometry.Scheme.proEtaleProjectionMateExact` keeps its
original statement and has a complete proof from the repaired theorem.

The proof reuses the existing stated `proEtaleProjectionGlobalComparison` and
`ProjectionRestriction.ringedProjectionTensorExact`; their existing holes are not
closed or duplicated here. The delivery does not claim axiom-free completion of
these transitive dependencies.

## Forced adaptations

`Sheaf.Paper.ProEtaleProjectionMateExact` (unclaimed). The original proof destructured
`proEtaleProjectionMateData` as `⟨τ, hτ, hshift, hunit⟩` under instances supplied by
`proEtaleProjectionMateShiftData`; against the corrected statement (whose first
existential is now the source shift structure) that pattern no longer type-checks, so
the original module fails to compile. The eight proof lines are replaced by
`exact proEtaleProjectionMateData f R S c a b E` (the corrected statement is the
parent's statement verbatim), and the now-unused private import of
`Sheaf.Paper.ProEtaleProjectionMateShiftData` is removed. Signature, docstring and
public imports are unchanged. (Added by the reviewer.)

## No longer needed

Removed `import Sheaf.Paper.ProEtaleProjectionMateShiftData` from the parent and
removed `lem-weil-pbc-proetale-projection-mate-shift-data-s4` from its proof uses
and proof dependencies. The module `Sheaf.Paper.ProEtaleProjectionMateShiftData`
and that node are no longer needed on this route: the normalized model supplies
jointly compatible shifts and their exactness directly. The repository's only Lean
importer and only DAG dependency parent were the adapted parent. No module is
withdrawn and no DAG node is deleted.

The item's old sole direct proof dependency,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, is no longer sufficient by
itself. It remains necessary as a statement dependency and through the normalized
model/comparison, so it is not reported as pruned. No public import was removed.
The new proof uses four existing precise dependency nodes instead of splitting the
projection obligation again. All unit-realization nodes remain in place.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (repaired): the previous split's typeclass parameters did not
mean “the compatible structures supplied by the companion theorem”; they meant
all `CommShift` structures independently. At the identity morphism with integer
coefficients and E the ring unit, twist just one structure by the coherent
character n ↦ (-1)^n. The degree-one shift equation changes sign. The universally
claimed equations would force twice the invertible unit mate to vanish, which is
false over the integers. Merely choosing exact source and target functors in a
separate existence theorem does not identify their shifts with compatible ones.

The source's canonical shifts and its unchanged parent conclusion are recovered
by the joint existential construction. The one DAG citer is
`lem-weil-pbc-proetale-projection-mate-exact`; its use still holds and its assembly
proof is adapted in the same packet. No chapter or unit route changes. No target
signature, hypothesis or definition changes.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
