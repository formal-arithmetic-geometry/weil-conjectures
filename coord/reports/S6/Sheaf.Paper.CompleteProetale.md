## What changed

Proved `AlgebraicGeometry.Scheme.completeProetale_isIso` in
`lean/Sheaf/Paper/CompleteProetale.lean`, with its exact original statement. The proof
transports each retained etale origin through the normalized finite-ring comparison,
uses the fourth edge of `AdicCoefficientDatum.fourTowers_compatibility`, proves joint
conservativity of derived tower evaluations directly from Mathlib homology, and
applies derived inverse limit to the resulting isomorphism. Unfolding
`completedExchange` leaves the specified ordered composite, whose factors are invertible.
The source is main-20261015 `sk-prop-pbc-complete/thm-weil-pbc-complete-proetale.proof.md`.
The unit's realized statements and steps remain in the dependencies; no alternate
proper-base-change theorem or constructibility hypothesis is introduced.

Adapted the unclaimed module `lean/Sheaf/Paper/CompletedPullback.lean`: its existing
`towerComplete_iff_intrinsic` now compares the unchanged quotient unit with the
published `PbcIsIntrinsicallyComplete` predicate. Its former internal universal
representative formulation cannot be applied to the public hypothesis. Both are the
same intended mathematical condition, but their coefficient presentations and
quantifiers are not definitionally identical. The comparison theorem remains unproved;
its docstring records the complete unit-preserving comparison argument. The new public
import of `BoundedConstructibleComplete` is needed by this statement. No target or
public definition changes. The original bridge has no code users outside its module.
The complete downstream consumer inventory, old/new signatures, source, edge cases,
and scope of the repair are in
`coord/changes/S6-intrinsic-completeness-bridge.md`.

Also proved `AdicCoefficientDatum.towerModulePull_exact` in that module directly from
ordinary exact pullback and pointwise preservation of finite limits and colimits.
No second notion of completion or origin was introduced. The helper isomorphisms in
the item are private and fully proved; the associated-module isomorphism is selected
from an existing uniqueness theorem. The public input origin hypothesis supplies the
retained complex, rather than any unproved existence theorem choosing new data.

Validation: both modified modules compiled together through `lcompile.py` before the
last exactness proof was added. The normalized scalar-square, ordinary realization
comparison and complete derived-origin transport separately compiled through
`lcompile.py` (4.3 seconds). The final auxiliary module, including the pointwise exactness proof, compiled
cleanly in 2.6 seconds. The earlier three dry runs and the first dry run of the resumed session stopped before
pushing because the compile server returned no answer after built-in retries (the
resumed attempt: 258 seconds), rather than any Lean error. The resumed dry run subsequently passed: commit `e4873b3a9c` compiles and
passes preflight, with review class CODEX; nothing was pushed by that dry run. The downstream inventory was refreshed against the current checkout:
1,329 affected modules including the adapted module, which remains unclaimed; the
bridge still has no existing code callers outside its declaration. `import_direction.py may` accepts the new public import.

## Proved and sorry left

Item: closed 1 of 1 original holes, in
`AlgebraicGeometry.Scheme.completeProetale_isIso`; zero holes remain in the item.
Added zero holes and split off zero theorems.

Auxiliary module: closed the existing hole in
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerModulePull_exact`.
The existing hole in
`AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerComplete_iff_intrinsic`
remains, with the corrected public-predicate formulation and the same source node
`def-weil-pbc-completed-pullback`. Its reformulation is not counted as a proof.
This is the only direct `sorry` left in the delivered files. The main proof uses
existing named dependency theorems that are still unproved, as stage 3 specifies.
Across the two delivered modules: 3 original holes, 2 closed, 0 added, 1 remaining.

## No longer needed

Removed all eight original proof-only import lines from the item:

- `Sheaf.Paper.AdicCoefficientDatum`: retained transitively; its definitions are used.
- `Sheaf.Paper.FiniteLevelProEtaleBaseChange`: retained through `FourArrows`, which
  certifies the finite exchange isomorphism.
- `Sheaf.Paper.FourArrows`: retained transitively; its finite isomorphisms are used.
- `Sheaf.Paper.CompletedTowerCompatibility`: retained by the public import of
  `CompletedBaseChangeMap`; its fourth-edge equation is used.
- `Sheaf.Paper.CompletedDirectImageLimits`: retained transitively; the specified
  outer comparison is part of the unchanged ordered composite.
- `Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones`: no longer needed by this proof.
  The short Mathlib homology argument supplies exactly the tower conservativity used.
- `Sheaf.Paper.CompletedMapReduction`: no longer needed by this proof. The actual
  tower evaluation equation comes from `fourTowers_compatibility`; conjugating a
  finite reduction of the completed exchange is a different statement.
- `Sheaf.Paper.CompletedExchangeCoherence`: no longer needed by this theorem, whose
  conclusion asserts invertibility only. Naturality and pasting are separate results.

Accordingly the proof node no longer lists
`lem-weil-pbc-levelwise-isomorphism-cones`,
`lemma-weil-pbc-completed-map-reduction`, or
`lemma-weil-pbc-completed-exchange-coherence` as proof dependencies.
Those modules/nodes may still be needed by other parents; no global unreachability
is claimed and no module is withdrawn. The two original public imports stay.
A direct proof import of `CompletedPullback` declares use of the repaired bridge and
orders the sandbox compile before the item. No unused proof import remains.

## Where the brief, the DAG or earlier work was wrong

The current blueprint proof calls completed-map reduction an evaluation statement
about the strict tower. The existing Lean declaration instead compares the reduced
completed map by conjugation. `fourTowers_compatibility` supplies the precise strict
tower fourth edge; using it follows the intended finite-level argument without
conflating the two statements. The old DAG already noted this distinction.

The existing completeness bridge does not use the public intrinsic predicate in the
item's hypothesis. The first compile of the item against the original bridge reported
a type mismatch: `PbcIsIntrinsicallyComplete` was supplied where the universal family
of `IsDerivedCompleteIntrinsic` proofs was expected. The interface repair records this
explicitly; it does not silently claim that coefficient transport or representative
independence is definitional. No existing consumer applies the old binders.

The generic levelwise-isomorphism/cone theorem uses a different coefficient-universe
presentation and much more completion theory than the tower-only conclusion needed
here. Mathlib's exact derived homology comparison gives that conclusion directly.
There is no source-mathematics dispute and no immutable target statement was changed.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
