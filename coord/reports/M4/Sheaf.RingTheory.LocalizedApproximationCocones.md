## What changed

Replaced the sorry in `Algebra.exists_localized_approximation_cocones` by a complete Lean
proof from `Algebra.localized_approximation_colimits` and the new, strictly smaller
`Algebra.canonical_localized_approximation_limit`. The existing theorem's statement and
all public imports are unchanged. Both added proof imports are ordinary imports.

The proof uses the existing explicit fraction diagrams, proves their locality and
commuting squares, constructs every stage numerator map, proves ring and module
naturality and semilinearity, and supplies the stage module equivalence and
IsLocalizedModule witness. Private proved helpers transport identity equivalences and
localization maps across equality of scalar actions. No definition takes data from an
unproved existence theorem. The unused-variable linter is scoped off for the existing
statement to preserve its original named `hmodel` binder.

The new module identifies the base and module colimits after the existing colimit theorem
has already supplied ψ and the compatible action. It does not repeat the existence of
those data, nor assert the stage comparison or numerator-map conclusions. The original
DAG node and the new node record this route. The original unit's realized nodes are
unaffected.

## Proved and sorry left

Closed the original hole in `Algebra.exists_localized_approximation_cocones`
(node `lem-weil-pbc-localized-approximation-cocones`): 1 of 1 original sorries closed.

Added exactly one hole: `Algebra.canonical_localized_approximation_limit`, in
`Sheaf.RingTheory.CanonicalLocalizedApproximationLimit`
(node `lem-weil-pbc-canonical-localized-approximation-limit`). Its body is exactly
`:= by sorry`. Its docstring and node give the source and fraction-colimit argument.
This is a decomposition: one upper hole closed, one strictly smaller hole added,
net holes zero. The existing imported `Algebra.localized_approximation_colimits`
still contains sorry and is not changed by this delivery.

Both delivered modules compile together, with no compiler warnings. The theorem combines
existing colimit data, the separate limit comparison, and genuine Lean proofs of all
remaining stage assertions; it is not a renamed application of the original statement.

## No longer needed

None: no pre-existing imports were removed and no global module pruning is claimed.
The original node's direct dependencies on
`lem-weil-pbc-filtered-colimit-localization-at-prime` and
`def-weil-directed-colimit-abelian-groups` are replaced by the explicit localized-diagram
module and the new comparison node. Ring localization and additive eventual-equality
results remain needed below the new comparison, so they are not globally pruned.

Discarded the earlier attempt's unused `localized_approximation_canonical_diagrams`
proposal; no such declaration or node is included in this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the original theorem as sorry and therefore did not meet the
requirement to close an existing hole. The dry-run rejection was correct, rather than a
tool failure. Its proposed helper was not connected to a proof of the original theorem.

The existing `localized_approximation_colimits` theorem supplies ψ and the compatible
colimit module action, but its last clause is only a flatness equivalence. That clause
does not provide the IsLocalization witness or the R-linear equivalence required here.
The new comparison isolates this interface gap without changing the existing theorem.

`lem-pc-localized-approximation-colimits` belongs to another unit and is used as a generic
localization-colimit tool. Its explicit diagrams and colimit interface apply without
finiteness or Picard assumptions. This use does not bypass any realized step of
`sk-thm-p1`; none of the item's old dependencies is a realized unit step.

The source was checked at the official Stacks pages for Tags 00RC and 037D, and
`algebra.tex` was downloaded into the sandbox's scratch directory for reading. The
comparison is the omitted colimit identification in the first reduction, with the
fraction argument written out. No statement or definition was weakened or changed.

## New nodes

`lem-weil-pbc-canonical-localized-approximation-limit` records only the base-localization
witness and R-linear comparison for the fixed canonical fraction diagrams and already
supplied compatible ψ and action. Its argument compares the localized ring colimits,
lifts module numerators and denominators, descends fraction equality with a multiplier,
and checks the restricted R-action. The edge cases checked were zero modules, singleton
and constant identity diagrams, noninjective transitions, and the zero top ring (where
no prime q exists). No finiteness assumption is used. Compatibility with all localized
coprojections determines the supplied ψ and action, so arbitrary alternative choices
do not invalidate the comparison.

Mathlib searches used leanfinder, loogle and grep; LeanSearch was also attempted
and returned Internal Server Error, which is recorded without an absence conclusion. The full imported blueprint was
searched with `blueprint_refs.py search` for localization colimits and Tag 037D; no
matching blueprint statement was found. The new statement and its source proof follow
parent steps 2 and 4. There are no change records or forced adaptations.

## Second reading by M4

1. Compared the delivered item module with the repository version. The existing theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof helpers
   and proof-only imports were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`. The item theorem has no `sorry`,
   and the only remaining `sorry` is the named split theorem
   `Algebra.canonical_localized_approximation_limit`; no forbidden declarations or hollow
   definitions occur. Verdict: pass.
3. Checked the split statement against the imported declarations and searched Mathlib and
   the library for duplicates. The comparison theorem is strictly smaller than the item,
   has a source and complete docstring proof, and its DAG node matches its Lean statement.
   Verdict: pass.
4. Checked the proof route from the top downward. It uses the explicit localized diagrams,
   the supplied colimit theorem, and the new comparison exactly where needed; no shorter
   available theorem was found. The unit's realized route is preserved. Verdict: pass.
5. Checked the item and new node proof dependencies against the imports and proof text.
   The original obsolete dependencies are removed from the node, while all actual imports
   remain needed. Verdict: pass.

Changed after this reading: added this review record only; no Lean statements or proofs
were changed.
