## What changed

Replaced the sole sorry in `DerivedCategory.ringPseudoCoherent_localization_glue` by a complete
Lean induction. A proved private helper derives an upper cohomology bound from a bounded
finite-free witness. Finiteness of the index set gives a common local bound, and localization
vanishing detection gives the global bound. Induction on the natural-number bound above `m`
uses the existing vanishing-base and distinguished-triangle declarations. The second clause
uses the existing equivalence between pseudo-coherence and every fixed-degree condition.
All existing signatures and public imports are unchanged. The two new proof imports isolate
one-degree vanishing detection and one top-cohomology cone step. Their modules include sources,
complete proof docstrings, and matching DAG nodes; the original node now follows the Lean proof.

## Proved and sorry left

Closed: `DerivedCategory.ringPseudoCoherent_localization_glue` (one original hole).
The proof is a decomposition from two strictly smaller new obligations, not a hole-free proof
of the import closure. The private `isMPseudoCoherent_boundedAbove` helper is fully proved.

Added and left:
- `DerivedCategory.homology_vanishes_of_localization_span`, node
  `lem-pc-homology-vanishing-localization-span`.
- `DerivedCategory.isMPseudoCoherent_localization_cone_step`, node
  `lem-pc-m-pseudo-coherent-localization-cone-step`.

The item's module has no sorry. The delivery adds two holes, so the immediate ledger net is
one closed minus two added, namely -1. Existing vanishing-base, triangle, finite-cohomology,
and all-m equivalence obligations remain in their existing modules.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.FiniteHomologyOfMPseudoCoherent` from the item;
it is needed by the cone-step obligation and is still transitively imported, so it is not
pruned from the target closure. The original node no longer directly depends on
`lem-sc-finite-cohomology` or `lem-weil-pbc-module-finite-of-localization-span`; both are needed
by the new cone-step node. No planned mathematical dependency is discarded and no module is
claimed as pruned. The blueprint unit has no realized statement or steps to bypass.

Second reading additionally replaced the vanishing module’s broad public `TStructure` import
with the narrower `DerivedCategory.HomologySequence` needed by its signature, and removed
the cone module’s redundant public `DerivedCategory.HomologySequence` import (already
provided by `MPseudoCoherent`). Neither removes a module from the target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The planned lemmas supply the base and triangle closure,
but not the localization/extension-of-scalars cohomology bridge or the finite-free top-degree
map and its localized cone. These are the two new obligations. The original proof's largest
nonzero cohomology degree is unnecessary: any common upper bound suffices, avoiding the
all-zero exceptional case.

The Mathlib search found `exact_of_isLocalized_span`, `Module.eq_zero_of_isLocalized_span`,
and tensor-product localization instances. An attempted direct vanishing proof reduced to
identifying their tensor-product module structures with the structures used by
`ModuleCat.extendScalars`; that bridge was not completed, and no partial proof is delivered.
LeanSearch returned Internal Server Error; successful LeanFinder, Loogle, and source searches
are recorded in searches.jsonl. Sources were read through the Stacks Tag 066D page because
literature source files are absent from this remote clone.

Edge cases checked mathematically: an empty cover forces the zero ring, so all cohomology
vanishes; zero or nilpotent cover elements give zero localizations and cause no difficulty;
a complex with all cohomology zero is handled by the same finite-bound construction; negative
values of `m` and upper bounds are covered by the integer-to-natural conversion; `n = m` in
the cone step uses the witness epimorphism in degree `m`, whereas `n > m` uses its isomorphism.
No existing definition, statement, or external module was changed. Validation: all three sandbox Lean
modules compiled together in dependency order, with no warnings.

## New nodes

`lem-pc-homology-vanishing-localization-span`: detects zero cohomology in one specified degree
from zero cohomology after every standard-open localization. It asserts neither boundedness
nor pseudo-coherence and is strictly part of step 1.

`lem-pc-m-pseudo-coherent-localization-cone-step`: one finite-free top-cohomology cone
construction under a given bound. It asserts a lower bound and retained local pseudo-coherence,
not global pseudo-coherence of the cone or original complex. The main module supplies the
actual induction and applies the global triangle theorem. No change records are needed.

## Second reading by D3

1. Compared the existing Lean module with the repository using `diff`. The complete existing
   theorem signature is byte-for-byte identical; its docstring and public imports are unchanged.
   The only additions are a proved private helper, the induction proof, and proof imports.
   Both additional public theorems are in separate new modules, with no definition or interface
   repair and no change record required. Verdict: pass.
2. Compiled all three modules in dependency order through `lcompile.py`, without errors or
   warnings, after the import cleanup. Searched every delivered Lean file for forbidden
   declarations and trust bypasses: none. Exactly the two named split-off theorems contain
   `sorry`; no definition was added. Scratch `#print axioms` checks for all three public
   theorems show only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
   The private bound helper transfers vanishing across an actual cohomology isomorphism.
   Verdict: valid decomposition, not a proof of the entire import closure.
3. Read both new statements and their complete proof docstrings against Stacks
   [066D](https://stacks.math.columbia.edu/tag/066D) and
   [00EO](https://stacks.math.columbia.edu/tag/00EO). Vanishing detection is only one degree;
   the cone theorem constructs only one lowering step and does not assert global
   pseudo-coherence of the original object or the cone. Checked empty covers (zero ring),
   a single unit, zero and nilpotent localizations, all-zero cohomology, `n = m`, `n > m`,
   and negative degrees. At `n = m` the witness map is surjective; at `n > m` it is an
   isomorphism. The single-term source is pseudo-coherent at every degree, including
   `m + 1` as required by the first triangle clause locally. The cone is a concrete
   mapping cone in the proposed proof, not data defined by an arbitrary unproved witness.
   Repeated LeanFinder, Loogle, Mathlib grep, and library searches with different wording
   (recorded in `searches.jsonl`). Found general exactness and homology comparison tools,
   not either complete statement or a shorter existing descent proof. Neither remaining
   obligation could be closed by a short application. Verdict: true, strictly smaller,
   useful obligations.
4. Checked the common-bound construction, the induction threshold `m + k`, the successor
   lowering step at `n = m + k`, and the final integer-to-natural conversion. The
   pseudo-coherent clause applies the existing all-m equivalence in both directions.
   The old proof dependencies no longer directly used are exactly finite top cohomology
   and finite-module localization descent, both retained below the cone-step node and
   listed above. The unit `sk-thm-picard-duality` has empty realized statement/step lists;
   no realized unit node is bypassed. Verdict: route preserved and pruning report complete.
5. Checked the existing node diff: only `proof`, `proof_deps`, and `proof_origin` differ.
   Its steps match the Lean induction, and each node's `proof_deps` is exactly the union
   of step uses. Both new nodes carry sources, dependencies, searches, blueprint ancestry,
   creation metadata, chapter/unit, and verbatim Lean signatures in their `lean` records.
   Verdict: pass.

Changed only imports of the new modules as described above and this report. No proof or
statement repair was needed. One original hole is closed and two new holes remain: this
is a decomposition with immediate net -1, and no target-closure module is claimed pruned.
