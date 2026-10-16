## What changed

Proved `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_refinement_solving_local_requirements`
with its existing signature unchanged. The two other public theorems and both existing public
imports of the item are unchanged.

For each degree, intersect the pullbacks of the requested sieves along all relevant simplicial
operators. These finite intersections are covering and stable under every simplicial operator.
Construct a compatible tower of replacement stages solving these sieves, then assemble it and
select the identity operator to recover each original requirement.

Added five modules, all completely proved:

- `Sheaf.Paper.FiniteSplitLocalReplacementStage`: the actual proposition `StageSolves`.
- `Sheaf.Paper.FiniteEtaleSieveCover`: finite affine relative covers subordinate to a covering sieve.
- `Sheaf.Paper.FiniteSplitLocalReplacementZero`: the constrained degree-zero stage.
- `Sheaf.Paper.FiniteSplitLocalReplacementExtension`: the constrained successor stage, using the
  existing boundary geometry, relative cover, explicit refinement and split-structure attachment.
- `Sheaf.Paper.FiniteSplitLocalReplacementAssembly`: assembly retaining the solving cofans. It
  reuses the existing private matching/transport and tower helpers with proof-only `import all`.

The item imports the three construction theorems privately. The new route follows the existing
local-lifting paragraph and the 0DAV split induction. No existing dependency module was edited.
The unit record `sk-prop-h2` has no binding realized nodes to bypass; its route is unchanged.

Validation: each new theorem was compiled during development; the complete sandbox is compiled
in import order and checked by the required delivery dry run. Edge cases checked in the argument:
zero requirements give maximal sieves, the empty scheme permits empty affine covers and cofans,
and degree zero uses the unique simplex operator. No nonempty-cover assumption is introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_refinement_solving_local_requirements`
(node `lem-weil-pbc-hypercover-refinement`).

No `sorry` remains in the item or in any new module. Holes closed: 1; holes added: 0;
split off: 0. This is a proof from the existing declared dependencies, not a decomposition into
new unproved lemmas. In particular, `exists_finite_etale_sieve_cover`,
`exists_local_replacement_stage_zero`, `exists_local_replacement_stage_extension` and
`exists_local_replacement_of_stage_tower` all have complete Lean proofs.

The proof still relies on existing replacement/attachment declarations in the library, as the
stage-3 brief intends. Their existing holes are neither copied nor added by this delivery.

## No longer needed

No existing import or library module is pruned: all original imports are used by the existing
existence/cofilteredness and truncated-refinement proofs. Removed a redundant direct Grothendieck
import from the new stage-condition module before delivery. The second reading also removed
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` from `FiniteEtaleSieveCover`
(already publicly available through `Sites.Etale`) and `Mathlib.CategoryTheory.Extensive`
from `FiniteSplitLocalReplacementExtension` (already publicly available through the stage module).

The original node no longer directly uses `lem-weil-pbc-qcqs-finite-affine-open-cover`,
`lem-weil-pbc-etale-covering-affine-refinement` or `lem-weil-pbc-etale-covering-base-change` as
standalone local-lifting black boxes. Its direct dependencies are the proved initial, successor,
and assembly lemmas. The finite-affine geometry and base-change mechanisms are used below those
lemmas via Mathlib and the existing relative-cover construction. These are changes of direct
proof dependencies, not claims that those modules are globally unreachable.

The unproved duplicate declarations in
`WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement` were not imported or used.

## Where the brief, the DAG or earlier work was wrong

The old node had no finite-stage interface for carrying the prescribed local conditions. The
existing unconstrained stage extension and assembly discard the information needed to retrieve
those conditions, so applying their existential conclusions alone cannot prove this hole.
The new, fully proved local variants retain exactly that information.

The implementation intersects pullbacks along all operators, rather than only the degeneracies
listed in the old prose plan. This makes simplicial stability immediate and imposes only finitely
many conditions in each degree. It also works above the originally specified bound.

The local Stacks source checkout is absent on this machine. The cited proofs were read on the
official Stacks pages: [01GJ](https://stacks.math.columbia.edu/tag/01GJ),
[01GK](https://stacks.math.columbia.edu/tag/01GK),
[0DAV](https://stacks.math.columbia.edu/tag/0DAV), and
[094K](https://stacks.math.columbia.edu/tag/094K).
No statement was disputed or changed; no forced adaptation was needed.

## New nodes

`def-weil-pbc-finite-split-local-replacement-stage` records `StageSolves`, an explicit
finite-cofan condition on the existing replacement stage. This is a proposition, with no
chosen object or postponed data.

`lem-weil-pbc-finite-etale-sieve-cover` selects finitely many affine opens of a cover subordinate
to a prescribed sieve, covering a compact relative target. Its geometric selection is proved
from the existing Mathlib compact-cover API.

`lem-weil-pbc-finite-split-local-replacement-zero` constructs the degree-zero stage with its
solving cofan. The terminal matching object and the identity splitting are written explicitly.

`lem-weil-pbc-finite-split-local-replacement-extension` constructs one successor stage.
Finite coproduct universality pulls old solving cofans back to the normalized summands;
operator stability handles the degenerate copies. It invokes the existing split attachment.

`lem-weil-pbc-finite-split-local-replacement-assembly` builds a full hypercover from compatible
local stages. Its degree-n object and refinement map are read literally from stage n, so their
finite solving cofan transfers directly. No change record is needed: all existing signatures
and visibility remain unchanged.


## Second reading by E1

1. **Existing interfaces: pass.** Compared the item's complete diff against the shared
   repository. All three existing theorem signatures are byte-for-byte unchanged; the other
   two theorem proofs, both public imports, and all definitions used by the targets are
   unchanged. The item adds three plain proof imports and one proved private helper.
   The five additional modules are new. No other existing Lean file is delivered, and no
   statement-change record is needed.
2. **Proofs and data: pass.** Read all six modules and compiled them in import order through
   `lcompile.py --all`, with no errors or warnings. Scanned the delivered sources for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and written `sorryAx`: none occurs.
   A separate scratch import file printed axioms for all three item theorems and all five
   new public declarations. The cover, StageSolves, initial-stage and assembly declarations
   use only `propext`, `Classical.choice`, and `Quot.sound`. The successor stage and item
   theorems additionally depend on existing upstream `sorryAx`, as permitted for open proof
   dependencies; no other axiom appears. StageSolves is an explicit proposition, not chosen
   data. The new cover is an actual coproduct of explicitly specified affine-open schemes;
   the initial stage, attached functor and glued functor are explicit constructions inside
   existential proofs. No new definition chooses an arbitrary witness from an unproved
   existence theorem.
3. **New statements: pass.** There are no split-off unproved statements. The cover lemma
   constructs finite affine pieces over a compact relative target without assuming the
   covering source compact. The initial and successor lemmas solve only their stated finite
   stages; assembly retains the very cofans from the compatible tower. None merely renames
   the original local-requirement conclusion. Checked zero requirements (empty intersections
   are maximal), degree zero (the sole endomorphism is identity), empty schemes/empty cofans,
   and degenerate summands (pull back the lower cofan along its nondegenerate inclusion).
   Independent LeanFinder search for pullback of finite coproduct presentations, Loogle
   search for finite intersections of covering sieves, Mathlib grep, and direct searches of
   `lean/Sheaf` and `lean/WeilConjectures` found no shorter complete refinement theorem.
   The proof already uses Mathlib's compact affine extraction, extensive pullback API and
   cofan composition/reindexing results. The upstream duplicate refinement statement is
   unproved and supplies no shortcut.
4. **Route and pruning: pass after import cleanup.** Read the official Stacks proofs
   [01GJ](https://stacks.math.columbia.edu/tag/01GJ),
   [0DAV](https://stacks.math.columbia.edu/tag/0DAV), and
   [094K](https://stacks.math.columbia.edu/tag/094K). The finite family of all simplex-operator
   pullbacks is covering and stable under composition. The proof then follows the initial,
   successor and assembly construction, finally selecting each identity operator.
   The unit `sk-prop-h2` and its `realized` fields are unchanged; no realized unit step is
   bypassed. Compared the old proof dependencies with the new list: exactly the three
   removed direct geometry edges named under No longer needed are dropped. Existing item
   imports remain used by its retained proofs. Removed the two redundant new-module imports
   listed above; their declarations remain available through public imports.
5. **DAG: pass.** The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   Each of the five new nodes has source, creation, searches, blueprint, chapter/unit and
   Lean records; its Lean signature matches its module. For every delivered node,
   `proof_deps` equals the union of the proof steps' `uses`. The successor node names the
   boundary, relative cover and explicit attachment declarations actually used. The
   assembly node explicitly records its use of the proved private transport/matching
   helpers via proof-only `import all`; no new unproved assembly principle is hidden.

This reading changed only the two redundant imports and this report. It closes the original
hole `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_refinement_solving_local_requirements`
(1), adds no holes (0), and leaves no sorry in any delivered module. It is not a decomposition
into additional holes. No existing signature, definition, proof route at unit level, or node
statement was changed by the second reading.
