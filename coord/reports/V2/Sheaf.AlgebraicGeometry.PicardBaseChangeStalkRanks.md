## What changed

The original signature and docstring of `picardRankMatch_baseChange_stalk_ranks` are unchanged.
Its proof now obtains independent finite bases and equality of finranks, identifies their
cardinalities with `Module.finrank_eq_card_basis` and `Fintype.card_fin`, then uses
`Module.Finite.of_basis` and `Module.Basis.equiv` to finish. The two new modules are imported
only for this proof. Removed the redundant direct public import of
`Mathlib.AlgebraicGeometry.Morphisms.Flat`; the remaining public `FlatPullbackStalk` import
already exports it. The public signature still needs `FinitePresentation`.

The first worker's `PicardBaseChangeStalkRanksAux` module and its proposed node were removed:
its common-basis statement repackaged essentially the whole geometric argument. Replaced it
with `PicardBaseChangeStalkFiniteBases` (independent finite bases, no comparison) and
`PicardBaseChangeStalkFinrankEq` (numerical equality, no finite freeness). Each is a strict
part of the argument. No definition, existing statement, or unit route was changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_ranks`.

Holes added and still open:
- `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finite_bases`, node
  `lem-sc-picard-base-change-stalk-finite-bases`;
- `AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_finrank_eq`, node
  `lem-sc-picard-base-change-stalk-finrank-eq`.

This is a decomposition, not a completed geometric proof: one hole closed and two added,
net holes closed minus added = -1. The target still depends on `sorryAx` through these
statements (and potentially existing dependencies). The old proposed common-basis hole is
not delivered. No definition chooses any data from these existence statements.

## No longer needed

Removed direct import: `Mathlib.AlgebraicGeometry.Morphisms.Flat` (already publicly exported
by `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`). No library module becomes
unreachable from this removal; no globally pruned modules are claimed.

Every old direct `proof_deps` entry of `lem-sc-picard-base-change-stalk-ranks` is now used
only by the lower geometric statements: `def-sc-picard-universal-rank-match`,
`def-sc-finite-locally-free-sheaf`, `lem-weil-pbc-module-stalk-pullback`,
`lem-pc-module-pullback-identity-composition`, `def-pc-base-change`,
`lem-sc-finite-locally-free-stalk-finrank`, and `def-weil-proper-morphism`.
They have been replaced in the target node's direct `proof_deps` by the two new nodes;
none is claimed globally obsolete. The discarded auxiliary module/node was never landed.

## Where the brief, the DAG or earlier work was wrong

Return B9 (reviewer X-955a9, head 955a96ae5) repaired: both new nodes now name
`thm-sc-theorem-of-cube` as `blueprint.from.node`, with the exact requested proof
places and the five-node `via` chain through the Picard common-rank reduction.
Their earlier provenance incorrectly stopped at the non-blueprint stalk-ranks node.

The earlier worker called its common-basis assertion a strictly lower geometric statement,
but it bundled finite freeness and rank equality together. That is substantially the
original argument under a stronger conclusion and is inadequate as a strict-part split.
The repaired reduction isolates those two logical tasks and combines them in Lean.

The earlier auxiliary docstring and node gave only a sketch, and the delivered sandbox had
no updated target node. Both defects were repaired. Stacks 0BDP supplies the rank-reduction
context rather than this exact generality; the frame and empty-fibre arguments are an
explicit agent expansion using 01C6 and 0098, recorded as such in `proof_origin`.

## New nodes

`lem-sc-picard-base-change-stalk-finite-bases` constructs finite bases separately, using
local frames supplied by the universal rank condition and tensor-pullback stalk transport.
It does not compare the ranks and needs no empty-fibre argument.

`lem-sc-picard-base-change-stalk-finrank-eq` compares the two numerical finranks using a
point in a common residue-field extension, or zero stalks on the complement of the proper
image for an empty fibre. It asserts neither finite generation nor a linear equivalence.

Change record: `coord/changes/PicardBaseChangeStalkRanksImports.md` documents the redundant
public-import edge removal and every downstream user. All existing signatures and
definitions are preserved.

## Earlier second reading (a previous round; superseded)

1. Compared the complete original module with the sandbox using `diff`. The sole existing
   declaration's signature is byte-for-byte identical, and its docstring is unchanged.
   Only its proof and imports changed. The new statements are in their own new modules;
   no existing definition or other module was changed. Verdict: pass.
2. Compiled all three modules locally in import order with `lcompile.py`, without errors
   or warnings. Scratch copies with `#print axioms` for all three declarations showed only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Exactly the two reported named
   theorems have `sorry`; no forbidden declaration form or hollow definition occurs.
   Verdict: pass as a decomposition, with geometric holes remaining.
3. Read the definitions and relevant existing stalk, composition, and finite-local-freeness
   declarations. Searched Mathlib through leanfinder, loogle and grep with different queries,
   and searched repository/upstream Lean sources. Generic basis and finrank lemmas were
   found and used; no exact geometric specialization was found. Both splits are true and
   strict parts: independent finite bases do not imply their ranks agree, and numerical
   finrank equality alone does not imply freeness or finite generation. For a nonempty
   fibre, the common field extension supplies the comparison point; for an empty fibre,
   both stalks are zero. Zero-rank frames give empty bases; empty T\prime has no point t.
   No arbitrary witness enters a definition. Verdict: pass after replacing the old split
   and supplying complete proof docstrings and node records.
4. The target opens its hole and finishes using generic proved basis lemmas, after the two
   explicitly isolated geometric facts. Imports were checked; the redundant Flat import
   was removed. Every former direct proof dependency is listed above and retained only
   in the lower plans where needed. `dag/units/sk-prop-av-cube.json` was read: its realized
   arrays are presently empty, and the general-cube route and all its entries are unchanged.
   Verdict: pass; no unit-level bypass or claimed global pruning.
5. Read the updated target node and both new nodes against Lean. The target proof and
   proof dependencies now name exactly the two facts it invokes; the new nodes have
   verbatim Lean signatures, complete natural-language plans, sources, search records,
   creation, blueprint, chapter/unit and Lean records. Verdict: pass.

LeanSearch was also attempted for each split and returned Internal Server Error; its
unavailability is recorded, alongside the successful leanfinder, loogle and grep searches.
The dry run required a public-import change record, now supplied with all downstream users.

Second reading changed the split, target proof, proof-dependency records, redundant import,
change record, and report. No target statement or definition changed.

## Second reading by V2

1. Compared every delivered module with the repository. The only existing module changes
   imports and its proof; the existing signature is byte-for-byte identical and its
   docstring unchanged. The public Flat edge removal has the supplied change record;
   FlatPullbackStalk publicly exports Flat. No existing definition changes. Verdict: pass.
2. Independently compiled all three modules in import order with lcompile.py. All compile
   without errors or warnings. Recompiled temporary probe copies with #print axioms for
   each declaration: only propext, Classical.choice, Quot.sound and sorryAx occur. The
   only two sorries are the reported named split theorems; no forbidden declaration forms
   or definitions occur in the delivered files. Verdict: pass as a decomposition.
3. Read PicardUniversalRankMatch and the existing stalk-rank and pullback ingredients.
   Independently searched leanfinder for locally free direct-image pullback stalk bases,
   loogle for Module.Basis.equiv, grep for stalk bases and pullback finrank, and repository
   Lean sources. The hits give generic algebra, localization and stalk tools, not either
   missing geometric comparison. No short closure of either split was found. Checked
   the two arguments separately: hR at the identity and at h supplies the two local frames;
   a common residue-field extension compares ranks on a nonempty fibre; properness gives
   an open complement on which both direct images vanish for an empty fibre. Rank-zero
   frames give empty bases; an empty base has no t. Both lower statements are true strict
   parts, and neither merely renames the original conclusion. No witness is used to
   define data. Verdict: pass, with both geometric proofs still open.
4. The final proof uses the two geometric components and standard finite-basis algebra.
   Proof-only imports are plain imports. Checked the removed public Flat edge and every
   old proof dependency against the report. No globally unreachable module is claimed.
   Read sk-prop-av-cube.json: its realized arrays remain empty in the repository; this
   delivery preserves its general-cube route and changes no unit record. Verdict: pass.
5. Compared all three node Lean signatures exactly with their source text, and checked
   proof_deps equals the union of proof-step uses. Existing-node edits are confined to
   proof, proof_deps and proof_origin. Both new nodes have the required source, searches,
   creation, chapter, unit and Lean fields, with blueprint provenance through the existing
   five-node chain to thm-sc-theorem-of-cube. Verdict: pass.

Rechecked the cited sources directly: [Stacks 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
provides the rank-reduction context, [01C6](https://stacks.math.columbia.edu/tag/01C6)
defines finite local frames, and [0098](https://stacks.math.columbia.edu/tag/0098)
gives the tensor-pullback stalk formula. The empty-fibre extension is correctly identified
as an agent argument rather than an exact statement of 0BDP.

This second reading changed only this report and added independent search/probe evidence.
No Lean or node repair was needed. One original hole is closed and two are added: net -1,
so this delivery records a decomposition rather than a completed geometric proof.
