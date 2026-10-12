## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`
with a complete Lean reduction. Its signature and visibility are unchanged. Added proof-only
imports of `Mathlib.Algebra.Category.ModuleCat.ExteriorPower` and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso`.

The private helper `exteriorIso` constructs sectionwise exterior isomorphisms, proves
naturality on pure wedges using the existing unique restriction characterization, and
maps the presheaf isomorphism through sheafification. `zeroPushforward` proves pushforward
from an empty scheme is zero, using its subsingleton section rings and `Module.subsingleton`.
`termIso` computes all constant-rank strata and terms. The main proof assembles the complex
isomorphism, checks its zero-differential equations, localizes it, transports the exterior
sheaf, and applies Mathlib's single-functor shift comparison.

The only missing step is exterior-sheaf compatibility with inclusion of the full open.
It is a theorem in a new module with a source and complete proof in words. Updated the
assigned node's proof and dependencies to match. No other existing module was adapted.
Both delivered modules compile with `lcompile.py`. Lines are at most 100 characters.
The new statement was checked on empty X, d=0, non-free M and arbitrary characteristic:
the full-open equivalence and exterior universal property use neither a basis nor division.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.Scheme.Modules.constantRankExterior_derived_iso`
(node `lem-sc-constant-rank-exterior-derived-comparison`). No sorry remains in the assigned
module. This is a reduction, not a claim of an axiom-free final target proof.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_fullOpen_pushforward_iso`
(node `lem-sc-sheaf-exterior-full-open-iso`), in
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso`.
Its whole proof is exactly `:= by sorry`. It concerns only full-open restriction and
exterior sheaves; it has no rank-stratified complex, derived category, shift, second sheaf,
or input isomorphism. The assigned proof supplies all those remaining steps in Lean.

Accounting: one original hole closed, one strictly smaller hole added. This is a
decomposition with net zero direct holes. Existing exterior-sheaf restriction existence
and law theorems remain dependencies; they were neither restated nor modified.

## No longer needed

Removed the redundant direct proof-only import
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf` present in the current repository version;
`LocallyRankedExteriorComplex` already publicly imports it. No node or module leaves the
import closure. Both original public imports are required by the unchanged statement.
All three original proof dependencies remain needed; the full-open compatibility node
is added. Both added proof-only imports are used.
No local-freeness, determinant-duality, Koszul or t-structure modules are imported.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The assigned DAG's first step marked the full-open
exterior/sheafification identification elementary, but the existing interfaces do not
state that compatibility. It is now the one explicit lower lemma; the rank-stratum and
empty-pushforward calculations are proved in the assigned module.

[Stacks Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0) was read online because the
literature checkout is absent here. It supplies the locally constant exterior/shift
expression, not an explicit arbitrary-module theorem for this implementation. The new
lemma's proof is marked agent-written: an expansion of the construction and sheafification
universal property, citing the existing Mathlib module-sheafification adjunction node.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches ran and
their actual results are recorded.

`tools/blueprint_refs.py ancestor` returned None for the assigned node because its
`created.item` is a module name. The new node inherits the assigned node's explicit
`blueprint.from.node = lem-sc-finite-duality` and prepends the assigned node id to its via
list. The unit's statement and route are unchanged.

## New nodes

`lem-sc-sheaf-exterior-full-open-iso` states
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_fullOpen_pushforward_iso` in
`lean/Sheaf/AlgebraicGeometry/Modules/ExteriorSheafFullOpenIso.lean`.
It isolates full-open exterior-sheaf compatibility, the on-stratum part of the assigned
node's first step. Its JSON records the source, three kinds of search, complete proof in
words, statement and proof dependencies, blueprint ancestry and exact Lean signature.
No change record is needed: no existing definition, statement or public import changed.


## Second reading by U2

1. **Interface: pass.** Compared both delivered modules against the read-only repository.
   The sole existing theorem signature is byte-for-byte identical, including universes,
   assumptions, conclusion and visibility. All existing definitions are untouched. The
   new module contains one new theorem; the assigned module adds only private helpers
   and proof-only imports. No change record is needed.
2. **Proof: pass as a decomposition.** Compiled both modules with `lcompile.py`.
   The assigned module has no sorry; the support theorem has exactly its reported
   whole-proof sorry. A scratch copy with `#print axioms` for both public declarations
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The final
   scratch check also covered all three private helpers: `zeroPushforward` uses only
   the three standard axioms; the other helpers have the expected upstream holes.
   This final scratch copy compiled without warnings in 21.7 seconds. Inspected all
   helpers: no forbidden declarations or hollow data. `exteriorIso` constructs its
   maps sectionwise; the existing choice of restrictions is uniquely characterized.
   Component isomorphisms are chosen within a theorem proof, not exposed as data in
   a public definition. The first main-module compile timed out at 60 seconds; an
   unchanged retry compiled in 51.6 seconds, and the diagnostic scratch copy in 51.4.
   A later dry run timed out again. Profiling isolated the nested naturality equality
   composition. Replaced it by explicit-scalar exterior-map lemmas and sequential
   rewrites of the same equalities; the adjusted module compiled in 24.3 seconds.
3. **Split lemma: pass.** Its full-open inclusion is `X.topIso.hom`; transport through
   this scheme isomorphism identifies scalar rings, module sections and covers.
   Exterior universal properties and sheafification then give the claimed isomorphism.
   Checked empty X, d=0, d=1, arbitrary non-free modules and positive characteristic:
   no basis, division or rank assumption is required. This is strictly smaller than
   the original derived comparison and does not restate it. Its complete docstring
   proof and node agree. Independently searched with LeanFinder for invariance under
   ringed-space isomorphisms, Loogle for restriction/pushforward, and Mathlib/source
   grep for exterior and sheafification transport. The adjunction counit identifies
   restriction after pushforward, but does not identify the exterior construction;
   generic sheafification transport results likewise leave that compatibility step.
   No existing exact theorem or few-minute proof closing this lemma was found.
4. **Route and pruning: pass after report correction.** Read the proof top downward:
   pure-wedge naturality, constant rank strata, empty pushforward, the single complex,
   and Mathlib's derived single/shift comparison implement the original route. All
   three original proof dependencies are used; none is bypassed. Both public imports
   are needed, and both added imports are proof-only and used. Corrected the pruning
   report to include the redundant direct `ExteriorSheaf` import removed relative to
   the current repository. No module is pruned. The unit's `realized` record has an
   empty statement list and one empty step list, unchanged by this delivery; this
   below-unit reduction changes neither its statement nor its route.
5. **DAG: pass.** Compared the assigned JSON with the repository: only `proof`,
   `proof_deps`, and `proof_origin` differ. Each proof step names its actual Lean
   construction, and the dependency set equals the union of its uses. Checked the
   new node's source, agent-written proof origin, three recorded search kinds,
   statement/proof dependencies, creation data, blueprint ancestry, chapter/unit,
   status and exact Lean signature. Tag 0BR0 provides the motivating exterior/shift
   expression; the transport proof is explicitly agent-written, not attributed to
   that tag as a verbatim theorem.

Second-reading changes: made the scalar rings explicit in the two pure-wedge map
lemmas and replaced the nested equality composition by sequential rewrites, reducing
elaboration time. Corrected redundant-import accounting and added this review.
No statement, definition interface, or node required repair. One original direct
hole is closed and one strictly smaller hole added: net zero, a decomposition.
