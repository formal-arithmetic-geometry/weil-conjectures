## What changed

Closed the private `AlgebraicGeometry.Scheme.Modules.stalk_free_of_restrict_iso`
proof. The restriction-adjunction units restrict to isomorphisms because open
pushforward is fully faithful. The existing `stalk_bijective_of_restrict_iso`
helper turns their stalk maps into linear equivalences. Between those two stalk
maps, push forward the supplied trivialization composed with `restrictUnitIso`.
Finally compose with the existing source-library `Scheme.unit_stalk_iso`.

Added the proof-only import `Mathlib.CategoryTheory.Adjunction.FullyFaithful`.
Replaced the retired `all Sheaf.AlgebraicGeometry.IdealModuleProductStalk`
wrapper import with `all WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk`
to access the source library's private, already proved unit-stalk theorem.
The mathematical route and all existing statements are unchanged. The second reading below records import pruning and the matching DAG corrections.

The complete module compiles cleanly in about four seconds through `lcompile.py`.
`#print axioms birational_line_pushforward_generic_stalk` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.stalk_free_of_restrict_iso` (1 of 1
original holes). Consequently `birational_line_pushforward_generic_stalk` now
has no sorry dependency. Zero holes remain in the module; zero holes were added
or split off.

## No longer needed

Removed the retired `Sheaf.AlgebraicGeometry.IdealModuleProductStalk` wrapper
import, replacing it directly with its source-library implementation. The
underlying node `lem-weil-pbc-ideal-module-product-stalk` remains needed for its
proved private unit-stalk comparison. The second reading additionally removes the unused `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` import, replacing it with the already proved underived `WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward` API. Its old dependency `lem-pc-sections-open-base-change` is pruned from this proof, replaced by the attachment `lem-pc-module-pushforward-open-restriction`. The unused curve-specific `def-sc-function-field` dependency (module `Sheaf.AlgebraicGeometry.FunctionField`, never imported here) is removed from the DAG route: the proof uses the Mathlib field instance at the generic point of an integral scheme, recorded under `def-pc-integral-scheme`. `Mathlib.AlgebraicGeometry.FunctionField` remains needed only in the proof, so its import is now plain `import`. No claim is made that these modules have become unreachable from every target; that is measured by the ledger.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof-origin note says the three local stalk helpers were fully proved,
while the checked module still contained a `sorry` in
`stalk_free_of_restrict_iso`. This delivery completes precisely the recorded
adjunction-unit argument, without changing any statement or the unit's route.
The private unit-stalk theorem is now in the source-library module rather than
in the retired Sheaf wrapper.

## Second reading by F1

1. **Statements and visible data: pass.** Read the complete repository/sandbox
   diff. The only Lean changes relative to the repository are the body of
   `stalk_free_of_restrict_iso` and imports. All four existing declaration
   signatures, their visibility, and their docstrings are byte-for-byte unchanged.
   No definitions, targets, hypotheses, or conclusions changed. The only direct
   user, `ChowFiniteCohomologyWitness`, already imports `FunctionField` explicitly.
2. **Proof and axioms: pass.** Independently compiled the delivered module cleanly
   through `lcompile.py` (3.4 seconds after import pruning). A full scratch copy
   with `#print axioms` checked `stalk_bijective_of_restrict_iso`,
   `stalk_free_of_restrict_iso`, `line_pushforward_stalk_on_iso_open`, and
   `birational_line_pushforward_generic_stalk`, as well as the reused
   `pushforwardRestrictIso` and `Scheme.unit_stalk_iso`: each uses precisely
   `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, forbidden
   declaration, hollow definition, or arbitrary witness from an unproved theorem.
   The new argument first makes the restricted adjunction units invertible by
   full faithfulness, obtains linear ambient-stalk equivalences from their
   bijectivity, and composes with pushforward of the supplied trivialization and
   the structure-module stalk comparison. The orientation and scalar rings of
   all four isomorphisms match.
3. **Split statements: pass; none.** No holes or new Lean declarations are added.
   The new DAG node merely attaches the existing, axiom-checked
   `pushforwardRestrictIso`. Read its entire implementation, including the
   component-isomorphism argument. Its hypotheses are a cartesian square of
   schemes with open horizontal maps and an arbitrary module; the natural
   isomorphism is exactly its recorded statement. Empty opens and the identity
   square satisfy the same sectionwise equality. Searches of all DAG Lean
   records found no attachment of this construction; the existing open/open
   pushforward node requires the vertical map also open and does not cover this
   use. Blueprint searches and recorded LeanSearch, Loogle, and grep searches
   produced no duplicate or exact Mathlib replacement.
4. **Top-down proof, pruning, and route: pass after repairs.** Read Stacks
   `coherent.tex`, Tag 02O5, the paragraph establishing property (a), together
   with the preceding closed-pushforward generic-stalk paragraph. The Lean
   handles precisely the local rank-one argument, with closed-immersion scalar
   compatibility, and requires none of the surrounding coherence/properness
   assumptions. The generic point lies in the dense open because the integral
   scheme is nonempty and irreducible. Local trivialization and the open-stalk
   comparison need no integrality; an empty trivializing open cannot contain
   the supplied point. The residue map is bijective at the generic local field;
   the closed-immersion stalk map supplies the required residue-field lift.
   Existing library comparisons are reused. Removed the unused derived
   `Sections` import and made `FunctionField` proof-only. The other imports
   supply the displayed signature or named constructions in the proof.
   Read `dag/units/sk-thm-picard-coherence.json`: its recorded `realized` arrays
   are empty already, and are untouched. This repair preserves its proper
   coherence/Chow route; only the underived supporting comparison is recorded
   more accurately.
5. **DAG agreement: pass after repairs.** Read the item's node and the statement
   and Lean record of every old proof dependency. Replaced the stale reference
   to `pushforward_restrict_square` by the actually used
   `pushforwardRestrictIso`, replaced its derived dependency by the new existing
   declaration attachment, removed the unused curve-function-field dependency,
   and corrected `proof_origin` to describe the now completed unit argument.
   The remaining steps match the open-stalk comparison, closed-pushforward
   scalar rule, and residue-map calculation. `proof_deps` equals the union of
   step uses. The item's statement and Lean record are unchanged; the new
   node has its full schema, source, proof steps, searches, blueprint origin,
   and verbatim existing Lean signature.

Second-reading changes: import pruning/visibility, the corresponding import
change record, and DAG/report corrections only; the first worker's proof body was correct and was retained.

## New nodes

`lem-pc-module-pushforward-open-restriction` attaches the already proved
`AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso` in
`WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward` (lines 86-96,
with its construction and component proof at lines 56-80). It is the ordinary
cartesian open-restriction comparison used here, with no new Lean statement,
no added hole, and no finiteness hypothesis. Its natural-language proof follows
that source implementation. The three recorded searches are actual calls from
this second reading; direct inspection found the exact source-library match.
The blueprint origin follows the item's existing `blueprint.from` record.
Change record: `coord/changes/BirationalLinePushforwardGenericStalkImports.md`.
The preflight requires it for removed imports/public-import privatization; it
records every transitive downstream module, the sole direct importer's explicit
FunctionField import, and why no adaptation or statement/definition change is
needed. The first dry run also caught and corrected a metadata-only schema
error: an existing-declaration attachment must omit `lean.file`.
