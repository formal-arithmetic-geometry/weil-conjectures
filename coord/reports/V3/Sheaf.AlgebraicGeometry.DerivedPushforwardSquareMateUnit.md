## What changed

Replaced the target's `sorry` by a concrete ordinary comparison and a categorical
pasting argument. The proof uses the existing `derivedDirectImage_square_mate`
and `exists_derivedModuleDirectImageComposition` theorems, together with the
strictly smaller single-unit equality-transport statement. All calculations are
in the target module; no mate-equation theorem is split off. The target's public
signature is unchanged.

Added `Sheaf.AlgebraicGeometry.DirectImageSquareUnitTransport`, containing the
concrete `directImageSquareIso`, its proved whole-space identity
`directImageSquareIso_top`, and the documented transport obligation. Its public
SchemeDerivedDirectImage import provides the data and signatures. The target's two additional imports
are plain proof-only imports. Three proved private helpers provide the generic
isomorphism pasting, equality of the two pinned adjunction names, and congruence
of their composite mates. The homotopy object stays arbitrary; no representative
complex is introduced. File-local reducibility and preserved `let` bindings avoid
repeated expansion of chosen derived-functor data.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit`. Proved
`AlgebraicGeometry.directImageSquareIso_top` about the explicit comparison.
Added exactly one hole:
`AlgebraicGeometry.directImageSquare_unit_transport`, node
`lem-pc-direct-image-square-unit-transport`. There are no holes in definitions.
This is a decomposition (one original hole closed, one new smaller hole added),
not a net reduction of holes and not an axiom-free proof of the target.
The imported results retain their existing upstream proof dependencies; this
delivery does not close those dependencies.

## No longer needed

The original direct proof dependencies
`def-pc-derived-base-change-map` and
`lem-pc-ringed-spaces-derived-pullback-composition` are no longer direct proof
steps. They remain statement/transitive dependencies because the target fixes
these definitions and composition choices. The public
`AffineGlobalHomBaseChangeMap` import therefore remains.
Pruned the redundant direct import `Mathlib.AlgebraicGeometry.Modules.Sheaf`
from the new transport module in the second reading: SchemeDerivedDirectImage
already publicly imports it through DerivedCategory. No existing library module
becomes unreachable: pruned none.

Removed the first reader's proposed
`DerivedPushforwardSquareMateEquation` module and
`lem-pc-derived-pushforward-square-mate-equation` node from the delivery, together
with its unnecessary elaboration-only change record. These were never landed
library dependencies. Removed unused simplification arguments and unused earlier helpers. The new
private helpers are all proved and used.

## Where the brief, the DAG or earlier work was wrong

The first report called the new single-unit transport obligation an existing
hole and omitted it from the added-hole count. It also introduced an almost
complete mate-equation hole expressly to bypass the compiler time limit. That
split is removed: the existing normalized square-mate theorem supplies the
mate calculation, and the remaining argument actually pastes its equation with
the two composition-unit equations. The target statement and definitions used
by existing targets are unchanged. A change record documents the preflight's
classification of local reducibility commands; these change no public statement
or definition. In this resumed attempt, direct equality-isomorphism alternatives
were tested with compiler profiling. They caused expensive conversion of the
composite sheaf functors and were discarded; the delivery retains the explicit
pushforward composition construction. Development probes and the inherited
second-reading section were removed from the delivery for the next reader.
The inherited concrete calculation timed out on this machine. Profiling isolated
repeated conversion of the canonical and scheme-Hom adjunction names inside
conjugateEquiv. Explicit adjunction equality followed by congrArg₂ replaces that
conversion, and the complete main module compiled cleanly in 55.6 seconds.
No file was split and no limit was raised.

## New nodes

Change record: `coord/changes/DerivedPushforwardSquareMateUnit-local-reducibility.md`
documents file-local proof elaboration attributes flagged by preflight.

`lem-pc-direct-image-square-unit-transport` states equality transport of one
right-derived unit across the explicit ordinary comparison, for arbitrary
commutative squares of schemes. Its source, complete verbal proof, three kinds
of search, provenance, chapter/unit, blueprint relation, and verbatim Lean
statement are recorded in
`dag/nodes/sec-picard-framework/lem-pc-direct-image-square-unit-transport.json`.
It contains no adjunction, pullback mate, or derived composition comparison.

## Second reading by V3

1. Compared both delivered modules against the repository: the transport module
   is new, and the existing target signature is byte-for-byte identical. The
   existing node differs only in `proof`, `proof_deps`, and `proof_origin`.
   The two added target imports are proof-only. Local irreducibility attributes
   are scoped to this file and are accurately documented by the change record.
   No existing public definition or statement changes. Verdict: pass.
2. Compiled both modules in import order with `lcompile.py`: the transport
   module took 36.1 seconds and the target 55.2 seconds, with no warnings or
   errors. The target has no direct holes; the sole added hole is the named
   `AlgebraicGeometry.directImageSquare_unit_transport`. No forbidden declarations
   or hollow definitions occur. The explicit comparison uses Mathlib's actual
   pushforward composition and equality maps, not an arbitrary chosen witness.
   Separate scratch copies compiled with `#print axioms` for all four public
   declarations. `directImageSquareIso` and `directImageSquareIso_top` use only
   propext, Classical.choice, and Quot.sound. The transport theorem and the
   target additionally use sorryAx, as their open dependencies require.
   No other axiom appears.
   Verdict: pass, with the documented upstream and transport proof dependencies.
3. Read the entire split-off statement and its verbal proof. Mathlib's
   `SheafOfModules.pushforwardComp` is `Iso.refl`; scheme pushforwardCongr is
   identity when its equality is reflexive, by the component formulas and
   extensionality. Equality induction on the two composite morphisms therefore
   gives the transport law for their chosen units. This works on arbitrary
   homotopy objects, zero complexes, identity squares, and empty schemes: there
   is no unit cancellation or unstated acyclicity condition. It is strictly
   smaller than the target: no derived adjunction, mate, or composition choice
   occurs. Independently searched leanfinder, loogle, Mathlib, Sheaf, and the
   upstream library using equality-family and homotopy-comparison queries.
   Generic transport lemmas exist, but no duplicate of the concrete theorem was
   found. Tried to close it by identifying the ordinary comparison with eqToHom
   and then equality induction; two scratch attempts exceeded the unchanged
   60-second file limit, so neither is delivered. Verdict: true and properly
   split off; its complete proof obligation remains explicit.
4. Checked the proof from the target downward: its concrete comparison supplies
   the whole-space identity, the existing square-mate theorem supplies the mate
   formula, the two composition-unit equations supply the outside squares, and
   the small transport lemma supplies the middle. The generic pasting helper
   cancels only isomorphisms. Both additional target imports are used. Removed the transport module's
   redundant direct Mathlib.AlgebraicGeometry.Modules.Sheaf import: the same
   declarations are already public through SchemeDerivedDirectImage and
   DerivedCategory. The original
   public import supplies names in the signature. The old proof dependencies
   omitted by the new direct route are both listed under No longer needed.
   Read `dag/units/sk-thm-picard-duality.json`: its realized fields are unchanged;
   this reduction is below the unit level and bypasses no realized unit step.
   Verdict: pass; no library module is pruned.
5. Checked the nodes against every step of the Lean proof, the union of step
   dependencies, the verbatim transport signature, source/provenance, blueprint
   ancestry, chapter/unit, and the three search kinds. Verified the cited Stacks
   Tags 08HY and 0D5T online because the local cohomology.tex is unavailable.
   Those tags supply the base-change and composition context; the equality
   normalization is the elementary argument written out in the docstring.
   Repaired the new node's omitted statement dependency on
   `def-pc-derived-direct-image` and added explicit provenance and independent
   search evidence. Verdict: pass after this metadata repair.

Second reading changed the new node's statement-dependency documentation,
provenance, and search evidence, and added this review. The only delivered Lean edit was removal of that redundant direct Mathlib
import. The initial dry run flagged it as a missing source despite its local
presence; source inspection independently established it was redundant. The one-closed/one-added decomposition count is accurate.
