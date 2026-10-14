## What changed

Proved the two remaining moduleCup naturality theorems in
Sheaf.Paper.CechCupPullbackCompat. Their proofs lift arbitrary cohomology classes
to concrete resolution cycles, form the product cycle using Leibniz, transport
all three cycles through the existing resolution maps, and apply the two cup
characterizations. Three private helpers supply resolution-class surjectivity,
pairing closure and additive cycle transport across scalar rings.

The composition comparison now directly uses cechRefinement_comparison_square,
removing the auxiliary cup products and their comparison-existence dependency.
The added proof imports ModuleCupCoefficientResolutionMaps and
ModuleCupPullbackResolutionMaps are plain imports. Every existing mathematical
signature and definition is unchanged.

The second reading removed the unnecessary instance-name edits in
GlobalTensorPullbackMonoidalNormalization and ModuleCupNaiveDerivedCompatibility
and both associated change records. Neither dependency module is delivered.
It also corrected the DAG's description and citation of the imported Leibniz
identity. Only the item's Lean module, its proof metadata and this report remain.

## Proved and sorry left

Closed both original local holes of node
lem-sc-picard-cech-cup-pullback-compat:

- AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality
- AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality

Holes added: none. Statements split off: none. No textual sorry remains in the
item. Its seven public theorem bodies are complete. Axiom checks show permitted
axioms only for coefficient naturality and the four Cech naturality theorems;
cechCupPullbackCompat and moduleCup_pullback_naturality additionally reach
existing imported sorryAx. This is two local holes closed, not a claim of a
complete transitive proof or a measurement of the global sorry ledger.

## No longer needed

Removed the proof import Sheaf.Paper.CechComparisonMapNaturality and node
lem-sc-cech-comparison-map-naturality from proof_deps. The composition comparison
uses Sheaf.Paper.CechRefinementComparisonSquare directly. Comparing old and new
proof_deps gives exactly that one removed node. No public import is removed;
no other proof dependency or unit realization is pruned. Removal of a direct
import does not assert that the module leaves the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier package included two dependency instance-name repairs for a reported
ordinary-import collision. The return required those non-forced edits to be
removed. Independently compiled copies of both repository dependencies unchanged
in a scratch overlay: GlobalTensorPullbackMonoidalNormalization 13.0 s and
ModuleCupNaiveDerivedCompatibility 38.7 s. Both compile cleanly. The proposed item
also compiled cleanly in 40.2 s without the renames, and its ordinary-import probe
ran all seven public axiom checks in 1.7 s against those original dependency
outputs. The current environment therefore does not require those repairs.
Removed both modified dependency sources and both change records from delivery,
and retired their compiled overlay to the item's scratchpad. The final delivery
uses the original library dependencies.

The DAG's Step 2 described construction of a total tensor complex and expansion
of its signed differential. This module actually uses the already proved
cechCupCochain_leibniz theorem of def-sc-cech-cup-product. Updated that step to
cite the existing node and describe kernel differential vanishing and bilinearity;
updated proof_origin. The existing dependency union stays unchanged.

## Second reading by J4

1. Compared every proposed Lean module with the repository by diff, and checked
   every existing theorem, definition and abbreviation signature as literal
   text. All mathematical signatures and existing definitions are unchanged.
   Removed the dependency-module instance renames and their records after
   verifying the original dependencies and complete item import compile without
   them. The only delivered Lean file is CechCupPullbackCompat. No target,
   hypothesis or conclusion changes. Verdict: pass after pruning those edits.
2. Independently compiled the final item alone in 38.1 s and an ordinary-import
   scratch probe in 1.6 s that prints the axioms of all seven public theorems. Scanned the source: no sorry,
   forbidden declaration mechanism, hollow definition, or line over 100
   characters. Five public theorems use only propext, Classical.choice and
   Quot.sound; the main compatibility and pullback naturality retain the
   reported imported sorryAx dependencies. map_additive_cycle constructs its
   underlying element as the degree map applied to the input cycle and proves
   closure using the cochain map equation. Existential resolution witnesses are
   eliminated only inside theorem proofs, never used to define public data.
   Verdict: pass with the stated imported holes.
3. No statement was split off and no hole was added. Checked all three new
   private helpers: class surjectivity composes the homology projection with
   two isomorphisms, pairing closure uses Leibniz and zero differentials, and
   additive cycle transport uses differential commutation. These proofs include
   degree zero, zero coefficients and empty schemes without extra assumptions;
   additive transport does not require equal scalar rings. Searched Sheaf and
   the upstream source for class surjectivity and resolution pairing closure.
   Equivalent helpers in ModuleCohomologyCupProduct are private and unavailable
   through ordinary imports. Loogle's Function.Surjective,
   HomologicalComplex.homologyMap query returned zero hits. LeanFinder's
   cross-ring cycle query returned generic cyclesMk and HomComplex facts, with
   no shorter replacement for the concrete kernel constructor. Verdict: pass.
4. Read all seven proofs and the exact resolution-map statements. Each newly
   closed naturality lifts two arbitrary classes, forms their product cycle,
   transports the three cycles, uses the pairing equation and three class
   equations, and applies the source and target IsModuleCupProduct
   characterizations. It is a genuine reduction to resolution maps. The
   coefficient route is axiom-clean; the pullback route has the reported
   imported holes. Composition directly applies the refinement comparison
   square. All retained imports serve signatures or proofs; both new imports
   are plain imports. The old/new proof_deps difference matches No longer
   needed. Checked sk-prop-av-cube.realized: its statement and step lists are
   empty in the current repository; this delivery changes no unit realization
   or route. Verdict: pass.
5. Parsed both node records. Only proof, proof_deps and proof_origin differ;
   proof_deps is exactly the union of step uses. Both added dependencies name
   the resolution-map theorems the Lean proof actually applies. Corrected
   Step 2's stale attribution of the signed Leibniz proof and cited its
   existing def-sc-cech-cup-product node, which explicitly records
   cechCupCochain_leibniz. Updated proof_origin. No new node or mathematical
   statement is introduced. Verdict: pass after that metadata repair.

Second reading changed the package by withdrawing two unnecessary dependency
instance repairs and their change records, correcting the DAG's Leibniz
attribution and citation, and updating this report. The item's Lean proof
needed no further edit. Holes closed: moduleCup_coefficient_naturality and
moduleCup_pullback_naturality in AlgebraicGeometry.Scheme.Modules. Holes added:
none.
