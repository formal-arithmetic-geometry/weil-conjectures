## What changed

Proved `CategoryTheory.Functor.rightDerivedBottom_cycle_transport` with its original
signature and explicit comparison unchanged. Added three fully proved constituent modules:
`DerivedBottomInclusion`, `DerivedCyclesMap`, and `DerivedCyclesUnitNaturality`.
The target imports the first and third only for its proof. The cycle-map module is
publicly imported by the unit-naturality module because its statement uses that map.

The proof constructs the map from the single object of cycles to K, uses actual derived-unit
naturality, factors the resulting map into the lower truncation through its canonical
bottom-homology inclusion, and cancels the three maps of that inclusion against the
specified double-truncation comparison. Naturality of the single unit follows from the
already proved shift normalization. All constructions are explicit; no data are chosen
from an unproved existence theorem.

Updated the item's proof dependencies and added nodes for the three proved constituent
calculations. No existing definition, statement, visibility, or public import changed.

## Proved and sorry left

Closed the item's sole hole:
`CategoryTheory.Functor.rightDerivedBottom_cycle_transport`
(`new-lem-pc-derived-bottom-cycle-transport`).

Also fully proved:
- `DerivedCategory.Plus.single_map_bottomHomologyInclusion`
  (`new-lem-pc-derived-bottom-inclusion`).
- `DerivedCategory.cyclesDerivedMap_homology`
  (`new-lem-pc-derived-cycles-map-homology`).
- `CategoryTheory.Functor.rightDerived_cycles_unit_naturality`
  (`new-lem-pc-derived-cycles-unit-naturality`).

No `sorry` remains in any delivered module. Holes closed: 1; holes added: 0.
This is a proof, not a decomposition. `lcompile.py --all` compiles all four modules
without errors or warnings. Individual `#print axioms` checks for all four theorems
show exactly `propext`, `Classical.choice`, and `Quot.sound`.

Edge cases are covered uniformly: n is any integer, including negative values;
zero objects and acyclic K need no exception. The bottom inclusion requires only
vanishing below n, not vanishing above n. The cycle-unit naturality theorem is
proved for arbitrary bounded-below M and q and does not require left exactness.

## No longer needed

No existing imports were removed and no library module becomes globally unreachable.
In the new `DerivedCyclesMap` module, the second reader replaced
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus` with the smaller
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`; no bounded-below API is
used in that module. This does not prune a module from the target import closure.
The node `new-def-pc-derived-bottom-comparison` is no longer a proof dependency of this
item, and its module `Sheaf.CategoryTheory.Abelian.DerivedBottomComparison` need not be
imported for this proof. Its statement-context reference remains. The explicit
`rightDerivedBottomToSingleIso` construction remains unchanged.

The proof does not need a separate smart lower-truncation model or a chain-level
identification of its bottom cycles: the single-cycles map and the canonical bottom
inclusion supply those comparisons directly. No DAG node for those unused modeling
steps existed among the item's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original one-step plan did not
name the canonical-map comparisons needed for implementation. These are now proved
in three reusable modules, retaining the double-truncation and actual-unit route.
The unit record's realized statement and step lists are empty; no unit step was bypassed.

The first single-file compile could not find the recently landed normalization dependency;
`lcompile.py --all` resolved it using the available local compile mechanism. This did
not require a library adaptation or a tool change.

## New nodes

`new-lem-pc-derived-bottom-inclusion`: defines the canonical bottom-homology inclusion
and proves factorization of every morphism from a single object into an object
concentrated in degrees at least n. Uses the existing double-truncation homology formula
and single-source homology extensionality.

`new-lem-pc-derived-cycles-map-homology`: constructs the single-cycles chain map and its
localized map and proves its homology is the canonical homology quotient, with the
specified localization comparison.

`new-lem-pc-derived-cycles-unit-naturality`: proves actual derived-unit naturality on
the canonical cycle map, including bounded-below/unbounded compatibility, for any
bounded-below target. It uses the preceding proved cycle-map formula and the defining
rightDerivedNatTrans_app equation of the uniqueness comparison.

All sources are the parent's canonical-map elaboration of Stacks Tags 05TC (2) and
05TD (3). LeanFinder, Loogle, and source grep found constituent APIs, and no duplicate
of the delivered canonical formulas. No change records are needed.

## Second reading by R2

1. Compared the delivered item with the repository using diff. Restored one extra
   space before the theorem's proof separator; its signature is now byte for byte
   identical. The entire existing `rightDerivedBottomToSingleIso` definition is
   byte for byte identical. The only import additions to the existing module are
   private proof imports. The other three modules are new. No interface change or
   change record is needed. Verdict: pass.
2. Independently compiled all four modules in import order with `lcompile.py --all`,
   without errors or warnings. Searched all delivered Lean for holes and forbidden
   declarations: none. A scratch check of the four theorems, existing comparison,
   bottom inclusion, chain map and localized map shows only `propext`,
   `Classical.choice`, and `Quot.sound` for every declaration. The constructions
   use explicit maps, canonical inverses, and fully faithful preimages; none
   chooses data from an unproved existence theorem. Verdict: pass.
3. There are no unfinished split-off statements. Read each of the three proved
   constituent statements and its docstring argument. The inclusion factorization
   requires M to vanish below n, and does not mistakenly require an upper bound;
   on a single object it reduces to single/homology naturality. The cycle formula
   reduces to the inclusion followed by the quotient even with incoming boundaries.
   Unit naturality allows arbitrary q and does not require left exactness. Zero
   objects, zero maps, acyclic complexes and negative n create no exception.
   Independent LeanFinder, Loogle and grep searches with different wording, plus
   searches of Sheaf and the upstream source, found supporting APIs rather than a
   duplicate integer-degree canonical formula. The upstream degree-zero homology
   calculation does not directly replace the integer-degree result. Verdict: pass.
4. Read the proof from the original equation down to the three proved constituents:
   cycle-map homology, actual-unit naturality and bottom factorization. These are
   proper parts of the argument, not restatements. Existing comparisons and
   extensionality APIs are used rather than restated. Narrowed the new cycle-map
   import to Mathlib FullyFaithful, then recompiled the entire set. The old
   proof-dependency difference consists precisely of
   `new-def-pc-derived-bottom-comparison`, already listed above as no longer needed
   for the proof. No module becomes unreachable. Checked
   `dag/units/sk-thm-picard-semicon.json`: its realized statement and sole step
   lists are empty; the unit route has not been bypassed. Verdict: pass.
5. Compared the existing node: only `proof`, `proof_deps` and `proof_origin` differ.
   Their steps describe the actual factorization, unit calculation, shift-unit
   naturality and cancellation. Each new node has the required source, searches,
   creation record, blueprint origin, chapter, unit and Lean record. Its recorded
   statement occurs verbatim in its module and its dependencies match the proof.
   The three new results are completely proved; their `status: split` identifies
   their origin and does not conceal any hole. Verdict: pass.

Changes by the second reader: restored exact signature whitespace; corrected the
existing proof docstring to describe the implemented argument and its use of shift
normalization for single-unit naturality; narrowed the new cycle-map import; recorded
these checks and the import refinement. No mathematical proof repair was necessary.
Holes closed remain 1; holes added remain 0; no unfinished statement was split off.
