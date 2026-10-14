## What changed

The current item is already the repaired bounded-resolution/dimension bridge, rather
than the duplicate single-degree Ext criterion reviewed in upstream #1428. Make
Mathlib reuse explicit in its forward implication: apply
CategoryTheory.hasProjectiveDimensionLT_iff instead of its constructor directly.
The reverse implication already uses Mathlib's zero-bound projectivity criterion
and short-exact dimension shifting, followed by the existing bounded-resolution
splicing construction. Update the node's proof and proof_origin accordingly.
All signatures, definitions, visibility, imports, and callers remain unchanged.

## Proved and sorry left

ModuleCat.projective_resolution_ext_degree is proved with zero sorries.
The baseline already proved it: holes closed in this session: zero; holes added:
zero; split off: zero. This is repair validation and explicit reuse of Mathlib,
not net proof progress. No other module is delivered.

## No longer needed

No newly removed imports or nodes. All four imports are used: GlobalDimension
supplies the explicit bounded-resolution predicate, Dimension the statement's
Mathlib predicate and criteria, Ext the cocycle representation, and SuccSplice
the construction of an actual bounded resolution. The older direct long-exact
Ext proof and projective Ext criterion are already absent from this node's
proof dependencies: lem-weil-pbc-ext-long-exact-first-variable and
lem-weil-pbc-projective-ext-criterion are not needed by this proof. Neither
whole module is claimed globally pruned; other callers may still need it.

## Where the brief, the DAG or earlier work was wrong

The original dispatch assumption that the item contains sorry is stale. The
repair itself has also already landed: the historical node statement_change
records the replacement of the reviewed Ext criterion with the current bridge.
Mathlib hasProjectiveDimensionLT_iff says that its dimension predicate is
Ext vanishing. It does not construct a ProjectiveResolution with zero terms
above the bound, whereas HasProjectiveResolutionLE requires precisely that.
Thus replacing this bridge directly with that Mathlib lemma would not typecheck;
retaining the bounded-resolution construction and deriving the dimension part
from Mathlib addresses the review without duplicating its Ext criterion.

Repeated Loogle and LeanFinder searches confirmed the dimension APIs; local
Mathlib source inspection confirmed that they are Ext-defined. No exact
bounded-resolution equivalence was found. The zero-bound case uses self,
and the successor case uses the projective kernel sequence and splicing.
No unit-realizing node or step is bypassed. No target statement changes.
The previous worker's tool refusal must be retested: the current deliver3.py
explicitly recognizes listed repairs even when their baseline has no sorry.

## Second reading by Y3

1. Compared the complete delivered Lean module with the repository using diff.
   The only changed line is the forward proof's application of
   `hasProjectiveDimensionLT_iff`; the existing theorem signature, definitions,
   visibility and imports are byte-for-byte unchanged. No change record is needed.
   Verdict: pass.
2. Compiled the delivered file locally through lcompile.py with no errors or
   warnings. A scratch copy with `#print axioms
   ModuleCat.projective_resolution_ext_degree` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered module
   contains no sorry, axiom, unsafe, opaque, implemented_by, or extern declaration,
   and defines no data. The existing splicing theorem constructs the augmented
   complex and its resolution structure explicitly, without postponed data.
   Verdict: pass.
3. There are no split-off statements or new declarations. Checked the zero bound:
   Mathlib's zero-bound criterion gives a projective object and its identity
   resolution, with every positive term zero. In the successor case dimension
   shifting lowers the kernel's bound by one, and the existing splicing theorem
   raises its explicit resolution bound by one. The zero module and bounds
   larger than necessary cause no exceptional case. A fresh Loogle search for
   `CategoryTheory.ProjectiveResolution`, a grep search for finite supported
   resolutions, and local searches of the dimension APIs and HasProjectiveResolutionLE
   callers found no shorter independent bounded-resolution equivalence to use.
   Verdict: pass.
4. The forward proof kills cocycles using the zero source terms; the reverse
   proof uses Mathlib projectivity and dimension shifting before the existing
   bounded-resolution splice. Both public imports supply names in the theorem's
   statement. Both plain imports supply proof APIs (extMk and the splice), so
   no proof-only import is public. The report's No longer needed list is complete
   relative to the old proof_deps: none of its three nodes is newly unused.
   Inspected dag/units/sk-thm-p1.json: this item is below the unit level and no
   realized statement or step is bypassed or changed. Verdict: pass.
5. Compared the node JSON with its repository version. Only proof and
   proof_origin change, to name the actual Mathlib criterion application.
   The proof_deps union still correctly records the bounded-resolution
   definition, Ext definition, and successor splicing theorem. The node's
   statement and Lean record agree with the unchanged theorem signature.
   No new nodes require validation. Verdict: pass.

Second reading changed only this report; the Lean proof and node edits passed
without repair. No holes closed or added, and no split-off statements.
