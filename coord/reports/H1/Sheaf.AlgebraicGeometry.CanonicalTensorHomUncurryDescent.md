## What changed

The main theorem combines representative normalization with extension to an
isomorphism-compatible family. Its existing signature and docstring are byte-for-byte
unchanged. Both new modules are plain proof-only imports. Their public import of the
differential module is needed by their statements. No existing definition changed.

The sandbox copy of CanonicalTensorHomUncurryDifferential is byte-for-byte identical
to the repository version, supplying local compilation support only.

## Proved and sorry left

Closed the syntactic hole in AlgebraicGeometry.exists_tensorHomUncurry_descent
(node lem-pc-tensor-hom-uncurry-descent) by equality transitivity between normalized
values and the extension's agreement equation. This is a decomposition, not a
completed mathematical proof: one upper hole closed and two lower holes added.

Added named holes:
- AlgebraicGeometry.exists_tensorHomUncurry_descent_representative, node
  lem-pc-tensor-hom-uncurry-descent-representative: construct normalized values.
- AlgebraicGeometry.exists_tensorHomUncurry_descent_extension, node
  lem-pc-tensor-hom-uncurry-descent-extension: extend normalized values to a new
  isomorphism-compatible family, preserving the specified chain inputs.

Net minus one across these modules. Neither intermediate statement is claimed proved.
The existing lower hole AlgebraicGeometry.schemeTensorHomUncurryGraded_comm
(node lem-pc-tensor-hom-uncurry-differential) remains unchanged. The first worker's
false AlgebraicGeometry.tensorHomUncurry_descent_isomorphism_transport is deleted
and adds no delivered hole. No definition chooses data from these existence theorems.

## No longer needed

No source imports or globally needed modules are pruned. The parent node's old direct
proof dependencies lem-pc-tensor-hom-uncurry-differential, lem-pc-kflat-resolution,
lem-pur-hom-kflat-into-kinjective, lem-weil-pbc-kinjective-hom-derived, and
lem-pur-hom-complex-global-cochains are replaced by the representative and extension
nodes. All five remain in those nodes' proof plans: relocation, not pruning. The original
public differential import stays because the statement uses its chain-map construction.

## Where the brief, the DAG or earlier work was wrong

The first worker asserted transport for arbitrary t, with no normalization or naturality
hypothesis. This is false in general: on vector spaces, independently chosen nonzero
constant outputs can fail transport under multiplication by minus one. Normalization
alone still leaves arbitrary values on derived objects not literally complex images
unconstrained. The repair constructs a NEW family s and preserves only normalized
inputs; it does not assert that arbitrary t was already compatible.

The first transport hole had neither a docstring nor a node. The report omitted these
faults and the parent node's proof route was not updated. The new representative node
had an unrelated E3 created.item and incomplete Lean record. These faults are repaired.
Its terse docstring has been expanded into a complete representative-construction proof.

## New nodes

lem-pc-tensor-hom-uncurry-descent-representative separates normalized-value construction
from transport on arbitrary derived objects. Its statement is the first worker's
normalization statement; its source, proof, creator, searches and Lean record are completed.

lem-pc-tensor-hom-uncurry-descent-extension separates change of representatives, assuming
already normalized values. Its proof explains K-flat/K-injective choices, comparison of
roofs, evaluation on summands, cancellation of quasi-isomorphisms and agreement on the
specified inputs. It does not construct normalized values from nothing. No change record
is required; no existing interface changed.

## Second reading by H1

1. Compared all existing modules by diff. PASS: the item's existing signature and
   docstring are byte-for-byte identical. Only its proof and two plain imports change.
   The differential compilation-support source is identical.
2. Compiled all modules in import order, inspected every sorry and scanned forbidden
   constructs. PASS: no sorry in the main proof; two documented new theorem holes;
   the unchanged differential hole. No hollow definitions or forbidden declarations.
   Explicit axiom checks and the delivery probe are recorded below.
3. Checked both intermediate statements and their proofs in words against zero complexes,
   zero inputs, identity isomorphisms, arbitrary non-K-flat L, and derived objects not
   literally complex images. PASS after repair: the new family may replace arbitrary
   values of t. New LeanFinder, Loogle and Mathlib grep searches find only partial
   localization/Tor infrastructure. LeanSearch failed with Internal Server Error,
   honestly recorded. Searched lean/ with evaluation, uncurrying and normalization
   wording. Read the existing K-flat resolution, HomTensorTotal, global-cochain and
   K-injective Hom statements. The downstream existence theorem imports this item;
   the existing descent naturality theorem assumes transport, so neither is a shortcut.
4. Checked the route, imports and pruning. PASS as a decomposition. No unused source
   import is added; every old proof dependency is accounted for above. The unit
   sk-thm-picard-duality has empty realized entries; this item realizes no unit statement
   or step. Its chapter/unit and the unit route are unchanged.
5. Compared the parent proof with its updated node and both new Lean signatures with
   their nodes. PASS: the parent uses precisely representative plus extension; the new
   nodes have sources, complete proof plans, searches, matching verbatim Lean records
   and created fields naming H1 and this item. Their proof_deps are the unions of uses.

Changed the false transport assertion into a documented extension theorem in its own
module, repaired the main proof, expanded the representative proof docstring, completed
both new nodes, updated the parent proof route and corrected the report. No lower proof
was short enough to close during this reading.

Explicit #print axioms checks for the main theorem and both intermediate theorems
showed only propext, Classical.choice, Quot.sound and sorryAx. The latter is expected
from the two open intermediate statements and existing lower statements. Scratch
copies were removed before delivery. The main signature/docstring equality and all
100-character line limits were also checked mechanically.
