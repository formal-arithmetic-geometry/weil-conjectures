## What changed

Replaced the earlier all-degrees renaming with a reduction to the exact
Mayer--Vietoris comparison diagram, stated in the new module
`Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyMayerVietoris`.
The original signature and docstring are preserved. Its proof takes the product
of the two local comparisons and applies Mathlib's left-exact diagram lemma in
degree zero and its five lemma in each successor degree. Both new imports in the
original module are proof-only imports.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.H.baseChange_bijective_of_openCover` has a complete
proof from the diagram theorem and Mathlib's diagram lemmas. Both sandbox modules
compile successfully with `lcompile.py --all` (exit code 0, no warnings). The local
axiom probes in `deliver3.py --no-push` also pass. The server compile now passes,
and the required dry run prints OK except for the second reading, which the
second reader writes. Nothing was pushed.

The sole sorry in the delivery is
`AlgebraicGeometry.Scheme.Modules.H.baseChange_mayerVietoris`, in the new module,
node `lem-pc-flat-cohomology-mayer-vietoris`. It constructs exact rows and commuting
squares; it assumes no local bijectivity and concludes no global bijectivity.
Its docstring gives the construction, including the boundary compatibility via
exact inverse image and Yoneda composition, and scalar extension on pure tensors.

## No longer needed

Removed the direct proof-only import `Sheaf.Topology.ModuleMayerVietoris` from
the gluing module and relocated it to the new diagram module, where its theorem
is needed. The old direct proof dependencies
`def-pc-flat-cohomology-comparison`, `lem-sc-mayer-vietoris-ringed-space`, and
`lem-weil-pbc-flat-tensor-exact` move below the new diagram node; none is pruned
from the target closure. The five-lemma dependency remains direct.
The invalid earlier sandbox-only `lem-pc-flat-cohomology-gluing-all` and its
all-degrees restatement have been removed; they were never repository dependencies.
No affineness, compactness or separatedness lemmas are used.

## Where the brief, the DAG or earlier work was wrong

The previous attempt merely moved the same all-degrees statement to another name;
it was not a reduction. Its new node also had a placeholder Lean signature and
lacked a matching declaration docstring. It has been replaced completely.

The existing ringed-space Mayer--Vietoris theorem gives exactness and naturality
for module maps and open restrictions, but its signature does not state the
flat base-change squares for the particular `H.baseChange` map. The new node
isolates precisely that construction. Stacks 02KH refers to Mayer--Vietoris;
01EB supplies the sequence. Their specialization and Ext compatibility are
expanded here as an agent-written proof rather than attributed verbatim to Stacks.

Edge cases checked mathematically: U or V empty, U=V=X, the empty scheme, M=0,
and S the zero ring all admit the displayed exact rows. Degree zero has an initial
injection, rather than a nonexistent negative-degree boundary. For positive degree
the left outside term is the product in the preceding degree, so the five lemma
uses the local hypotheses in both adjacent degrees. There is no affine-intersection
assumption. The unit record has no realized statement or step assigned to this
node; the existing Mayer--Vietoris route is retained.

The earlier missing local dependency is now available, and the local compilation
of both modules succeeds. On this retry, local compilation and the delivery tool's local axiom probes passed
again. The original theorem signature and docstring were checked against the
repository; the diagram lemma has no bijectivity hypothesis or conclusion, and
the degree-zero and successor-degree applications match Mathlib's signatures.
The import-direction check permits the new proof-only dependency.
The first server dry run of this retry reproduced the missing existing
`FlatCohomologyComparison.olean` object file. The next dry run passed after
build availability recovered, without copying dependencies or changing tools.

## New nodes

`lem-pc-flat-cohomology-mayer-vietoris` states the exact commuting comparison
ladder independently of all local bijectivity hypotheses, in its own new module.
It is strictly the diagram-construction part of the argument: the original module
supplies the product bijectivity and the zero/successor diagram chases. Searches
were run using LeanSearch (unavailable: HTTP internal server error), LeanFinder
(generic Mayer--Vietoris short-complex infrastructure), and Mathlib grep (generic
site Mayer--Vietoris sequences); the existing localized-cohomology diagram concerns
localization by a line-bundle section, not this flat algebra comparison.
No definitions, existing statements, targets or public imports are changed,
and no change record is required.


## Second reading by Y2

1. Compared both delivered modules with the repository. Only the body and
proof-only imports of the existing gluing theorem change; its full signature and
existing docstring are byte-for-byte identical. No definition or target changes,
so no change record is required. The second module is new.
2. Compiled both modules locally without errors or warnings. Explicit scratch
`#print axioms` probes for `H.baseChange_bijective_of_openCover` and
`H.baseChange_mayerVietoris` returned only propext, Classical.choice, Quot.sound,
and sorryAx. The latter is expected: precisely the named diagram theorem remains
sorry. There are no definitions in this delivery, no forbidden declarations, and
no other sorry.
3. Read the diagram signature, its docstring and node against Stacks Tags 02KH
and 01EB, and the definitions of HOver, H.baseChangeLinear and H.baseChange.
The diagram has the exact tensor/product terms and comparisons required, assumes
flatness and a two-open cover, and assumes no bijectivity. It is a construction
lemma, not the original bijectivity implication under a new name. For U empty
(or V empty), the rows reduce to the identity sequence on the other open; for
U=V=X they have diagonal and difference maps; for X empty, M=0 or S the zero
ring all terms vanish. No separatedness, compactness, or affine intersection is
needed. The docstring explains boundary compatibility using the exact inverse
image of the free-abelian-sheaf sequence and Yoneda composition. Independently
searched with LeanFinder for pullback naturality of connecting maps, Loogle for
the left-exact diagram lemma, Mathlib grep for map/connecting compatibility,
and rg across both library roots. The existing boundary_connecting_naturality
is a degree-zero coefficient-sequence statement on one scheme; the etale
Mayer--Vietoris pullback results use different sites. Neither supplies this
diagram. Its construction cannot be closed in a few minutes from these APIs.
4. Checked every argument of the zero and successor diagram chases against
Mathlib.Algebra.FiveLemma. In degree n+1 the outside terms are product H^n,
intersection H^n, product H^(n+1), intersection H^(n+1); their surjectivity,
bijectivity, bijectivity and injectivity are exactly the supplied hypotheses.
The degree-zero proof correctly uses the initial injections. No shorter complete
route was found. Public imports provide signature types or instances; both new
imports of the existing module are proof-only. The unit sk-thm-picard-rr has
empty realized arrays; its route is unchanged. The No longer needed section
now lists all three old direct dependencies transferred below the diagram node.
5. Checked the two nodes against Lean: the existing node records product
bijectivity followed by the two Mathlib diagram chases; the new node records
scalar-extended exactness, the pulled-back cover, and comparison naturality.
Its declaration record matches the Lean signature, its proof dependencies are
the union of its step citations, and its source, creation, blueprint, chapter,
unit and search records are present. The diagram statement is strictly the
construction part, leaving the actual implication to the existing module.

Changed: added the missing proof-only import Sheaf.Topology.ModuleMayerVietoris
to the diagram module, so its declared Mayer--Vietoris dependency remains in the
import closure as reported. Clarified direct dependency relocation in No longer
needed. No Lean statement or proof body was changed by the second reading.
