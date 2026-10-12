## What changed

Proved the body of `AlgebraicGeometry.Scheme.exists_perfect_supported_stabilized_lift`
from two strictly smaller intermediate statements, without changing any existing signature,
visibility, definition, or target. This is a decomposition, not a sorry-free proof of the
transitive dependencies.

The main module defines a local proposition P(W) in its proof: an ambient derived object
and map, perfect and supported at points of W, with the required stabilization equation
on U. The initial ambient representative gives P(U). A single affine attachment gives the
source-plus-shift identification; the main module composes it with `biprod.mapIso` and
`(hS n).symm`, and proves the map equation using `ha n`, inverse cancellation, and
`biprod.map_fst_assoc`. It chooses a finite affine subcover using Mathlib, performs a
Finset induction maintaining compactness and P, proves the final union is top, and extracts
global perfectness and support directly from their pointwise definitions.

Added `Sheaf.AlgebraicGeometry.SupportedMapInitialAmbientLift` and
`Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment`, each containing one public theorem
with its complete sourced construction in the docstring. The initial lemma is the
extension-by-zero base case, and does not assert global perfectness. The attachment lemma
asserts only one geometric attachment and the first-projection equation; it contains no
stabilization sequence, finite cover, global compactness hypothesis, or final target.
Updated the parent node's proof, proof_deps, and proof_origin to match the actual Lean proof.

Validation: all three sandbox modules compile through `lcompile.py --all`, with unchanged
existing theorem type and no warnings. The main proof uses a local heartbeat budget for
elaboration of derived restriction and the biproduct equation, with an explanatory comment.
The delivery dry run printed OK: compilation and preflight pass, except for the second
reading that the next worker supplies. Nothing was pushed. No definition or data
construction uses sorry.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_perfect_supported_stabilized_lift`
(node `lem-sc-perfect-supported-stabilized-lift`), by a complete finite-cover induction
and categorical equation calculation.

Added two holes, each exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.exists_supported_map_initial_ambient_lift`
  (`lem-sc-supported-map-initial-ambient-lift`): ambient extension-by-zero representative,
  local perfectness/support on the original open, and the adjunction map equation.
- `AlgebraicGeometry.Scheme.exists_supported_map_affine_attachment`
  (`lem-sc-supported-map-affine-attachment`): one affine attachment, local properties on
  the enlarged open, and the source-plus-shift first-projection equation.

There is no sorry left in the assigned module. Holes closed: 1; holes added: 2.
This is a decomposition; it is not claimed as a positive net sorry reduction. Existing holes
in the affine inputs and derived gluing remain outside the files delivered here.

## No longer needed

Removed the direct imports of `Sheaf.AlgebraicGeometry.AffinePerfectMapLift`,
`Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension`, and
`Sheaf.AlgebraicGeometry.DerivedOpenGluing` from the assigned module, replacing them with
the two intermediate modules. Their nodes remain needed by the affine attachment and their
modules remain in its proof-dependency imports. No existing node or module is pruned from
the transitive proof route. The unit record has no realized statement or steps to bypass.

The initial lemma uses the existing extension-by-zero adjunction, unit-restriction
isomorphism, and stalk comparison modules, rather than introducing a second definition
of extension by zero. The attachment imports the existing derived-localization and
quasi-coherent open-restriction modules for the needed local categories and target.

## Where the brief, the DAG or earlier work was wrong

The original three dependencies do not supply the iteration interface: there is no stated
single-attachment theorem with the local perfectness/support and restriction equation
needed to maintain a finite-cover invariant. The proof now exposes this interface and its
initial case as separate items, and performs the finite iteration in the assigned module.
There is no statement correction and no forced adaptation.

The repository does not contain the cited `literature/stacks-project/perfect.tex` or
`cohomology.tex` on this machine. Read the actual public Stacks statements and proofs at
https://stacks.math.columbia.edu/tag/09IM and https://stacks.math.columbia.edu/tag/08BT;
the new nodes cite these sources directly. WANTED: a local copy of Stacks perfect.tex
(Tag 09IM) and cohomology.tex (Tag 08BT), for the two new nodes and their next proof
workers. The existing blueprint-ancestor tool reports
None for this already-created item's ancestor; its own blueprint.from and the existing
affine input nodes consistently identify `lem-sc-finite-duality`. Kept that recorded
ancestor, with the full via chain, for both new nodes.

Searched the source library and Mathlib for a shorter route. LeanFinder returned derived
fractions/cochain-complex facts, with no supported perfect extension theorem. LeanSearch
returned Internal Server Error, recorded as unavailable. Loogle located the restriction
functor and over-equivalence comparisons and the finite-subcover infrastructure. The
Mathlib grep found over-equivalence infrastructure, not the two new statements. All
remote searches were run with msearch.py and recorded in searches.jsonl. Blueprint
searches for stabilized, supported, affine attachment, ambient representative, and
extension by zero found no matching geometric intermediate statement.

Edge cases checked against the constructions: empty U uses the zero extension; empty or
redundant affine V does not invalidate the attachment; an empty finite cover has base
union U, and the covering equation then forces U = top; empty X makes local perfectness
and support vacuous; zero source and empty support use exactly the same extension and
first-projection equations. The local invariant deliberately imposes no perfectness
outside the current open, because extension by zero generally is not globally perfect.
Neither intermediate asserts a retraction or a direct-summand conclusion.

## New nodes

`lem-sc-supported-map-initial-ambient-lift` is the extension-by-zero initialization,
strictly weaker than the target: it yields local perfectness/support only on the specified
open. Its proof constructs the ambient representative from the actual extension-by-zero
functor and the inverse module equivalence, and uses the derived adjunction and its unit.
The theorem is in `lean/Sheaf/AlgebraicGeometry/SupportedMapInitialAmbientLift.lean`.

`lem-sc-supported-map-affine-attachment` is the one-affine-open step of Stacks 09IM,
applied on W union V, followed by the initial ambient representative. It uses the existing
affine extension, affine map lifting, and derived open gluing statements. Its output is a
source-plus-shift isomorphism and projection equation; it leaves the index transition and
finite-cover induction to the main proof. The theorem is in
`lean/Sheaf/AlgebraicGeometry/SupportedMapAffineAttachment.lean`.

No change record is needed: existing interfaces and statements are unchanged.

## Second reading by S4

1. **Module comparison.** Compared the assigned module with the repository version. The
   existing theorem signature, visibility, and definitions are byte-for-byte unchanged;
   only its proof and proof-only imports changed. The two added modules are new files and
   do not alter an existing declaration.

2. **Compilation and proof checks.** Compiled all three sandbox modules with
   `lcompile.py --all`; compilation succeeds without warnings. The assigned theorem has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining
   `sorry`s are the two explicitly named split-off theorems, each exactly `:= by sorry`,
   with a source, proof docstring, and matching DAG node.

3. **Statements and new nodes.** Read both split-off statements against their Lean types
   and edge cases (empty opens, zero source, and redundant affine attachment). Each is a
   true, strictly smaller interface needed by the finite-cover proof: the initial theorem
   asserts properties only on U, and the attachment theorem asserts properties only on
   W union V plus the restriction equation. Neither restates the target or adds a hollow
   definition. Searched the repository and Mathlib for an existing declaration; none was
   found.

4. **Pruning and route.** The main proof follows the unit route: initial case, one affine
   attachment, finite affine subcover induction, and extraction at top. Its imports are
   reduced to the two intermediate modules and `PerfectComplex`; the removed direct imports
   are still used transitively by the attachment theorem. No proof-dependency node became
   unused and no unit step was bypassed.

5. **DAG agreement.** Updated the parent node's proof, proof dependencies, and proof origin
   to match the Lean proof. The two new node records match their theorem statements,
   declarations, sources, proof steps, and `split` status. No target statement or existing
   interface changed.

The second reading made only this report addition; no Lean source repair was necessary.
