## What changed

Closed the body of `AlgebraicGeometry.Scheme.exists_perfect_lift_plus_finiteLocallyFree`
without changing its signature, visibility, public imports, or definitions.
The proof first derives pseudo-coherence from the existing finite-free local refinement
and applies `exists_boundedAbove_finiteFree_lift`. It then uses one new intermediate
statement, `exists_low_perfect_truncation_triangle`, on that supplied lift.
The main proof constructs the qcqs instances on U, applies the existing perfect Hom-gap
theorem, chooses r = min(N,a), proves quasi-coherence and cohomology vanishing of the
shifted single sheaf, kills the connecting map, and applies Mathlib's distinguished
triangle splitting theorem. Single-functor shift isomorphisms give the requested summand.
The private `qc_single` helper is fully proved from cohomology of single complexes;
it adapts the established argument in AffineDerivedPushforwardTExact to any degree.

Added `Sheaf.AlgebraicGeometry.AffinePerfectTruncationTriangle`, one public theorem with
one hole, recording the low truncation construction from a supplied bounded-above
finite-free representative. It does not assert vanishing of the connecting map or an
isomorphism with a direct sum. Its proof in words describes the finite Tor bound,
module/sheaf transport, image/kernel on U, bounded perfect tail, short exact sequence,
and inverse rotation. Empty U and zero complexes are covered. No data definition is
chosen from this existence theorem: the main proof only eliminates its witnesses locally.

Updated the item's DAG proof route and added the intermediate's node. The unit route
is preserved. No existing statement or definition was changed and no adaptation is needed.
Both sandbox modules compile cleanly through lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_perfect_lift_plus_finiteLocallyFree`
(node `lem-sc-affine-perfect-plus-locally-free`). There are no holes in the item's module.
The private helper `qc_single` is also proved.

Added one hole: `AlgebraicGeometry.Scheme.exists_low_perfect_truncation_triangle`
(node `lem-sc-affine-perfect-low-truncation-triangle`) in the new module
`Sheaf.AlgebraicGeometry.AffinePerfectTruncationTriangle`.
This is a decomposition: one upper hole closed, one lower hole added, net zero new
hole closures. The construction of the low triangle remains; the pseudo-coherent lift,
vanishing, splitting, and shift bookkeeping are assembled in Lean.
The previously existing imported dependency holes are not claimed as proved.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree`
and `Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor` from the item.
They remain proof imports of the new truncation module, whose planned construction needs
them. Their nodes therefore remain needed transitively; no module is pruned from the
item's import closure. All four original proof-dependency nodes remain needed.
No unused proof import is retained in the completed item proof.

## Where the brief, the DAG or earlier work was wrong

The old DAG and module docstrings cite different historical tags. Read the actual
Stacks source at https://stacks.math.columbia.edu/tag/08EG (Lemma 36.13.6).
Retained the DAG's corrected shift convention: with M in degree r-1, the quotient is
M[1-r], and inverse rotation gives M[-r] -> tail|U -> F -> M[1-r].
The final Lean shift isomorphisms explicitly check these degrees.

The existing lift and finite-local-freeness statements do not themselves supply the
truncation triangle. This is the gap isolated by the new intermediate, rather than
replacing the whole desired direct-sum conclusion with a renamed theorem.
The current perfect-to-pseudo-coherent-and-Tor theorem also asks for derived-category
instances on schemes of all smaller opens. The main proof obtains pseudo-coherence
directly from finite-free refinement, using precisely the original statement's instances.
The Tor-amplitude globalization and sheaf/module transport remain in the new construction's
proof obligation. They are not claimed to have been formalized here.

Mathlib searches used LeanFinder, Loogle, and grep; LeanSearch was attempted but returned
Internal Server Error. None gave the affine truncation construction; Mathlib does supply
the final split-triangle theorem. Blueprint search found no duplicate construction node.

## New nodes

`lem-sc-affine-perfect-low-truncation-triangle` records a bounded finite-free representative's
arbitrarily low finite-locally-free truncation triangles, before vanishing or splitting.
It belongs to sec-picard-framework / sk-thm-picard-duality and follows the first part of
Stacks Tag 08EG. Its module is `Sheaf.AlgebraicGeometry.AffinePerfectTruncationTriangle`.
The main theorem supplies the representative via the existing lift theorem, then combines
this strictly partial construction with the existing Hom-gap theorem and Mathlib splitting.
No change record is required because no existing interface changed.

## Second reading by D2

1. **Visible declarations: pass.** Diffed the delivered item against the repository and
checked that its existing theorem signature is byte-for-byte identical. Public imports,
visibility, definitions, and existing docstrings are unchanged. The existing node differs
only in `proof`, `proof_deps`, and `proof_origin`; no change record is needed.
2. **Proof and trust: pass with the reported split hole.** Compiled both modules locally
with `lcompile.py --all`, without errors or warnings. Scratch copies with `#print axioms`
show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the two public
theorems; the private `qc_single` helper uses only the three permitted axioms. Scanned
both files: the only `sorry` is the reported named truncation theorem; no forbidden
declaration or hollow definition occurs. Existential witnesses are eliminated in a proof,
not used to define data.
3. **Split statement: pass.** Read the kernel theorem, finite-free refinement, Tor theorem,
and Stacks Tag 08EG. The new lemma isolates the construction of a triangle, without the
vanishing or direct-sum conclusion, and is a strictly partial argument rather than a
renaming of the item. Its docstring gives the construction and node. For empty U the
construction restricts to zero; for the zero complex the zero tail and zero sheaf work.
For a single finite free complex, sufficiently low tails recover it with zero boundary
sheaf; the bound is deliberately existential. Additional LeanFinder, Loogle, Mathlib grep,
and project searches found no duplicate affine finite-free truncation triangle.
4. **Route and pruning: pass.** Checked the pseudo-coherence reduction, the choices
`r = min N a` and `r-1 < a`, quasi-coherence and vanishing of the shifted single complex,
and Mathlib's zero-third-map splitting followed by the single-functor shift isomorphism.
All retained proof imports support these steps or the split theorem's documented plan.
The two removed direct imports remain transitively needed by the split module, so no
module is pruned. All four old dependency nodes remain transitively needed. The unit
`sk-thm-picard-duality` has empty realized statement/step lists, and its record and route
were not changed or bypassed.
5. **Nodes: pass.** Read both node files and compared the statements, Lean signatures,
proof steps and dependency unions with the implementation and remaining proof obligation.
The new node has the required source, searches, blueprint origin, chapter/unit, split
status, creation and Lean fields. Existing-node metadata follows the new proof.

Second reading changed only this report by adding the review evidence. No Lean or DAG
repair was needed. The delivery remains a decomposition: one upper hole closed, one
strictly lower construction hole added, net zero hole closures.
