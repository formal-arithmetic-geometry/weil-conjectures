## What changed

The statement and visibility of `CategoryTheory.truncation_canonical_abutment` are unchanged.
Its proof now constructs the iterated D inclusions recursively, proves equality of the limiting
subobjects with the sharp stationary cycles and boundaries using their GLB/LUB properties, and
constructs the infinite-page/finite-page isomorphism from the cycle-tower projection's kernel.
It then combines the canonical cocone, the proved filtration transport, and finite-page comparison.

New modules:

- `Sheaf.CategoryTheory.TruncationAbutmentCocone`: the explicit derived-cohomology maps, their
  invertible degree-zero component, and the diagonal cocone/incoming-alpha normalization.
- `Sheaf.CategoryTheory.AbutmentImageFiltration`: proved. It factors the prescribed cocone through
  the normalized diagonal colimit, constructs its transport to H and D(0,n), and proves all image
  formulas, support bounds, finiteness, exhaustiveness, separatedness, inverse-limit completeness,
  negative graded/infinite-page vanishing, and convergence. Its explicit cokernel.mapIso on
  consecutive image subobjects transports the canonical graded map and hence weak convergence.
- `Sheaf.CategoryTheory.AbutmentFinitePageComparison`: only the positive-bidegree comparison
  maps and their commuting equations, for an abstract half-plane exact couple and given filtrations.

All four modules compile together without warnings through lcompile.py. No definition contains
sorry; all new data definitions are private constructions with complete proofs. The existing
unit statement and realized steps are preserved. No existing interface, target, or other module
was adapted. DAG proof fields now record the actual reduction.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.truncation_canonical_abutment` (lem-sp-truncation-canonical-abutment).
There is no sorry in its module.

Also proved the new theorem `CategoryTheory.abutment_image_filtration`
(lem-sp-abutment-image-filtration), including all its private helpers. This proof uses the existing
named half-plane diagonal-colimit, weak-convergence and sharp-bound declarations; existing
sorries in those dependencies are not claimed closed.

Added two whole-theorem holes, each in its own new module with source, proof in words and node:

- `CategoryTheory.truncation_abutment_cocone` (lem-sp-truncation-abutment-cocone).
- `CategoryTheory.abutment_finite_page_comparison` (lem-sp-abutment-finite-page-comparison).

This is a decomposition, not a sorry-free proof of the original theorem: one original hole is
closed and two strictly smaller holes are added, for net -1 before any independent downstream
work. The first hole involves no E, f, g, filtration, limiting subobject or convergence conclusion.
The second is generic in an abelian category, involves no derived category or truncation functor,
and assumes the previously constructed inclusions and filtrations. It contains only the positive
finite-page maps. The stationary-subobject and sharp-page quotient arguments, and all filtration
and colimit transport, are actual Lean proofs rather than new holes.

Edge cases checked mathematically and in the typed interfaces: at p=0 the incoming iterate
normalizes to c; at p<0 both adjacent filtration steps are top and the graded cokernel is zero;
when q<a both finite-page quotients vanish; when n<a the top and bottom bounds overlap only on
an abutment forced to be zero by the invertible c and the D bound. The finite comparison bound
R=max(p+3,q-a+2) is at least 3 for p>=0, so all natural-index subtractions are valid. The cocone
lemma needs no chosen lower bound and its statement does not assume one.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.CategoryTheory.ExactCouple` and `Sheaf.CategoryTheory.Filtration`: redundant; their
  definitions remain available through the unchanged public ExactCoupleConvergence import.
- `Sheaf.CategoryTheory.DerivedCoupleExact`: belongs to the remaining finite-page comparison
  node, whose new module imports it.
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso` and
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`: belong to
  the remaining canonical-cocone node, whose new module imports them.

The complete list of old direct proof dependencies absent from the new original-node
`proof_deps` is `def-sp-truncation-couple`, `def-sp-filtration`,
`def-sp-image-filtration`, `lem-sp-derived-couple-exact`,
`lem-weil-pbc-derived-functor-truncation-iso`, and
`lem-weil-pbc-derived-direct-image-triangulated`. The first three remain statement
dependencies and are used in the helper interfaces; the last three remain proof
dependencies of the two open helpers. None is globally dispensable.

No whole module is pruned from the targets' import closure. The original node's direct proof
edges to the derived-couple and derived-truncation lemmas are replaced by the two smaller nodes;
these underlying lemmas remain needed there. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The supplied plan is mathematically consistent, but its existing declarations do not directly
state the additional prescribed cocone and finite-page map equations. HalfPlaneConvergence and
HalfPlaneGradedCanonical provide abstract convergence and canonical infinite-page comparison,
not the specified lambda/lift/psi equations. These interface gaps are now isolated explicitly.

The ancestor helper returned None for the supplied node. Its existing blueprint.from record
explicitly identifies thm-sp-truncation-e2; the new nodes preserve that reference and prepend the
original node to via.

WANTED: the local source text at
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/thm-sp-truncation-e2.md`,
steps 5--7, and `literature/stacks-project/homology.tex` / the derived-categories source containing
Tag 05TC. They are absent on this machine. The proofs in words refine the supplied complete
node/docstring plan; proof_origin is agent, not a claim of having inspected unavailable literature.
LeanSearch returned Internal Server Error for all three concept searches; this is recorded as
unavailable. LeanFinder, logged Mathlib grep searches, both library roots and related DAG nodes
were checked; none supplies the two remaining full interfaces.

## New nodes

`lem-sp-truncation-abutment-cocone` records the canonical derived-cohomology diagonal cocone;
module `Sheaf.CategoryTheory.TruncationAbutmentCocone`, left with one named theorem sorry.

`lem-sp-abutment-image-filtration` records the fully proved abstract transport of the finite image
filtration and convergence to an invertible normalized cocone;
module `Sheaf.CategoryTheory.AbutmentImageFiltration`, no sorry.

`lem-sp-abutment-finite-page-comparison` records the positive finite-page quotient comparison
with all prescribed maps and equations; module `Sheaf.CategoryTheory.AbutmentFinitePageComparison`,
left with one named theorem sorry. No change record is needed: all existing signatures and
public imports stay unchanged.


## Second reading by C1

1. **Interfaces: PASS.** Compared the delivered original module with the repository
   using `diff -u`, then compared the complete theorem signature as raw text: it is
   byte for byte identical, including all hypotheses, existential witnesses and map
   equations. Its docstring, visibility and public imports are unchanged. The other
   three modules are new; no existing declaration or definition is adapted. The
   original node differs only in `proof`, `proof_deps` and `proof_origin`.

2. **Proof and data: PASS as a decomposition.** Independently compiled all four
   modules in import order through `lcompile.py`, without errors or warnings.
   Scratch copies with `#print axioms` checked every delivered definition and theorem,
   including private helpers: only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` occur. Exactly the two reported public whole-theorem sorries remain;
   neither a definition nor a private theorem contains a sorry. No forbidden axiom,
   unsafe/opaque declaration or implementation override occurs. The limiting
   subobjects are determined by their GLB/LUB properties; the diagonal colimit is
   determined up to its unique cocone-compatible isomorphism. The cocone theorem
   prescribes H, j and c explicitly, and the filtration steps are determined by
   their incoming images and top bounds. The chosen factor map in the proved
   filtration theorem comes from a unique universal property. There is no new
   arbitrary witness of mere existence used to define data.

3. **Split statements: PASS.** Read both open interfaces and their docstring and
   node proofs. The cocone statement is independent of E, f, g, L and convergence;
   the finite-page statement assumes the already supplied inclusions and
   filtrations and has no derived-category data. Neither merely renames the item.
   Checked p=0, p<0, q<a and n<a. In particular R=max(p+3,q-a+2) is at least 3,
   u=p-R+2 is at most -1, and the iterated source of the outgoing derived D term
   has second index q-R+1<a. Exactness makes g the required quotient, while the
   negative-E bounds make lambda invertible. The stable projection equation has
   the correct orientation. Independent searches used new LeanFinder queries on
   derived truncation cocones and derived-g image quotients, Loogle on cokernels,
   and rg on both library roots and Mathlib's abelian-category files. Found
   truncation and cokernel building blocks, but no full remaining interface.
   `HalfPlaneGradedCanonical`, `pageCouple_image`, the transition-inclusion
   identity, and the right-derived truncation isomorphism were read; applying them
   still requires the reductions named in the two holes. Neither hole could be
   closed by a short direct application. The unavailable local literature and
   agent proof origin are already recorded honestly above.

4. **Route and pruning: PASS.** The original module proves the recursive inclusions,
   GLB/LUB stabilization and sharp finite-page quotient comparison before assembling
   the cocone, proved filtration transport and positive finite-page maps. The
   transport proof uses existing normalized colimits, weak convergence and sharp
   bounds, and Mathlib's image and cokernel isomorphisms. Public imports support
   signatures; proof-only imports are plain imports. Imports in the open modules
   retain their declared proof plans. Checked `dag/units/sk-thm-properbasechange.json`
   and its `realized` fields: no unit statement or step is replaced or bypassed.
   The complete removed direct-edge list is now explicit above; no whole module is
   claimed pruned. One old hole closed and two new holes added remains net -1,
   a decomposition rather than a sorry-free proof.

5. **DAG: PASS.** Each new node has its source, full interface, proof in words,
   searches, split status, creator, blueprint provenance, unit/chapter and Lean
   record. Each `proof_deps` equals the union of its proof steps' `uses`.
   Original-node proof steps track the actual recursive, stationary-subobject,
   quotient, cocone, filtration and finite-page reduction. New-node signatures
   agree with the Lean statements, and proof origin is agent throughout.

Second-reading changes: completed the exact list of removed original proof edges
in `## No longer needed`, recorded the independent checks and verdict here, and
left the correct Lean proofs, statements and DAG records unchanged. No additional
hole was closed or added in this reading.
