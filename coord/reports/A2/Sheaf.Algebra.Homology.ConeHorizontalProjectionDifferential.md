## What changed

Added a complete filtration and kernel-subobject argument for the target theorem. The two explicit source/target generator sign calculations are isolated in `coneHorizontal_projection_generator_vanishing`; the target theorem is proved from that strictly lower statement, the explicit tail description, and the differential commutation law.

## Proved and sorry left

Closed the original hole in
`HomologicalComplex₂.coneHorizontal_projection_differential`
(node `lem-sp-cone-horizontal-projection-differential`) by a complete
kernel-subobject reduction.

Added one named hole in
`HomologicalComplex₂.coneHorizontal_projection_generator_vanishing`
(node `lem-sp-cone-horizontal-projection-generator-vanishing`). It states the
source and target generator sign identities, without a filtration or a quotient.
There are no other holes added or left in the delivered modules. This is a
one-for-one decomposition, with zero net holes removed, not an axiom-free proof
of the differential theorem. Both declarations' axiom lists contain exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed

None: all three original proof dependencies remain used:
`def-sp-cone-horizontal-projection`, `lem-sp-cone-horizontal-step-stable`
(the explicit summand/image/tail definitions), and
`def-sp-filtered-complex-subquotients`. No imported module is pruned.
The new generator module is a plain proof-only import. Each original public
import supplies a name used by the unchanged theorem signature. The generator
module's two public imports supply names used by its own signature.

The unchanged sandbox copies of `ConeHorizontalProjection`,
`ConeHorizontalStepStable`, and `FilteredComplexSubquotients` supply local
compilation dependencies; no change to these modules is delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked by a missing shared olean for `ConeHorizontalProjection`. Compiling the dependency modules in the sandbox resolves that infrastructure issue. The mathematical generator calculation remains the single split-off lower item.

## New nodes

`lem-sp-cone-horizontal-projection-generator-vanishing` — `Sheaf.Algebra.Homology.ConeHorizontalProjectionGenerator`.

## Earlier second reading (a previous round; superseded)

The complete kernel-subobject assembly was checked by a second reading. The remaining generator sign calculation is a strictly lower statement and is the only sorry retained.

## Second reading by A2

1. **Interfaces:** diffed every sandbox module against the repository.
   The differential theorem's complete signature and original docstring are
   byte-for-byte unchanged; the only original-module edits are the proof,
   a proof comment, and the plain generator import. All three copied dependency
   modules are byte-for-byte identical to the repository. No definition, target,
   visibility, hypothesis, or conclusion changed; no change record is needed.

2. **Proof and compilation:** compiled all five sandbox modules in import order
   through `lcompile.py`, without errors or warnings. Read the reduction:
   `hs` and `ht` put each image in `kernelSubobject g`, `Finset.sup_le` puts
   the tail there, `hF` gives factorization of the filtration inclusion, and
   kernel vanishing plus `arrow.comm_assoc` proves the exact stated equation.
   A scratch copy with `#print axioms` for both declarations gave exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the scratch copy
   was removed. The only `sorry` in the set is the named generator theorem.
   There is no forbidden declaration or hollow definition.

3. **Remaining statement:** checked the generator theorem against the explicit
   definitions and Mathlib's `ι_D₁`, `ι_D₂`, `d₁_eq'`, `d₂_eq'`,
   `ιTotalOrZero_map`, `homotopyCofiber.inlX_d`, and `shiftFunctor_obj_d'`.
   Read Stacks Tag 012X, first-filtration formula and Lemma 12.25.1(1).
   The cone refinement is an agent's calculation, rather than a theorem
   directly stated there. For `h>p` every output column is greater than `p`;
   for `h=p` the source blocks agree as `-e^2*d_A` and `e^2*f=f`, and the
   target blocks agree as `e*d_B`, with `e=(-1)^p`. In particular `p=0`
   gives no sign change and `p=1` needs the minus sign on the source projection.
   Checked zero bicomplexes, `n<p-1`, `n=p-1` (only source survives), and
   `h>n.toNat`/`h>(n+1).toNat` (the generator is zero). These include the
   `p=0,n=-1` boundary. The statement is true and is precisely the component
   calculation used by the reduction. It does not repeat the filtration
   theorem: it has no `F` or `hF`, and leaves the kernel/finite-supremum
   assembly to the proved theorem. It remains a decomposition, not net progress.
   Searched Mathlib with different Loogle, LeanFinder and grep queries recorded
   in `searches.jsonl` and the new node. Also searched `lean/Sheaf` and upstream
   `WeilConjectures` for the column projection names and related equations.
   The results supply component APIs, not this signed generator theorem;
   no existing theorem directly closes it in a short proof.

4. **Route and pruning:** the kernel-subobject argument is a direct use of the
   tail's defining finite supremum and Mathlib's image/kernel lemmas. There is
   no unnecessary biproduct isomorphism or quotient invertibility argument.
   All original dependencies are used, and imports are minimal for the public
   signatures. Read `dag/units/sk-prop-av-pqf-finite.json`: its `realized`
   statement and step lists are empty, and the unit is the geometric
   proper/quasi-finite theorem. That inherited unit assignment does not describe
   this homological tool; this delivery preserves it and does not replace any
   realized unit step or chapter route.

5. **Nodes:** checked the new node's chapter, unit, source, creation record,
   blueprint origin, three kinds of search and Lean declaration against the
   file. Replaced its abbreviated statement by a self-contained statement and
   its flattened Lean signature by the verbatim signature. Expanded the
   generator docstring and node proof to cover both cone blocks and all
   extension-by-zero boundaries. Rewrote the original node's proof as the two
   steps actually implemented (generator-to-kernel containment, then filtration
   factorization and differential commutation). The union of their `uses`
   equals `proof_deps`; original statement and statement dependencies stay
   unchanged. Updated the proof-origin description accordingly.

**Changes from second reading:** repaired the generator module header, source
citation and complete natural-language proof; made its new node self-contained
and its Lean signature verbatim; recorded the independent searches; corrected
both nodes' proof descriptions and the report's decomposition accounting.
The Lean proof and all existing signatures and definitions were retained.
