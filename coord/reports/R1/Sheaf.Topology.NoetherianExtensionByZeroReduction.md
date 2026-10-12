## What changed

Proved `TopCat.noetherian_extensionByZero_reduction` with its signature unchanged.
The module now imports `Sheaf.Topology.ConstantSubsheafFiniteFiltration`,
`Sheaf.Topology.CohomologyReductionConstantSubsheaves`, and Mathlib's Ext exact sequences
as proof-only imports. Three proved private helpers give vanishing at the middle and
right positions of a short exact sequence and transport vanishing through an isomorphism.

The main proof applies the new finite-generation reduction, uses the existing finite
filtration of a finitely generated constant subsheaf, proves vanishing for each quotient
from the two extension-by-zero terms, and inducts over the filtration using the canonical
cokernel sequences. This implements the final paragraph of Stacks 02UX in Lean.
The existing item's node records this exact route.

## Proved and sorry left

`TopCat.noetherian_extensionByZero_reduction`: its sole original sorry is removed.
The finite-filtration cohomology argument is complete, as are all three private helpers.

One new sorry remains: `TopCat.noetherian_vanishing_of_constant_subsheaves`, in
`Sheaf.Topology.CohomologyReductionConstantSubsheaves`, node
`lem-sc-cohomology-reduction-constant-subsheaves`. It isolates the first three paragraphs
of 02UX: directed unions of finitely generated subsheaves, induction on generators,
and one-generator quotient kernels. Its extra premise is vanishing for finitely generated
subsheaves of the constant integer sheaf; the main proof establishes that premise by
finite filtration rather than assuming the original conclusion again.

Both delivered modules compile together locally without warnings. The delivery dry run
performs the server compilation and the stage-3 checks. The result is a reduction from
named statements, not a claim that its transitive sorry dependencies are closed.

## No longer needed

No nodes or modules are pruned, and no existing import was removed. The old direct
proof dependencies `lem-sc-topological-filtered-cohomology` and
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` no longer occur in the
item's `proof_deps`; both have moved to the new reduction node
`lem-sc-cohomology-reduction-constant-subsheaves`. They remain necessary for the argument. The constant-subsheaf
finite-filtration node and its module are still used directly. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition needed changing. The source was fetched read-only
from the Stacks project into the sandbox scratchpad because this machine has only the
literature lists. Its current label for 02UX is `lemma-vanishing-generated-one-section`,
whereas the old item node calls it `cohomology-lemma-vanishing-reduction`.

The filtration interface is sufficient as stated: `hQ` identifies each `Q i` with the
cokernel of the corresponding monomorphism. The proof explicitly builds that canonical
short exact sequence; it does not assume the auxiliary `S i` is the filtration sequence.
The latter sequence is used only to show that `Q i` has zero cohomology.

Edge cases checked: a zero-generator subsheaf is zero; an empty filtration (`m=0`)
uses only its zero initial term and terminal isomorphism; the empty space has only zero
abelian sheaves; `d=0` and the first allowed degree `q=1` still have `q+1>d`.
The new reduction accepts all of these cases and adds no nonemptiness or positivity
hypothesis. Searches via LeanFinder, Loogle, and Mathlib grep found the Ext exactness
API but no theorem that performs the topological reduction. LeanSearch returned HTTP
500 and is recorded as unavailable. Blueprint searches for finite-generation cohomology,
constant subsheaves, and one-section generation found no duplicate blueprint node.

## New nodes

`lem-sc-cohomology-reduction-constant-subsheaves`, module
`Sheaf.Topology.CohomologyReductionConstantSubsheaves`: the finite-generation and
one-section quotient reduction from Stacks 02UX, conditional on vanishing for finitely
generated constant subsheaves. The docstring and node give the full directed-union,
generator-induction, and finitely generated kernel argument. It is strictly a part of
the original proof: the main module still proves the entire finite-filtration step and
combines it with this reduction. No change record is needed: no existing public
signature, definition, or public import changed.


## Second reading by R1

1. Compared the full item module with the repository by diff. The existing theorem
   signature and docstring are byte-for-byte unchanged; all existing public imports
   remain unchanged. The only Lean additions are three private proved helpers,
   three proof-only imports, the item proof, and the new reduction module. No
   definition or existing public statement changed, so no change record is required.
2. Independently compiled both modules with lcompile.py, in import order: clean.
   Scanned both files for prohibited declarations and checked line widths. The sole
   delivered sorry is the named new reduction theorem listed above. Scratch-copy
   `#print axioms` checks give only propext, Classical.choice, and Quot.sound for
   each private helper; the item and new reduction additionally use sorryAx, as
   expected from the stated open dependencies. No definition contains sorry.
3. Read Stacks cohomology.tex, label lemma-vanishing-generated-one-section (02UX),
   against the new node and its Lean signature. Compactness, basis and intersection
   hypotheses match; the additional premise is precisely vanishing for finite
   coproduct-generated subobjects of the constant integer sheaf. Directed unions,
   induction on generators, the monic extension-by-zero map, and the degree-shifted
   kernel sequence justify the new lemma. It omits the finite-filtration argument,
   which the item actually proves, so it is a genuine partial reduction. Checked
   zero generators, empty space, d=0, and q=d+1: no extra positivity or nonemptiness
   assumption is used. Independent LeanFinder and grep searches using generators,
   finitely presented quotients, and integer subsheaves found no matching reduction;
   Loogle returned the cohomology definition and general sheaf APIs, not this lemma.
   Searches in lean/Sheaf and the upstream checkout found no duplicate. Closing
   this remaining lemma requires substantial generated-subsheaf/filtered-colimit
   formalization, rather than a short application of an existing theorem.
4. Read the proof from the item downward. Ext exactness supplies the two short-exact
   vanishing steps directly; no custom open lemma is needed for them. The hQ
   isomorphisms, rather than any unstated compatibility of S with the filtration,
   identify the canonical cokernels. The finite induction starts at the zero term
   even for m=0, and the terminal isomorphism gives K. All three new proof imports
   are used. The two displaced old direct dependencies remain in the new node;
   the report now names them explicitly. No module is pruned. The unit record
   sk-thm-curveestimate realizes thm-sc-proper-cohomology and has no listed steps;
   that realization and the source's extension-by-zero route are preserved.
5. Compared the existing node diff: only proof, proof_deps, and proof_origin change.
   These describe the applied reduction, quotient vanishing, canonical cokernel
   sequences, finite induction, and isomorphism transports actually in Lean. The
   new node has the required source, complete proof, dependency union, search
   records, creation/blueprint/unit metadata, and verbatim Lean statement.

Second-reading changes: clarified the displaced-dependency accounting in
`## No longer needed` and added this review. No Lean repair was necessary.
