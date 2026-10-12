## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.FinitePresentationIntegralFiltration`
by a complete well-founded induction on `TopologicalSpace.Closeds X`. The induction
assertion covers all finitely presented modules whose support closure is contained in
the induction bound. Strictly smaller support closures trigger the recursive call;
ideal-pushforward quotients are retained. Isomorphism invariance of the factor predicate
is proved explicitly and the coarse chain is refined to the required chain.
The original theorem signature, universes, visibility and three public imports are unchanged.
The two added imports are ordinary proof imports.

Added `Sheaf.CategoryTheory.FiniteFiltrationRefinement`, fully proved. Its three principal
private helpers identify mapped consecutive quotients, expand the proved upstream
`ObjectProperty.filtrationClosure` into a subobject chain, and put a subobject chain back
into the closure by index induction and short exact sequences. The public theorem then
refines an outer chain by the supplied filtrations of its factors. The source-library
module `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions` supplies the
proved closure-under-extensions machinery; it has no holes and no import path to the item.

Added `Sheaf.AlgebraicGeometry.FinitePresentationSupportReductionFiltration`, which states
the geometric part of Tag 01YF BEFORE induction on smaller supports. This proper part
of the argument leaves finitely presented smaller-support factors unresolved. The
reducible-support, J-adic and generic-ideal-inclusion construction is documented in full,
and its node preserves the substantive existing proof dependencies. Updated the item's
node to follow the actual support induction and refinement proof.

All three modules compile together via lcompile.py. The delivery dry run passed its
compile, axiom and preflight checks; only the independent second reading remains. The refinement theorem compiles with
no holes. Source read: Stacks `coherent.tex`, label `lemma-coherent-filter` (Tag 01YF),
including `lemma-prepare-filter-support` and `lemma-prepare-filter-irreducible` (Tag 01YE).
The source was read in the local literature copy and Tag 01YF online.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_integral_filtration`, node
`lem-pc-e2-finite-presentation-integral-filtration`.

The new `CategoryTheory.finite_filtration_refinement`, node
`lem-pc-s3-finite-filtration-refinement`, and its four private helpers are completely proved.
They use the source library's proved extension machinery, rather than a second geometric
filtration statement.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_support_reduction_filtration`,
node `lem-pc-s3-support-reduction-filtration`. Its proof is exactly `by sorry` and it is the
only hole in the delivery. There is no hole in a definition or private declaration.

This is a decomposition: one upper hole closed and one strictly weaker geometric hole
added, with support induction and categorical refinement proved here. It is not a complete
proof of Tag 01YF and does not claim a net decrease of the hole count. The new hole does
not assert the original conclusion: smaller-support factors are permitted to be arbitrary
finitely presented modules, and no filtration of those factors is provided. Recursive
calls in the main theorem perform that remaining step and the proved refinement theorem
combines their filtrations. No data is defined by choosing a witness from an unproved
existence statement; all use of the open theorem is confined to a proposition proof.

## No longer needed

No existing import was removed and no whole module is claimed pruned from the targets'
import closure. The original geometric obligations have moved into the proper geometric
subproblem, rather than being silently discarded. The noetherian-support induction stays
in the item's proof. The existing stronger
`Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes` is not imported because
it would close an import cycle through `FiniteFreeComplex` back to the item.

The finite geometric subproblem uses the ideal power and product definitions from
`Sheaf.AlgebraicGeometry.IdealModuleProductStalk`; it does not need the adic inverse-system
interface of `def-weil-pbc-coherent-formal-module` or the tensor-pullback construction
`def-pc-module-pullback` as PROOF dependencies. Their definition roles and other users
are retained; no claim of whole-library pruning is made. All other original geometric
proof dependencies are retained in the new node, with the proved categorical refinement
node added for concatenation.

The complete list of old direct proof dependencies now used only by the geometric
subproblem is:

- `def-pc-integral-scheme`
- `def-weil-closed-immersion`
- `def-weil-irreducible-components`
- `lem-weil-pbc-basic-open-function`
- `lem-weil-pbc-closed-immersion-coherent-equivalence`
- `lem-weil-pbc-closed-pushforward-stalks`
- `lem-weil-pbc-coherent-generic-point-ideal-inclusion`
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`
- `lem-weil-pbc-coherent-support-power-ideal-kills`
- `lem-weil-pbc-coherent-support-union-exact-sequence`
- `lem-weil-pbc-finite-type-module-support-closed`
- `lem-weil-pbc-ideal-module-product-stalk`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-immersion-base-change-lft`
- `lem-weil-pbc-module-iso-on-stalks`
- `lem-weil-pbc-module-stalk-exact`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `lem-weil-pbc-scheme-sober`
- `pqf-lem-coherent-ft-locnoeth`
- `pqf-lem-locnoeth-lft`

The other two old direct proof dependencies, `def-pc-module-pullback` and
`def-weil-pbc-coherent-formal-module`, are no longer proof dependencies of either
node, for the reasons above. The Mathlib minimal-closed-subset dependency remains
directly used through its well-founded-closed-set instance. These are dependency
relocations and two discarded proof interfaces, not modules pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier coherence wrapper was an equivalent restatement and is not reused. The
current reduction implements support induction and proves the categorical assembly.
The original node's minimal-counterexample text is replaced by equivalent well-founded
induction on closed support bounds. The geometric node deliberately does not invoke
support minimality: a reducible support produces two unresolved proper-support factors,
and irreducible support produces ideal factors and proper-support cokernels.

The coarse statement was checked on the empty scheme and zero module (empty chain),
an integral ideal (one ideal factor), reducible support (two proper-support factors),
and nonreduced irreducible support (finite J-adic layers followed by generic inclusions).
It does not require a nonzero ideal or strict subobject chain. The categorical proof
handles length-zero chains, repeated subobjects, and predicates that do not contain zero.
Its bottom/top and last-quotient cases are explicit Lean arguments.

The unit `sk-thm-picard-coherence` has no realized statement or step nodes; its records
and the chapter route are unchanged. Project-wide searches found the existing geometric
filtration theorem and the proved upstream `filtrationClosure` machinery. LeanSearch
returned Internal Server Error for both new statements and is recorded unavailable;
LeanFinder and actual Mathlib grep searches were run and are recorded in searches.jsonl.

## New nodes

`lem-pc-s3-finite-filtration-refinement`: a general abelian-category refinement theorem,
with no remaining hole. Its source is the induced-filtration and J-adic-refinement steps
of Tag 01YF. It combines proved source-library extension closure with a new fully proved
conversion to the exact subobject/cokernel interface used by the item.

`lem-pc-s3-support-reduction-filtration`: the geometric coarse-filtration step of Tag 01YF,
with one named hole. Its two alternatives isolate strictly smaller support before any
inductive resolution. Its node records the existing coherence, support-union, ideal-power,
reduced-induced-subscheme, generic-inclusion and stalk ingredients, and categorical
refinement for the finite J-adic assembly. There are no statement changes, forced
adaptations, change records, or edits to modules held by another group.

## Second reading by S3

1. Compared the delivered item with the repository using diff and a byte comparison
   of its full theorem signature: identical signature, universe, namespace and visibility.
   No existing definitions changed; the other two modules are new. Existing public
   imports are unchanged and the two added imports are private proof imports. PASS.
2. Compiled all three delivered modules together with lcompile.py in import order.
   Read every proof and all four private categorical helpers. Exactly one textual hole
   remains, the public named support-reduction theorem listed above. No forbidden
   declarations or hollow definitions occur. A separate scratch module printing axioms
   shows refinement uses only propext, Classical.choice and Quot.sound; the geometric
   hole and the original theorem additionally use sorryAx, as reported. PASS as a
   decomposition, not as an axiom-clean proof of the geometric target.
3. Read the new statements and their nodes against Stacks
   [01YF](https://stacks.math.columbia.edu/tag/01YF) and
   [01YE](https://stacks.math.columbia.edu/tag/01YE). The coarse result is a proper
   geometric subproblem: it does not resolve any proper-support quotient. Checked
   empty scheme, zero module, one ideal factor, reducible support, and nilpotent
   thickening/J-adic layers. For refinement checked zero-length outer/inner chains,
   repeated subobjects, and P identically false (only zero objects can satisfy the
   premise). Sources and complete prose proofs are present. Independent LeanFinder
   search for devissage/proper support/generic ideals and Loogle plus Mathlib grep
   for subobject chains found no replacement. Repository searches found the stronger
   coherent theorem, which is still open and has the reported import cycle, and the
   proved upstream filtrationClosure machinery already used here. PASS.
4. Read the support-bound induction from the top: the recursive bound strictly
   decreases by lt_of_lt_of_le, and isomorphism transport has the correct direction.
   The categorical proof uses proved closure-under-extensions rather than another
   open refinement theorem. The public imports provide signature vocabulary; added
   proof imports are used. No shorter available route was found. Expanded the
   no-longer-needed section to enumerate every relocated original dependency and
   distinguish those from the two discarded proof interfaces. The unit record's
   realized statement and step lists are empty and unchanged; its route is kept. PASS.
5. Compared the node statements and verbatim lean.statement records with the Lean
   declarations; checked proof_deps equals the union of proof-step uses in all three
   nodes. The original node records exactly induction, support reduction and refinement;
   the geometric node retains the original geometric obligations. Both new nodes have
   source, provenance, actual search records, creation data, blueprint ancestry, unit,
   chapter and Lean records. PASS.

Second-reading changes: completed the dependency enumeration in this report and added
this review. No Lean proof, statement, definition, import or node needed repair. The
remaining geometric theorem is not a few-minute consequence of the available proved
interfaces, so it remains explicitly open. Hole accounting remains one original hole
closed, one new hole added, net zero; categorical refinement is fully proved.
