## What changed

Replaced the retained cyclic proof of
`AlgebraicGeometry.Scheme.Modules.coherent_generic_filtered_extension` with a
compiling reduction through the new `CoherentGenericFilteredSource` module. The
original theorem signature and docstring are unchanged. All original public
imports remain unchanged. Only this item and one new module are delivered; no
other group's module is adapted.

The main proof constructs the reduced induced subscheme of T, proves it integral,
and identifies its generic point with ξ. The new construction theorem supplies a
coherent filtered source A and a mono whose generic stalk is surjective. The main
proof constructs the actual categorical cokernel, obtains its coherence from
`coherent_kernel_cokernel_sum`, and uses `module_stalk_exact` to prove surjectivity
of its projection on every stalk. It explicitly proves that its generic stalk is
zero and its support is strictly smaller than T, then assembles the short exact
sequence. There is no support induction or choice of data from an unproved mere
existence theorem inside a definition.

The source construction is a strictly smaller step: it assumes a given integral
closed immersion, has no support equality hypothesis, and asserts neither a
cokernel, a short exact sequence, nor strict support containment. The topological
construction and the entire cokernel argument remain real Lean proofs here.

Both modules compiled locally without errors or warnings other than the intended
new theorem's sorry warning. The mandated dry run passed compilation and preflight,
with only the second reading pending; nothing was pushed. Sources read: Stacks 01YE
(lemma-prepare-filter-irreducible) and 01YF (lemma-coherent-filter), especially the
last paragraph. Searches in Mathlib via LeanSearch (unavailable), LeanFinder,
Loogle and grep, and local source searches, found no exact independent
filtered-source theorem. The unit record has no realized nodes; its route is
unchanged.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.Scheme.Modules.coherent_generic_filtered_extension`
(node `lem-pc-s3-coherent-generic-filtered-extension`). The item contains no sorry.

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.coherent_generic_filtered_source`
(node `lem-pc-s3-coherent-generic-filtered-source`, module
`Sheaf.AlgebraicGeometry.CoherentGenericFilteredSource`). Its proof is exactly
`by sorry`, with a source and complete proof in words.

This is a decomposition: one upper hole closed, one lower hole added, net zero
textual holes. It is not a claim of an axiom-free proof or positive net hole
reduction. The main theorem also uses existing coherent-closure and exact-stalk
declarations and the reduced-induced-subscheme declaration.

## No longer needed

No original public import was removed. The second reader removed the redundant
private import `Mathlib.CategoryTheory.Abelian.Exact`; exactness is already available
through the retained dependencies. Compared with the retained failed attempt,
the following private proof imports are absent:

- `Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion`;
- `Sheaf.AlgebraicGeometry.CoherentIdealSumCokernelReduction`;
- `Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationIdealSum`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.

The ideal-sum cokernel reduction module and node
`lem-weil-pbc-coherent-ideal-sum-cokernel-reduction` are no longer mathematical
proof dependencies of either delivered node: the main theorem proves the
cokernel/support assertions directly, and the source construction uses coherence
and nonzero-stalk arguments without taking a cokernel. This does not assert that
no other target path needs that module. The generic ideal inclusion and ideal-sum
filtration nodes remain needed by the new source-construction node, so they are
not claimed as transitively pruned.

## Where the brief, the DAG or earlier work was wrong

The retained proof compiled against the green snapshot but could not land: all
three planned proof imports reached this item through higher-direct-image
machinery. The explicit dry run reported the cycle
`CoherentGenericFilteredExtension -> CoherentGenericPointIdealInclusion ->
CoherentGenericPointClosedDescent -> ClosedImmersionPushforwardAnnihilated ->
AffinePushforwardBaseChange -> AffineMorphism -> FiniteFreeComplex ->
FinitePresentationIntegralFiltration -> FinitePresentationSupportReductionFiltration
-> CoherentIntegralFiltrationIrreducibleSupport -> CoherentGenericFilteredExtension`.

The original generic ideal inclusion and ideal-sum filtration declarations are
proved in the repository, but cannot be imported here under that architecture.
The new construction node records precisely the remaining part of the argument;
its next worker must account for those imports, or construct the source from
lower-level theory. The maintainer should still separate affine pushforward's
elementary quasi-coherence API from its higher-direct-image imports. No script
was edited, no cycle check was bypassed, and no unforced adaptation was made.

`blueprint_refs.py ancestor lem-pc-s3-coherent-generic-filtered-extension` reports
None because the existing node's created.item is a module name. The new node
records the broken ancestry honestly and names the exact source-construction
steps it serves. Blueprint search for generic constructions and local DAG
searches found no imported blueprint statement of this smaller construction.

## New nodes

`lem-pc-s3-coherent-generic-filtered-source`, in
`dag/nodes/sec-picard-framework/lem-pc-s3-coherent-generic-filtered-source.json`,
is the generic filtered-source construction, separated from the quotient/support
argument. Its coherent F, Noetherian X, integral closed immersion, nonzero generic
stalk and annihilation hypotheses match 01YE and the source-filtration part of
01YF. A zero target stalk is excluded explicitly; the nonzero stalk rules out a
zero ideal or zero summand count. F may have support away from the image of the
immersion, since the construction concerns its generic stalk. No change record
is needed: no existing signature, definition or public import changed.

## Second reading by R1

1. **Interface: pass.** Compared both delivered modules and the existing node with
   the read-only repository. The only existing declaration's signature and
   docstring are byte-for-byte unchanged; the four original public imports remain
   unchanged. Only its proof and private proof imports changed. There are no
   changed definitions, target statements, forced adaptations or change records.
2. **Proof and axioms: pass as a decomposition.** Independently compiled the two
   modules in import order with lcompile.py. Compiled a scratch copy of the main
   module with #print axioms for both public declarations: each uses exactly
   propext, Classical.choice, Quot.sound and sorryAx. The only new textual sorry
   is the named coherent_generic_filtered_source theorem. No forbidden axiom,
   unsafe/opaque/extern/implemented_by declaration, or hollow definition occurs.
   The reduced subscheme is an actual vanishing-ideal construction. The cokernel
   is the categorical cokernel, whose universal property determines it; no
   definition chooses arbitrary data from an unproved existence theorem.
3. **Split-off statement: pass.** Read Stacks 01YE and 01YF online and the existing
   generic ideal inclusion and finite ideal-sum filtration statements/proofs.
   01YE explicitly needs no support equality, so the source lemma is true even
   when F has additional support away from i(Z). Checked X = Z = Spec(k), where
   the construction is a finite-dimensional vector space with its partial-sum
   filtration; checked the zero-stalk and zero-ideal/rank boundary cases, which
   hx excludes. The source lemma leaves out the quotient, its coherence, the
   short exact sequence and strict support containment: these are genuinely
   proved in the main module, so this is a strict subproblem, not a renamed
   item. Its source, complete verbal proof and matching new node are present.
   Repeated LeanFinder, Loogle and Mathlib grep with different queries (recorded
   in searches.jsonl) and searched both local Lean roots. No independent exact
   replacement was found. The rank-one ideal inclusion has an extra dimension
   one hypothesis and cannot replace the arbitrary-rank construction. Closing
   the source lemma requires the documented import-cycle repair or lower-level
   source construction, beyond a few-minute proof repair.
4. **Route and pruning: pass after import repair.** Read the proof downward:
   generic-point identification, then the filtered source, then the real cokernel,
   stalk calculation and strict containment. The only unnecessary new import
   found was Mathlib.CategoryTheory.Abelian.Exact; removed it and recompiled
   successfully. All other new proof imports supply declarations used explicitly.
   Every old proof dependency is accounted for: reduced-induced-closed-subscheme
   stays; generic-point-ideal-inclusion and integral-filtration-ideal-sum move to
   the source node's proof plan; ideal-sum-cokernel-reduction is replaced by the
   explicit cokernel argument. Thus only the latter node is transitively bypassed
   by this argument. Read dag/units/sk-thm-picard-coherence.json: its realized
   statement and step lists are empty, and no unit/chapter route is replaced.
5. **DAG: pass.** The existing node changes only proof, proof_deps and
   proof_origin; its three steps track the actual main proof. The new node has
   the required source, statement dependencies, proof steps and their dependency
   union, searches, provenance, chapter/unit, blueprint ancestry record and Lean
   record. The Lean statement in each node matches its declaration. The new
   node honestly retains the generic-inclusion/ideal-sum prerequisites; it does
   not claim their cyclic modules can currently be imported into this item.

Second-reading changes: removed one redundant private Mathlib import, wrapped a
long source-docstring line, and made the direct versus transitive dependency
pruning explicit here. No proof, statement or definition needed correction.
The delivery still closes one original hole and adds one strictly smaller hole:
net zero, a decomposition rather than a completed axiom-free theorem.
