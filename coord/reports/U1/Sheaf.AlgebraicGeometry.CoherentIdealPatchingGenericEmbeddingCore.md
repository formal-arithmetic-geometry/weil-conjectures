## What changed

Replaced the only sorry in
`Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingCore` with a complete Lean
reduction. The original theorem signature and public imports are unchanged. Added proof-only
imports for the generic ideal inclusion, the existing common generic lattice, coherent finite
sums, the forgetful finite-limit calculation, and the new annihilator-factorization lemma.

The proof handles a zero ideal pushforward directly with rank one; identifies the two generic
points; obtains a positive-rank nonzero ideal lattice; forms its finite sum and both generic
monomorphisms; obtains the ideal-product factorization; and proves the final mono and stalk
surjectivity using the ideal-product range formula and cancellation through an injective stalk
map. The private theorems prove finite-limit preservation of module stalks and invertibility
of stalk maps on finite biproducts. No chosen data definition or interface adaptation is added.

Compiled both delivered modules in import order without errors or warnings. All Lean lines
are at most 100 characters. The factorization is the only new statement: unlike the original
statement, it has no integral subscheme, no ideal on that subscheme, no finite sum or rank,
and no map into that sum. The finite-sum construction and the final combination are proved.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.coherent_ideal_patching_generic_embedding_core`
(node `lem-weil-pbc-coherent-ideal-patching-generic-embedding-core`). No sorry remains in
the assigned module.

Added and left: `AlgebraicGeometry.Scheme.Modules.coherent_generic_mono_ideal_factor`
(node `lem-weil-pbc-coherent-generic-mono-ideal-factor`), in the new module
`Sheaf.AlgebraicGeometry.CoherentGenericMonoIdealFactor`.

This is a decomposition: one upper hole closed and one strictly smaller hole added, net zero.
The existing `integral_ideals_common_generic_lattice` declaration still has its pre-existing
sorry; it is used rather than duplicated. Other imported proofs can also rest on existing
holes. They are not new holes of this delivery.

Edge cases: zero i_*I uses r=1; r=0 or A=0 contradicts the nonzero generic stalk of G.
The factorization lemma allows arbitrary points, zero cokernels and zero modules; its
annihilator argument remains valid without compactness. The empty integral source is
excluded by IsIntegral.

## No longer needed

No original imports are removed: all five original public imports are needed by the unchanged
statement. No module can be claimed globally unreachable from this delivery.

The trial proof-only import `Sheaf.AlgebraicGeometry.CoherentIdealSumCokernelReduction`
and its node `lem-weil-pbc-coherent-ideal-sum-cokernel-reduction` are not needed by this proof:
nonzeroness of A follows directly from the zero-ideal affine-section calculation. They are
not imported in the final module. This is local pruning only; other users can still need them.

## Where the brief, the DAG or earlier work was wrong

The assigned node's proof was a single placeholder, with no proof dependencies or numbered
geometric steps. Its Lean docstring referred to the complete geometric construction; the
parent node and the primary source supplied that construction. The node copy now records the
actual Lean route, including the existing common-lattice theorem and the new factorization.

The node's prose requests generic bijectivity although this core Lean statement requests only
surjectivity. The unchanged Lean conclusion is proved; generic injectivity follows separately
from monomorphy, as the existing parent decomposition already intends.

The common-lattice module initially lacked its compiled artifact. It became available on the
next refresh and is now imported normally. LeanSearch returned an Internal Server Error;
LeanFinder and source grep found no matching annihilator-factorization theorem.

WANTED: `literature/stacks-project/coherent.tex`, Tags 01YL and 01YE, is absent on this worker
machine. The sources were read at https://stacks.math.columbia.edu/tag/01YL and
https://stacks.math.columbia.edu/tag/01YE. The proof-origin records are marked agent for the
adaptation. The chapter and unit records and their realized steps are untouched; the common
lattice is used as a geometric tool and no unit-level route is bypassed.

## New nodes

`lem-weil-pbc-coherent-generic-mono-ideal-factor` is the coherent-cokernel annihilator step:
a generic coherent mono contains an ideal multiple of its target, with a full ideal stalk.
Its new module contains one public theorem with exactly `:= by sorry`, a source and complete
proof in words. The node expands the cokernel, annihilator and kernel-factorization arguments
with their existing proof dependencies and records all three required search kinds.
Change record: `coord/changes/coherent-ideal-patching-core-scoped-proof-commands.md`.
Preflight treats the added scoped commands conservatively as an interface change; the record
explains their locality and the unchanged public signatures and imports. No forced adaptation
is needed. The stalk-limit helper is a private theorem, installed as an instance only locally.

## Second reading by U1

1. Interface preservation: compared the complete core module with the repository using
   diff and separately compared the theorem signature as bytes. It is identical, including
   the hypotheses, the specified biproduct, and both surjectivity conclusions. The existing
   docstring and all five public imports are unchanged. There are no definitions added or
   adapted modules. The new local instance attributes and noncomputable section are covered
   by the change record and end within this module. Verdict: pass.

2. Kernel verification: compiled both delivered modules in import order with lcompile.py:
   the factor module took 2.4 seconds and the core took 9.1 seconds, with no errors or warnings.
   Compiled a scratch copy with explicit #print axioms for both public declarations. Each
   reports exactly propext, Classical.choice, Quot.sound, and sorryAx. The core has no sorry;
   the sole new sorry is exactly the named factorization theorem listed above. Its module
   has no data definitions. The core's existential eliminations are inside a Prop proof,
   not witness-based data definitions. No forbidden declaration or compiler escape is used.
   The two private stalk helpers have complete proofs. Verdict: pass as a decomposition,
   not as an axiom-free completion of the import closure.

3. New statement: read Stacks 01YL (lemma-property-irreducible-higher-rank-cohomological),
   especially its ideal-power containment and final intersection argument, and 05JU
   (morphisms-lemma-scheme-theoretic-support) and 05JV on the Stacks website. The new lemma
   isolates the containment step by taking the annihilator itself. Coherence of the cokernel
   and coherent/quasi-coherent finite-type equivalence supply the hypotheses of the existing
   schemeTheoreticSupport statement. Its affine annihilator equality and support equality,
   together with quasi_coherent_ideal_zero_set_affine, give a full ideal stalk at the chosen
   point. The affine product-range statement proves vanishing of the product-to-cokernel
   composite, and abelian kernel factorization gives the unique lift through the mono.
   Read the cited node statements, including module_stalk_exact and the Mathlib kernel-lift
   exactness match; they supply the indicated facts. No integral, generic-point or compactness
   assumption is silently used in this new lemma. Tested the zero cokernel (unit annihilator),
   zero target and source (zero maps), and the affine example tR -> R at a point where t is
   invertible (annihilator (t)); each satisfies the precise conclusion. On a noncompact
   locally Noetherian scheme the affine annihilator construction still glues, so no uniform
   power or finite affine cover is required. The statement is strictly smaller than the item:
   it supplies no rank, common lattice, embedding into an ideal sum, or final stalk surjection.
   Its docstring gives the complete argument and its node matches its Lean signature.
   Independent LeanFinder query used "annihilator sheaf of a finite type quotient vanishes
   at a point, ideal times module contained in submodule" and found only module support
   facts, not this sheaf factorization. Launcher grep and targeted rg over Mathlib's scheme
   module/ideal files, the upstream algebraic geometry files and lean/Sheaf found no existing
   replacement; schemeTheoreticSupport gives the annihilator but not this factorization.
   Verdict: true, sourced, useful, and not a relabeling or duplicate.

4. Route and pruning: followed the proof from the zero-pushforward branch through the
   generic inclusion, rank/ideal nonzeroness, common lattice, finite sums and final factor.
   The stalk-sum helper uses finite-limit reflection and Mathlib's biproduct comparison;
   the final surjectivity is proved by the product range formula and injective cancellation.
   All six added imports are proof-only and serve these steps. The five original public
   imports provide the unchanged interface. The old node had empty proof_deps, so there is
   no omitted old dependency in No longer needed; the unused trial reduction is explicitly
   reported without claiming global pruning. Read dag/units/sk-thm-p1.json, including its
   realized statement and all four step lists: none is replaced or changed, and this local
   geometric tool remains below the unit route. Closing the factor theorem would require
   formalizing the annihilator and affine factorization steps; no immediate existing
   specialization closes it in a few minutes. Verdict: pass; net holes zero, pruned none.

5. DAG agreement: the existing node differs only in proof, proof_deps and proof_origin.
   Its four steps match the actual zero branch, generic inclusion, sum of common lattices,
   and ideal factorization followed by stalk cancellation. Their uses have union exactly
   proof_deps. The new node has a self-contained statement, source, four proof steps and
   their dependency union, agent proof origin, recorded searches, creation/blueprint records,
   matching chapter and unit, split status, and the verbatim Lean theorem signature.
   The pre-existing prose says bijective where this unchanged core signature says surjective;
   the report correctly records this and the parent supplies injectivity separately. No
   statement or dependency field was silently altered to make the proof easier. Verdict: pass.

Second reading changed only this report by adding the independent review. No Lean or DAG
repair was necessary. Scratch axiom probes were removed before delivery.
