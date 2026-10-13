## What changed

Completed `MvPowerSeries.FormalFiberDegreePDerivation` without changing its signature,
visibility, or original docstring. The proof rules out a pth root of a using Frobenius
injectivity and the degree assumption, clears its denominator as c=s^(p-1)b=s^p a,
applies the existing derivation detection theorem, extends that derivation, and proves
its value on a is a unit by the Leibniz rule in characteristic p.

Added the fully proved general helper `Derivation.exists_formalFiber_extension` in
`lean/Sheaf/RingTheory/FormalFiberDerivationExtension.lean`. It follows the finite-model
argument: unique prime, finite-completion comparison, tensor cancellation, localization,
completion, localization again, and transport. Private helpers construct localization
extensions and conjugate derivations explicitly; no new definition chooses an arbitrary
witness. Updated the parent DAG proof and recorded the new helper's node.

Both delivered modules compile together in import order using lcompile.py. Public
imports of the existing item and every existing signature are preserved. The extension
helper tests its tensor compatibility on every b in B, including the zero formal fibre.
The arguments also cover n=0, m=0 and q=0; prime p excludes the degree-one case.

## Proved and sorry left

Closed the one original hole: `MvPowerSeries.FormalFiberDegreePDerivation`
(node `new-lem-weil-pbc-degree-p-derivation-component`).

Also proved the new theorem `Derivation.exists_formalFiber_extension`
(node `new-lem-weil-pbc-finite-model-formal-fiber-derivation-extension`).
No sorry remains in either delivered module; zero holes added, zero split off.
This is a proof from existing library declarations, some of whose import closures
still contain sorry; it does not claim that the entire target closure is axiom-free.

## No longer needed

Removed the direct proof imports `Sheaf.RingTheory.CompletionFiniteExtension`,
`Sheaf.RingTheory.Derivation.CompletionAndLocalization`, and
`Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique` from the item: these are still
used by the proved extension helper and are not pruned from the total import closure.
Removed `Mathlib.RingTheory.Noetherian.Basic` from the item as unused.

The proof does not need `lem-weil-pbc-finite-algebra-noetherian` as a separate step;
it uses finite type over the complete local coefficient ring directly. Removed this
node from the parent's proof dependencies. Also removed the parent's direct edges to
`lem-weil-pbc-completion-finite-extension`, `lem-weil-pbc-derivation-extends`, and
`lem-weil-pbc-purely-inseparable-integral-prime-unique`: these three edges now belong
to the new extension helper and remain in the transitive proof route. No Sheaf module in the original route is
proved unnecessary throughout the target closure: regularity, normality, the finite
model, derivation detection and the three extension ingredients remain used.
Removed the unused `Mathlib.Algebra.MvPolynomial.NoZeroDivisors` import from the new helper.
The unit's realized statements and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's extension proof used `TensorProduct.smul_tmul'` for balancing
between factors; that lemma describes the external tensor action. The required lemma
is `TensorProduct.smul_tmul`. Supplying a local `DistribMulAction B H` instance from
the already installed module structure prevents expensive instance search. Both
modules now compile within the single-file limit.

WANTED: the local `literature/stacks-project/more-algebra.tex` copy is missing on this
machine. The source argument was checked read-only against
[Stacks Tag 07PR](https://stacks.math.columbia.edu/tag/07PR) and
[Stacks Tag 07PE](https://stacks.math.columbia.edu/tag/07PE). The new and updated proof
origins are marked agent for the Lean implementation rather than claiming to have
read the absent local document. No statement dispute or forced adaptation is needed.

## New nodes

`new-lem-weil-pbc-finite-model-formal-fiber-derivation-extension`, in
`dag/nodes/sec-proper-base-change/`, records the fully proved theorem
`Derivation.exists_formalFiber_extension` and its three existing proof dependencies.
It isolates the source's extension step for a general normal Noetherian domain,
not the parent's degree-p unit conclusion. The searches found no complete Mathlib or
library duplicate; LeanSearch was unavailable and is recorded as such. The blueprint
search returned no matching node. No change record is needed: existing interfaces
are unchanged and the new helper is imported only for the item's proof.

## Second reading by K2

1. **Existing interfaces — PASS.** Compared both delivered modules with the read-only
   repository. The only existing public declaration is
   `MvPowerSeries.FormalFiberDegreePDerivation`; its signature, visibility, and docstring
   are byte-for-byte unchanged. The declaration-table comparison reports no statement
   changes. The extension module is new. No definitions or target statements changed,
   and no forced adaptations or change records are needed.
2. **Proof and trust — PASS.** Independently compiled both modules in import order
   through lcompile.py (38.1 and 25.6 seconds), without warnings or errors. Scanned both
   files: no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   Scratch copies with `#print axioms` for both public theorems compiled cleanly and
   printed exactly propext, Classical.choice, Quot.sound, and sorryAx. The last comes
   from existing dependency holes, not a new hole. Read the private constructions too:
   localization uses the proved square-zero construction, and transport explicitly
   conjugates the additive map and proves the derivation laws. The derivative unit
   argument uses c=s^p*a and does not assume the final ring is nonzero.
3. **New statements and alternatives — PASS.** No unproved statement is split off.
   The fully proved extension theorem is strictly the extension part of the argument;
   it does not restate the degree-p unit conclusion. Read its docstring and matched
   the finite-completion equivalence and three extensions against Stacks
   [07PR](https://stacks.math.columbia.edu/tag/07PR),
   [07PE](https://stacks.math.columbia.edu/tag/07PE), and
   [07N9](https://stacks.math.columbia.edu/tag/07N9). Checked the cases M=K, q=0,
   characteristic zero, and a zero final localization: none requires an omitted
   hypothesis. The parent also permits n=0 or m=0 and excludes degree one by p.Prime.
   Repeated LeanFinder, Loogle, and Mathlib grep searches with different wording, and
   searched both library roots. No full duplicate was found. Existing localization
   wrappers are private or specialize to the same universe; the new helper handles
   distinct universes and arbitrary localization models. Mathlib's LinearEquiv.compDer
   changes only the codomain module, so it is not the required ring conjugation.
4. **Route and pruning — PASS.** Read downward from the unchanged theorem: Frobenius
   injectivity, finite model, denominator clearing, existing derivation detection,
   extension, Leibniz, unit factor. Every proof import supports one of these steps.
   New proof-only imports are plain imports; new public imports support signatures.
   The original public imports also supply the domain/prime instances required by the
   residue-field signature. Compared all old proof_deps with the new direct and
   transitive edges. The finite-algebra-Noetherian step is bypassed; three extension
   ingredients move behind the helper and are not pruned from the closure. Read
   sk-thm-p1.json realized: no unit statement or realized proof step is bypassed.
5. **DAG agreement — PASS.** Compared the existing node diff: only proof,
   proof_deps, and proof_origin change. Read the new node, its verbatim Lean signature,
   source, complete proof steps, dependency union, search records, creation metadata,
   blueprint provenance, chapter and unit. These match the code. Its statement is the
   general extension assertion, including agreement on every b in B and allowance
   for the zero ring.

Second-reading changes: clarified every removed direct dependency in No longer needed;
added independent Loogle search evidence to the new node; appended this review.
No Lean proof or signature repair was necessary. One original hole closed, zero holes
added, zero split off; no module pruned from the target import closure.
