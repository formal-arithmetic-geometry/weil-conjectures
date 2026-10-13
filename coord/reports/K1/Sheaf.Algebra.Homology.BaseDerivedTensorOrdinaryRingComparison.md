## What changed

In Sheaf.Algebra.Homology.BaseDerivedTensorOrdinaryRingComparison, replaced the
whole sorry of ModuleCat.exists_baseDerivedTensor_ordinary_ring_comparison with
an explicit reduction. The public statement and existing docstring are unchanged.
Added proof imports Mathlib.RingTheory.TensorProduct.Maps and
Sheaf.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison.

The tensor-ring equivalence is constructed by forward and inverse mapRingHom
maps, with both inverse laws proved by tensor induction. The ordinary chain
isomorphism is assembled from termwise semilinear tensor equivalences; its
linearity, differential square, inverse and generator equation are proved.
The module obtains restricted derived cohomology transport from one new lemma,
then proves tensor-algebra linearity using the A-action and B-linearity and
upgrades the additive equivalence via LinearEquiv.ofBijective. Extensionality
proves the requested comparison square. The scalar-extension helper follows
the already proved private helper in SemilinearScalarExtensionHomologySquare;
that module is not imported, since its helper is private.

Updated the parent node's proof, proof_deps and proof_origin to this actual route.
The new node inherits sec-picard-framework and sk-thm-picard-semicon. The unit's
statement and steps are preserved; its realized fields do not name this node.

## Proved and sorry left

Closed the original whole proof hole:
ModuleCat.exists_baseDerivedTensor_ordinary_ring_comparison
(lem-pc-base-derived-tensor-ordinary-ring-comparison). No sorry remains in the
item's module or in its private helpers.

Added one public theorem with exactly `:= by sorry`:
ModuleCat.exists_baseDerivedTensor_restricted_ring_comparison
(lem-pc-base-derived-tensor-restricted-ring-comparison), in
Sheaf.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison.
This is a decomposition: one upper hole closed, one lower hole added, net zero.
The new lemma only transports restricted derived cohomology and its counit;
it neither constructs the tensor-ring equivalence nor the ordinary chain
isomorphism and does not assert tensor-algebra linearity. All those parts are
proved in the caller. It is therefore a strict part of the argument, not the
original existence theorem under a new name.

Checked edge cases: no nontrivial-ring, boundedness, flatness or isIso-comparison
hypothesis has been added. The ring/chain constructions cover zero rings and
zero complexes. The residual lemma uses only universal derived functors and
exact coefficient equivalences and permits both morphism universes. The maps
to C₀ and C are unused, as required by the original statement.

## No longer needed

None. No original import was removed. The cohomology model remains necessary
for the statement and its scalar-extension additive instance. The abstract
derived-category definition remains a statement dependency and a dependency
of the new restricted transport lemma. No blueprint unit or required unit
step is bypassed. RingIsoNaturality and RingTransport were considered but are
cyclic with this item, so neither is imported. The fixed-ring quasi-isomorphism
comparison and model-independence modules are not needed by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The earlier plan called the first step elementary;
its formalization also needs a target-ring linearity proof for semilinear tensor
equivalences and a differential square, which are now explicit. The old
proof_deps listed only definitions and provided no lemma assembling the exact
coefficient-equivalence/derived-counit transport. That assembly is the new
strict intermediate item. LeanSearch was unavailable; LeanFinder, Loogle and
local source searches were run, and their outcomes are in the new node.

## New nodes

lem-pc-base-derived-tensor-restricted-ring-comparison:
restricted B₀-linear derived-cohomology transport, A-action compatibility and
the underlying ordinary comparison square. Its module is
lean/Sheaf/Algebra/Homology/BaseDerivedTensorRestrictedRingComparison.lean.
The source and complete proof in words are in its docstring and node.
No statement, definition or public import was changed; no change record or
forced adaptation is necessary.

## Second reading by K1

1. **Statements and interfaces.** Compared the delivered ordinary module with
the repository version. The target signature is byte-for-byte unchanged; the
new restricted theorem has the documented strict intermediate statement.
Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`.
The ordinary target has no `sorry`; the only remaining `sorry` is the named,
documented restricted transport theorem. No forbidden declarations occur.
Verdict: pass, with the documented split hole.

3. **New statement.** Checked the restricted theorem's edge cases and
hypotheses: it adds no flatness, nontriviality, or comparison-isomorphism
assumptions and is strictly weaker than the parent target. Its DAG node,
docstring, and Lean declaration agree. Verdict: pass.

4. **Pruning and route.** The proof uses the tensor-product map, explicit
extension-complex construction, and the restricted transport lemma; no
existing import can be removed without losing a used declaration, and the
unit route is retained. Verdict: pass.

5. **DAG agreement.** Updated proof, proof dependencies, and proof origin for
the parent node to match the written proof, and checked the new node metadata.
Verdict: pass.

Changed only the two delivered modules, their node records, and this report;
the added public declaration is the necessary split-off transport result.
