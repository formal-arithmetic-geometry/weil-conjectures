## What changed

Proved the unchanged theorem `AlgebraicGeometry.perfect_tensor_hom_duality` in
`Sheaf.AlgebraicGeometry.PerfectTensorHomDuality` from the existing RHom comparison,
internal-Hom adjunction, and monoidal pullback model, together with two geometric
interfaces split off into new modules. The global opposite pairing is obtained by applying
the RHom comparison to the perfect dual and transporting along the first bidual isomorphism.
Mathlib's `tensorLeftAdjunction` supplies all four adjunctions. Upstream
`ExactPairing.map` supplies both pullback pairings without needing the RHom base-change
clause. Existential witnesses are eliminated within the theorem proof; no definition or
chosen-data construction is added.

Added proof-only imports for DerivedInternalHomAdjunction, DerivedPullbackMonoidalModel,
DerivedPullbackPerfect, DerivedTensorQCohClosure, and the upstream rigid OfEquivalence
module. Updated the item's proof and proof dependencies to match this argument.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.perfect_tensor_hom_duality`
(node `lem-pc-perfect-tensor-hom-duality`). The item's module has no remaining sorry.
This is a decomposition, not an independent axiom-free proof: existing imported theorems
still carry their own holes, and two holes were added:

- `AlgebraicGeometry.derivedPullback_preserve_perfect`, node
  `lem-pc-derived-pullback-perfect`, in DerivedPullbackPerfect. Only perfectness of
  derived pullback is asserted, for arbitrary perfect ambient objects; there are no
  duality, quasi-coherence, pairing or adjunction conclusions.
- `AlgebraicGeometry.canonical_derivedTensor_preserve_QCoh`, node
  `lem-pc-canonical-derived-tensor-qcoh`, in DerivedTensorQCohClosure. This is only tensor
  closure for the fixed canonical monoidal structure; it asserts no perfectness or duality.

Both statements were checked on zero objects and the empty scheme; neither needs
quasi-compactness, separatedness, or boundedness of the other tensor factor. Every new
hole is the whole proof of a named public theorem, with a source and proof in words.
The complete combining proof and both new modules compile with no warnings.

## No longer needed

Removed the direct proof-only import of Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
from the item. Its node `lem-pc-flat-complex-derived-pullback` is no longer a direct proof
dependency, but is retained below the new perfect-pullback lemma; it is not globally pruned.
The item's direct definition proof dependencies def-pc-perfect-complex and
 def-pc-derived-pullback are replaced by the named geometric interface and monoidal model;
their public statement imports and transitive mathematical dependencies remain needed.
No whole module can be claimed pruned from the targets' closure in this delivery.
The RHom base-change clause and the local dual-transport argument of the previous plan
are unnecessary: ExactPairing.map implements direct monoidal transport.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies have useful but incomplete interfaces for the packaging required
here: flatComplexDerivedPullback computes pullback of bounded flat representatives but
 does not itself assert perfectness of an arbitrary perfect object's pullback.
The tensor clause of derivedPullback_tensor_preserve_QCoh concerns
Q(Tot(P tensor N)) with a geometric K-flat hypothesis; it does not state closure for the
fixed global schemeDerivedTensorMonoidal tensor on arbitrary derived objects.
The two new geometric interfaces isolate exactly these gaps.
The canonical tensor closure is the remaining representative-to-global bridge for the
existing 08DX theorem, not a new mathematical tensor theorem.
The unit record sk-thm-picard-duality has no realized nodes in its statement/steps lists;
no unit's designated statement or step is bypassed.

WANTED: literature/stacks-project/perfect.tex, Tags 08DX and 09UA, for the two new nodes.
The Stacks source checkout is absent on this machine; the proof sketches were reconstructed
from the recorded library interfaces and are marked proof_origin.by = agent.

## New nodes

`lem-pc-derived-pullback-perfect`: DerivedPullbackPerfect, the perfectness-only part of
Step 3, proved in words by restriction to strictly perfect representatives and termwise
flat pullback. Blueprint searches for 09UA found no blueprint node; DAG search only found
the parent and RHom comparison. The latter does not state perfectness of pullback.

`lem-pc-canonical-derived-tensor-qcoh`: DerivedTensorQCohClosure, canonical derived-tensor
closure needed both globally and after pullback. The existing 08DX node states the result
through K-flat representatives; this new interface provides the bridge to the fixed global
tensor. Blueprint search for 08DX found no blueprint node. Three kinds of Mathlib search
were run; LeanSearch returned Internal Server Error and is recorded as unavailable.
No change record is needed: all existing statements and definitions are unchanged.

## Second reading by C3

1. I compared the delivered item module with the repository version. The theorem signature
and all existing declarations are unchanged; only proof imports and the proof body changed.
Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without
errors or warnings. The item has no remaining `sorry`; the two split declarations are named
public theorems whose entire proofs are explicit `sorry`s, with source and proof sketches in
their docstrings. No definitions contain `sorry`, and no forbidden declaration forms occur.
Verdict: pass.
3. I checked both split statements on the zero and empty-scheme edge cases and searched the
library for duplicate declarations. Each statement is a strict geometric interface needed by
the item and is not already present. The node JSON statements, Lean signatures, sources,
proof dependencies, and proof origins agree. Verdict: pass.
4. I followed the proof downward from the target: it uses the internal-Hom comparison,
canonical tensor closure, the monoidal pullback model, pullback perfectness, and pullback
quasi-coherence. The old flat-complex import and direct dependencies are no longer used;
the unit's designated route remains represented by the parent node. Verdict: pass.
5. The unit record and node metadata remain consistent with the revised route, and the
delivery report records the two decomposed holes and their nodes. Verdict: pass.

I changed only the report after the first preflight: this section was added to document the
independent second reading required by the stage-3 delivery contract.
