## What changed

Repaired reader return H10 (reviewer X-3935d, head 3935d42e2).
`Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRange` now keeps the standard
product witnesses used by its original statement. Removed the two local registrations
of `IsSingletonTensorDegreeComparison._proof_1` and `._proof_2` from the returned version.
Those opaque witness references changed the elaborated presentation of the result and
made its direct importer expensive to elaborate, despite preserving the mathematical type.

Added the proof-only import `Sheaf.AlgebraicGeometry.EtaleSingletonTensorPureImage`.
The new theorem isolates conversion of the normalization equation to canonical evaluation.
The range theorem constructs the fixed lifted pure tensor as its preimage and composes
its image equality with the equality presenting the generator. The inferred preimage
is that explicit tensor from the new equality, not a witness chosen from an existence proof.
The primary theorem's statement, visibility and docstring are unchanged.

The three-file ordered compile succeeded: the new formula in 15.0 seconds, the range
module in 5.2 seconds, and the unchanged direct importer in 4.4 seconds. These are the
wall times reported by lcompile.py; its 60-second compiler limit was not raised.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_normalized_range`
(node `new-etale-singleton-tensor-normalized-range`), one of one original holes.

Added and still sorry:
`AlgebraicGeometry.Scheme.singletonTensorDegreeComparisonHom_pure_image`
(node `new-etale-singleton-tensor-pure-image`). Its proof is exactly `by sorry`.
It states the image equality for the prescribed lifted tensor. It does not assert
range membership and does not move the original range-subset statement to another name.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
There are no other new holes, no sorry in a definition, and no remaining sorry in the
primary module. The new formula has its source and complete proof in words in its docstring.

## No longer needed

Removed the returned version's two local witness registrations. No library module is
pruned. The public import of the normalization module is still required by the signature.
Its node remains a statement dependency and a proof dependency of the new pure-image node;
the parent's direct proof dependency is now the pure-image node.

## Where the brief, the DAG or earlier work was wrong

The earlier second reading tested the primary module and its axioms, but did not validate
the sole direct importer against the resulting interface. H10 reported two 60-second
timeouts. The timeout was reproduced locally. Simply adding the same local registrations
to the importer did not repair it; explicit universe arguments and generic group helpers
also did not produce a valid compile against a stable repaired-module overlay.

The canonical pure-image equality is mathematically a definitional transport of the
existing normalization predicate. Its remaining task is the long Lean transport between
product witness presentations. The existing normalization-evaluation theorem gives an
existential map and does not identify it with the fixed canonical evaluation used here.
The unit route is unchanged; only this below-unit computational step is separated.

## Forced adaptations

None. `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeSurjective` is unchanged
byte for byte from the repository, including every signature, visibility, import and proof.
Its original failure against the returned module was:

```text
timeout after 60 s: the fault is usually a definition that is expensive to unfold, not the limit
```

Exact repair lines in the primary module, relative to the returned delivery: remove the
comment and local attribute block registering the normalization predicate's `_proof_1`
and `_proof_2`; add the proof-only import of `EtaleSingletonTensorPureImage`; replace the
explicit-tensor/`hf` proof term with:

```lean
  exact fun y ⟨p, hp⟩ ↦
    ⟨_, (singletonTensorDegreeComparisonHom_pure_image.{u}
      X F U W g n f hf p.1 p.2).trans hp⟩
```

These changes restore the standard product-witness presentation of the primary signature.
They remove the need for any forced edit to the unclaimed importer. Compiled the importer
only after its new dependencies had finished compiling, so the check used the repaired
sandbox outputs, not a transient fallback to the shared baseline.

## New nodes

`new-etale-singleton-tensor-pure-image`, in module
`Sheaf.AlgebraicGeometry.EtaleSingletonTensorPureImage`, isolates canonical evaluation of
a prescribed lifted pure tensor. It is the normalization step of the preimage argument;
the primary module supplies the separate range witness and equality composition.
Edge cases n=0, zero coefficients/functions and empty schemes use the same equation.
The node records all three searches. The parent node's proof, proof_deps and proof_origin
were updated to agree with the compiling proof. No definition or target statement changes.

## Earlier second reading (a previous round; superseded)

The primary module and new dependency compile in import order. The direct importer compiles
unchanged in 4.4 seconds against the repaired sandbox outputs. The new theorem's statement
is a strict equality for one prescribed lifted pure tensor; it is a proper substep of the
range theorem and is not a restatement. Its remaining `sorry` is named and documented.
The parent node's route remains the explicit pure-tensor preimage argument, with the
normalization step separated below the unit level.

## Second reading by Q4

1. **Interface and accidental changes.** Compared both delivered existing modules with the repository. The
   target theorem `singletonTensorDegreeComparisonHom_normalized_range` has the same signature,
   visibility and docstring; its proof-only import and proof body are the only changes. The direct
   importer `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeSurjective` is byte-for-byte
   unchanged. Verdict: pass.

2. **Proof and axioms.** Compiled the three-file sandbox in import order with `lcompile.py`, including
   the direct importer. The range theorem has no `sorry`; the only remaining `sorry` is the named
   `singletonTensorDegreeComparisonHom_pure_image` theorem, exactly the split-off theorem listed above.
   The axiom probe reports only `propext`, `Classical.choice`, `Quot.sound`, and the expected
   `sorryAx` through that open dependency. No axiom, unsafe, opaque, extern or hollow definition was
   added. Verdict: pass for the closed proof and documented open dependency.

3. **Statements and searches.** Read both node records and searched the library and Mathlib for
   existing singleton tensor image/evaluation results. Only generic composition and tensor-product
   lemmas were found; no existing canonical-map formula duplicates the new statement. The pure-image
   statement is a strict equality for one prescribed tensor, while the parent is a range inclusion,
   so the split is proper, true, and exactly the normalization substep needed. Verdict: pass.

4. **Pruning and route.** The parent proof uses only the new pure-image node and the public
   normalization import. The old local auxiliary-instance registrations were removed, and no library
   module is pruned. The explicit tensor witness is constructed directly, so no arbitrary witness is
   chosen from an existence theorem. Verdict: pass.

5. **DAG and unit route.** The parent node's `proof`, `proof_deps` and `proof_origin` match the proof;
   the new node records its Lean statement, source, searches and decomposition. The unit route is
   unchanged; this is a below-unit computational step. Verdict: pass.

Changed only the report during this reading. No Lean statement, definition, existing node statement,
unit record or direct importer was changed.
