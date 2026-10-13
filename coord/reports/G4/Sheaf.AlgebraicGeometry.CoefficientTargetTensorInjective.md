## What changed

Proved `coefficientTarget_tensor_injective` from a geometric decoder, with a private,
fully proved tensor-induction lemma. Added `CoefficientTargetTensorDecoder` to isolate
construction and normalization of the decoder. The original statement is unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.coefficientTarget_tensor_injective` (one hole).
Added: `AlgebraicGeometry.Scheme.Modules.exists_coefficientTarget_tensor_decoder`
(one hole, node `aux-pc-coefficient-target-tensor-decoder`). This is a decomposition,
with net zero holes, not a completed affine geometry proof. The original module has
no remaining sorry. The private `tensor_leftInverse_of_generators` is fully proved.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
and `Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange` from the item;
they remain planned dependencies of the decoder, so neither is globally pruned.
The affine tilde/Gamma, open-immersion restriction and conjugate-unit nodes are also
needed by the decoder. No original node is globally pruned. The comparison-map
module remains public because it defines the supported sections in the statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The affine-sections theorem uses tensorPullback and
its chosen adjunction unit, rather than the standard pullback and the structural
A-action in this statement. Those chart, scalar and unit transports remain in the
new decoder theorem. The decoder has no candidate c or injectivity hypothesis;
the original theorem supplies the tensor-induction argument for arbitrary c.
Empty affine opens give zero modules and satisfy its formula. No flatness is used.

## New nodes

`aux-pc-coefficient-target-tensor-decoder` states existence of an R-linear map on
supported sections with its value on pullback-unit generators. It isolates the
geometric construction in the existing balanced-map proof; no inverse identity
on arbitrary tensors or injectivity is assumed. No statement or definition changes,
forced adaptations, or change records.

## Second reading by G4

1. Compared both delivered modules with the repository. The existing target declaration is byte-for-byte unchanged in name, parameters, hypotheses, conclusion, and visibility; only proof imports and proof bodies changed. The decoder is a new declaration with its own node and documented split. Verdict: pass.

2. Compiled both modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all`; compilation succeeded. Checked for forbidden declarations and `sorry`: the only remaining `sorry` is the named decoder theorem, which is listed with node `aux-pc-coefficient-target-tensor-decoder`. The target proof has no `sorry`. The private tensor left-inverse is fully proved. Explicit scratch-copy `#print axioms` checks for both public theorem declarations compiled successfully: each reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected from the open decoder. Verdict: pass; the open decoder is the declared decomposition.

3. Reviewed the split-off decoder statement and proof plan. It isolates the geometric construction from the final algebraic argument: it asserts existence of an R-linear decoder and its values only on supported generators, with no candidate forward map or injectivity conclusion. The target still proves the left-inverse identity on arbitrary tensors by induction and then cancels it; this is a decomposition, not a completed proof of injectivity from closed premises. Its docstring gives the geometric construction, balancing argument, edge cases, and source. Searches recorded in `searches.jsonl` and the node found no existing duplicate declaration. Verdict: pass.

4. Reviewed pruning and route. The target uses the decoder plus tensor induction and left-inverse cancellation; the unit route and all decoder proof dependencies remain represented. The two direct geometric imports removed from the target are imported privately by the decoder, so no dependency needed by the proof was lost. Verdict: pass.

5. Checked DAG agreement. The target node proof and `proof_deps` name only the decoder for the delivered theorem; the decoder node records the six geometric dependencies used in its stated construction. The unit and chapter fields are retained, and the new node has the required Lean record, source, proof, searches, and creation metadata. Verdict: pass.

Changed during second reading: no mathematical or interface changes; added this review section. Independent LeanFinder and Loogle searches found pullback/adjunction infrastructure and TensorProduct.ext, respectively; neither closes the geometric decoder. The unit realized record currently has empty statement and step lists; this delivery is below the unit level and does not alter that pre-existing record.
