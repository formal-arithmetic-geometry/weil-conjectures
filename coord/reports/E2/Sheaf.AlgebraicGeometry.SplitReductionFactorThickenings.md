## What changed

Proved `AlgebraicGeometry.Scheme.exists_split_reduction_factor_thickenings` in
`Sheaf.AlgebraicGeometry.SplitReductionFactorThickenings`, keeping its signature and
all public imports unchanged. The proof constructs the factor-image opens through
Mathlib's finite-product and nilradical-quotient prime-spectrum homeomorphisms.
Surjective ring maps give closed immersions into Spec R; factoring through the
image opens gives the required surjective closed immersions. Algebra-equivalence
linearity proves the structural-map identities. Updated the theorem's proof
explanation and its DAG node to record this direct route.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.exists_split_reduction_factor_thickenings`
(node `lem-weil-pbc-split-reduction-factor-thickenings`). No holes added or left;
this is a complete proof, not a decomposition. Local single-file compilation
passes without errors or warnings. The proof uses no project theorem containing
sorry. The construction includes the empty index set and zero-ring factors:
Mathlib's sigma spectrum homeomorphism handles both without nonemptiness assumptions.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism`.
Its node `lem-weil-pbc-reduction-universal-homeomorphism` is unnecessary for this
proof: only the affine nilradical quotient homeomorphism is needed, and Mathlib
proves it directly. The planned node
`lem-weil-pbc-finite-affine-coproduct-spectrum` and its scheme-coproduct construction
are also unnecessary for this proof: `PrimeSpectrum.sigmaToPiHomeo` supplies the
needed topological partition. No proof imports remain; the existing public imports
already expose all the Mathlib ingredients. These are removals from this item's
proof dependency list, not claims that other targets do not use the nodes.
No unit statement or realized unit step is bypassed (`sk-prop-sf-cbc` has empty
realized statement and steps lists).

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The proof plan was valid but
more general than necessary: scheme-level coproduct identification and universal
homeomorphism of arbitrary scheme reductions can be replaced by their already
proved prime-spectrum ingredients. No definitions, statements, other modules,
or public visibility were changed.

## Second reading by E2

1. Compared the delivered module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only the
   proof, its docstring, and the proof-only import were changed. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked the theorem's axioms. It
   compiles without warnings, contains no `sorry`, forbidden declarations, or
   hollow definitions, and `#print axioms` gives only `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Reviewed the direct construction and searched the library and Mathlib
   ingredients. The theorem is not duplicated; the homeomorphisms, open images,
   surjective closed immersions, and structural-map equality are all used with
   their stated hypotheses. Verdict: pass.
4. Checked the proof from the target downward. The reduction and finite-product
   dependencies are replaced by the shorter Mathlib prime-spectrum route; the
   removed import and proof dependencies are recorded above, and no old
   dependency remains unused. Verdict: pass.
5. Compared the updated DAG proof and dependencies with the Lean proof. The
   three elementary steps describe the quotient homeomorphism, partition, and
   lifted closed immersion exactly, and the unit route is preserved. Verdict:
   pass.

Changed the report only by recording this second reading; no further Lean repair
was needed.
