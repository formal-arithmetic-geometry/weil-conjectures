## What changed

Proved `AlgebraicGeometry.zeroDimensional_baseChange_fibre_points` without changing
its signature or existing docstrings. Added proof-only imports of
`Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry`.
The proof uses the already proved geometry theorem to obtain residue-field
isomorphisms. Mathlib's residue-field pullback square then makes each tensor
spectrum a singleton. Its pullback point correspondence gives existence and
uniqueness. Updated `new-zdbp-fibres-point` to match this proof.

Local compilation succeeds without warnings. No new declarations or modules.
The argument covers the empty scheme vacuously and arbitrary field extensions,
including the identity extension and extensions which are not algebraically closed.

Searches: LeanFinder for pullback projection bijectivity with residue-field
isomorphisms found the PullbackCarrier correspondence and tensor pullback square;
Loogle for `CategoryTheory.Limits.pushout.inr` and grep for `isIso_inr` found
categorical pushout isomorphism ingredients. Repository searches found no direct
proof of the item and found the already proved geometry theorem. The existing
Mathlib pullback-square interface suffices without adding a tensor-ring lemma.

## Proved and sorry left

Proved `AlgebraicGeometry.zeroDimensional_baseChange_fibre_points`
(node `new-zdbp-fibres-point`): one of one original sorries removed.
No sorry remains in the delivered module; no sorry is added elsewhere.

## No longer needed

No existing import was removed. The direct dependency
`lem-weil-pbc-closed-point-residue-field-base` is removed from this node's
`proof_deps`: its conclusion is already supplied by `new-zdbp-geometry`.
It remains needed transitively by the geometry proof, so this is not a claim
that its Mathlib module can be pruned from the target closure.
No other planned node or module is pruned. No separate residue-field identification
or tensor-ring isomorphism module is needed.

## Where the brief, the DAG or earlier work was wrong

No statement or mathematical error found. The planned explicit use of
`residueFieldIsoBase` in this module was redundant once the geometry theorem
supplied `IsIso` of the residue-field map. The unit's route is unchanged.

## Second reading by J1

1. Compared the delivered module with the repository version: the theorem signature and existing declarations are unchanged; only proof-only imports and the proof body differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; no errors or warnings, and no `sorry` remains in the module. The remaining `sorryAx` in the scratch axiom print is transitive from the imported open geometry theorem. Verdict: pass.
3. Checked the split node against the Lean declaration and searched the repository for duplicate statements. The node is a strictly smaller intermediate result, mathematically true, and has the required source and proof description. Verdict: pass.
4. Checked the proof route from the target downward and the imports. The geometry unit step is retained; the two added imports are proof-only and no unnecessary existing import was removed. Verdict: pass.
5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the actual proof. They agree, including the removal of the redundant closed-point residue-field dependency. Verdict: pass.

No code or DAG changes were needed during this second reading; only this review section was added to the report.
