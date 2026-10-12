## What changed

Replaced the original sorry in `coherent_property_integral_ideals_of_small_support` with
an exact-sequence argument. The new module `Sheaf.AlgebraicGeometry.CoherentIdealPatchingExactSequence`
isolates the geometric generic-point patching construction, including the ideal-intersection and
zero-ideal cases. It assumes none of extension closure, positive-sum descent, or the small-support
property hypothesis. The target applies those hypotheses explicitly.

The four auxiliary arguments (finite type transport, coherence transport, coherence of zero,
and property invariance under coherent isomorphism) are local facts inside the target proof. This
avoids publishing declarations whose statements duplicate the private helpers in
`CoherentPropertyDevissageIntegralSubschemes`, which the landing checker rejects.

Both modules compile together with lcompile.py --all. The target signature is unchanged.
The geometric statement was checked against Stacks 01YL online; combining the intersection
inclusion with the positive sum gives a single small-support quotient, before applying P.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.coherent_property_integral_ideals_of_small_support`; its four
auxiliary facts are local proof terms rather than declarations.
Added one hole in
`AlgebraicGeometry.Scheme.Modules.coherent_ideal_patching_exact_sequence`
(node `lem-weil-pbc-coherent-ideal-patching-exact-sequence`). This is a decomposition:
one hole closed, one strictly geometric hole added, net zero. No sorry occurs in any private helper
or definition. The remaining geometric theorem has a complete natural-language construction in
its declaration docstring and DAG proof steps.

## No longer needed

Removed these direct proof imports from the target module; their geometric work remains below
the new node, so they are not pruned from the targets' closure:
- Sheaf.Algebra.Homology.ModuleStalkExact
- Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
- Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion
- Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
- Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
- Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
- Sheaf.Paper.SchemeTheoreticSupport

No original geometric DAG dependency is pruned. The two coherence modules remain direct proof
imports for the proved isomorphism-invariance helpers. All original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original plan was found. The final ideal-intersection step can be
combined with the inclusion of the patched submodule before invoking the property P: this yields
a single geometric exact-sequence statement. It preserves the unit route. The early sandbox
nonzero-case restatement and bottom-object equality attempts were discarded; neither is delivered.
Accidental temporary repository edits were restored before preparing the delivery.

## New nodes

`lem-weil-pbc-coherent-ideal-patching-exact-sequence`:
`lean/Sheaf/AlgebraicGeometry/CoherentIdealPatchingExactSequence.lean`, declaration
`AlgebraicGeometry.Scheme.Modules.coherent_ideal_patching_exact_sequence`. Its conclusion is a
positive-sum short exact sequence with coherent terms, a first term isomorphic to a coherent
module having P, and a quotient supported in i(Z) with vanishing generic stalk. The zero case
uses P(0); the nonzero case is the generic inclusion, annihilator patching and ideal intersection
of Stacks 01YL. There are no interface changes or forced adaptations and no change record.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. The theorem signature and all
existing declaration interfaces are unchanged; only proof text and proof-only imports changed.
Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The target has no remaining `sorry`;
the only remaining hole is the named split theorem
`coherent_ideal_patching_exact_sequence`, and no forbidden declarations or hollow definitions occur.
Verdict: pass.
3. Read the split theorem and its DAG node. Its statement is a genuine geometric reduction,
strictly simpler than the target, with a complete source-based docstring and matching node metadata.
No duplicate declaration was found in the library. Verdict: pass.
4. Checked the proof route against the unit route and the imported dependency declarations. The target
uses the patching theorem, extension closure, finite-sum descent, and small-support hypothesis in the
stated order; removed imports are recorded above. Verdict: pass.
5. Checked the DAG proof, proof dependencies, proof origin, and realized unit route against the Lean
proof. The new node is marked split and all dependencies used by its statement are recorded.
Verdict: pass.

Changed only this report section; no code repair was needed after review.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository versions. Existing declaration signatures,
definitions, and target hypotheses are unchanged; the target only removes proof-only imports and
replaces its proof. Verdict: pass.
2. Compiled all sandbox modules with `lcompile.py --all`. Compilation is clean; the only remaining
`sorry` is the named split theorem, and no forbidden declarations or hollow definitions occur.
Verdict: pass.
3. Read the split theorem and node. Its geometric exact-sequence conclusion is strictly smaller
than the target, its docstring gives the construction and source, and the node metadata matches the
Lean declaration. Verdict: pass.
4. Checked the proof route and imports. The target invokes the patching theorem, derives coherent
isomorphism invariance from extension closure, then uses small-support and positive-sum descent;
removed imports are no longer referenced by the target. Verdict: pass.
5. Checked DAG proof, proof dependencies, proof origin, and the realized unit route against the
Lean code. The split node remains on the planned geometric route. Verdict: pass.

I changed no code during this second reading; only this report section was appended.

## Second reading by V1

1. Compared the target module with the repository version. The target theorem signature and all
existing declarations are byte-for-byte unchanged; only proof text and proof-only imports changed.
Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. Compilation is clean; the only
remaining `sorry` is the named split theorem, and no forbidden declarations or hollow definitions
occur. Verdict: pass.
3. Read the split theorem and its DAG node. The conclusion is a strictly smaller geometric
short-exact-sequence reduction, with a source-based docstring, and its node metadata matches the
Lean declaration. No duplicate declaration was found in the library. Verdict: pass.
4. Checked the proof route and imports. The target uses the patching theorem, derives coherent
isomorphism invariance from extension closure, then applies small-support and positive-sum descent;
the removed imports are no longer referenced directly. Verdict: pass.
5. Checked the DAG proof, proof dependencies, proof origin, and realized unit route against the
Lean proof. The split node remains on the planned geometric route. Verdict: pass.

Changed only this report section during second reading; no code repair was needed.
