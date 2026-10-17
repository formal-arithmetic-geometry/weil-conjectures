## What changed

Repaired both interface objections in the return at b217ecd04. Compared the retained
proposal with the current shared source; the old proposal and its independent reading are
archived in `scratchpad/returned-before-interface-repair` and are not reused as a review
of this revised delivery.

1. `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` has exactly its
   original public imports. The rejected public import of the p-adic specialization is
   gone. Its pre-existing lemma `boundedConstructible_derivedExtendScalars_obj` is now
   proved using private imports of `Sheaf.Paper.ContinuousIntegralScalarExact` and
   `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`. The induced norm identifies
   the actual source integral ring and inclusion definitionally with the continuous ones;
   exactness and the generic preservation theorem finish the proof. This consumer is
   unclaimed. No signature, attribute or definition is changed.
2. `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` retains every
   upstream declaration verbatim, including the disputed
   `isTriangulated_boundedConstructible`. Its proof is still open. The three rejected public
   structural additions are removed from the proposal. All existing proof bodies and
   imports are unchanged. Documentation points to the actual proved conditional theorem
   and marks the false declaration itself as `STATEMENT-DISPUTED`.
3. The fully written coefficient-specific variant
   `isTriangulated_boundedConstructible_padicIntegers` stays entirely in
   `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated`, as requested by the gate.
   Its proof explicitly uses the existing conditional source instance and integral Serre
   closure; it does not claim to prove the arbitrary-ring assertion.

The consumer preservation node now records the shorter exactness/preservation route and
its existing source declaration. Its statement and all maintainer-owned fields are
unchanged. The earlier proposed edit of the already proved conditional triangulation
node is withdrawn; its sandbox copy matches the current repository exactly.
No unit statement or realized step is changed.

Validation: all three delivery modules compile together with `lcompile.py --all`, with
no errors or warnings (2.0, 3.6 and 18.4 seconds). A source-level declaration comparison
finds zero changed signatures, removed or added source declarations, changed attributes,
or changed public imports. The only changed source proof is the existing consumer lemma.
The consumer is currently imported only by the generated aggregate `WeilConjectures`;
its one-hole reduction is not claimed as a reduction in the targets' import closure.
The required `deliver3.py --no-push` dry run passes compilation and all preflight checks
except the second reading, which the next worker must supply. Nothing is pushed.

## Proved and sorry left

Assigned module: **zero of one** original holes proved. The remaining hole is
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible` (the upstream noetherian-only
assertion, recorded by the audit of `sk-def-sfb-bounded-constructible`). It is disputed,
retained unchanged, and neither counted as proved nor silently replaced by a weaker result.

Additional existing consumer hole closed:
`AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_obj`
(`lem-sfb-extend-scalars-bounded-constructible`). Its complete Lean proof compiles from
existing named results. No replacement obligation is introduced.

The consumer's other pre-existing hole remains:
`AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
(`thm-sfb-extend-scalars-localization`). Its statement and proof are unchanged.

The new specialization
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_padicIntegers`
(`lem-weil-pbc-padic-integers-bounded-triangulated`) has a complete proof and zero local holes.
The existing conditional source theorem remains fully proved.

Across the delivered files: three original holes, one closed, two left, zero added,
zero split off. This is partial progress with the original disputed statement still open;
it is not a proof of that statement. Axiom probes show inherited `sorryAx` in both the
specialization and the newly proved consumer lemma, so neither is claimed to be closed
under the project's final axiom criterion. The conditional generic source instance has
only `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

Withdraw the rejected public import of
`Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` from the source consumer.
The new coefficient-specific module remains as the sound variant requested by the return.

Withdraw the proposed source additions
`isClosedUnderIsomorphisms_boundedConstructible`, `containsZero_boundedConstructible`, and
`isStableUnderShift_boundedConstructible`. Their proposed proofs were valid, but these
extra exported declarations are unnecessary when preserving the upstream interface.
The conditional triangulation theorem and its existing node are unchanged.

The newly proved consumer lemma uses the two existing exactness/preservation nodes.
Its former direct proof-dependency edges below are removed; this is pruning of that proof
route, not a claim that the nodes or their modules have become globally unreachable:

- `def-sfb-integers-to-subfield`.
- `det-prop-sfb-qlbar-colimit-x-invert-ell`.
- `lem-sfb-modobj-extension-right-exact`.
- `lem-sfb-extend-scalars-preserves-homology`.
- `sk-def-sfb-derived-extension-of-scalars`.
- `def-sfb-left-derived-exact`.
- `sk-def-sfb-module-pushforward-pullback`.
- `lem-weil-pbc-left-adjoint-preserves-colimits`.
- `def-sfb-modobj-extension`.
- `sk-prop-sfb-cartesian-coefficients`.
- `sk-def-sfb-coefficient-change`.
- `sk-def-sfb-constructible`.
- `det-def-sfb-constructible-local-model`.
- `sk-def-sfb-bounded-constructible`.

No existing Lean module or original public import is pruned. The two new private imports
are both used. The unit's integral-to-rational route and all realized steps stay intact;
no finite-constant-local-model comparison is needed for the current general ring-object
bounded-constructibility predicate.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: a topologically noetherian base does not imply finite presentation of
kernels over an arbitrary coefficient ring. For B = k ⊕ V with V infinite dimensional and
square-zero, multiplication by a nonzero e in V has kernel V; its B-action factors through
k, so it is not finitely generated. The source and target are free of rank one. Constant
discrete coefficient and module sheaves over a geometric point realize this obstruction
to constructible cone cohomology. The base is noetherian.

The returned proposal addressed this by deleting the false instance, but the current
adopted-source gate forbids that interface change. This revision follows the requested
alternative: preserve the upstream declaration and give the valid coefficient-specific
variant in Sheaf. Its existence does not settle the disputed original hole. That limitation
is explicit above; the consumer's preservation proof is independent additional progress.
The maintainer should escalate the retained false upstream signature to the human; the
coefficient-specific theorem is not a resolution of that mathematical dispute.

The old consumer DAG proof expanded finite constant local models unnecessarily. Its
statement uses the current `sk-def-sfb-bounded-constructible`, whose definition explicitly
uses stratified local finite presentation. The existing generic exact-scalar-extension
lemma applies directly to that predicate. The new route does not alter the statement or
identify different notions of constructibility.

The previous report's second reading reviewed a materially different interface-changing
proposal. That review is archived, not presented as a review of these changes. No script,
gate, shared source, lock or target statement was modified. Nothing is pushed.

## New nodes

`lem-weil-pbc-padic-integers-bounded-triangulated` records the proved integral-coefficient
specialization and its two existing dependencies. It introduces no unresolved statement.
Its original search evidence and full natural-language proof are retained. The node for
the source consumer lemma is updated only in `lean`, `proof`, `proof_deps`, and `proof_origin`.
The existing conditional triangulation node is unchanged.

Change record: `coord/changes/C4-preserve-upstream-triangulation-interface.md`.

## Second reading by C4

1. **Interface comparison.** I diffed the delivered source modules against the shared versions. Existing declaration signatures, attributes, definitions, and public imports are unchanged. The target module has only documentation and dispute-marker changes; the rationalization consumer changes one proof and adds private proof imports. The p-adic specialization is a new module and declaration with its own node. Verdict: pass; no forced adaptation is present.

2. **Compilation and proof hygiene.** `lcompile.py --all` compiles all three delivered modules without errors or warnings. The only remaining holes are the retained `isTriangulated_boundedConstructible` declaration in the target module and the pre-existing `isLocalization_boundedConstructibleExtendScalars` declaration in the consumer; both are named in the report and have corresponding DAG records or upstream records. No delivered definition contains `sorry`, and no forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC` declaration was added. Verdict: pass for the delivered proof bodies, with the two explicitly retained open statements.

3. **New statements.** The p-adic specialization is a genuine coefficient-specific consequence of `integralConstructible_serre` and the conditional weak-Serre triangulation theorem; it does not restate the disputed arbitrary-coefficient instance. I searched the repository and ran the independent declaration searches for the same theorem and found no duplicate declaration. The consumer proof closes its existing lemma without introducing a new statement. Verdict: pass.

4. **Pruning and route.** The consumer proof uses exactly the continuous integral scalar exactness theorem and the generic exact-scalar bounded-constructibility theorem; its node records those two dependencies and the report lists the old route dependencies removed. The p-adic proof follows the integral Serre closure route and then the conditional triangulation theorem. The unit route and realized steps are unchanged. Verdict: pass.

5. **DAG/report agreement.** I checked each delivered node's Lean record, proof steps, proof dependencies, source, and declaration against the code. The new p-adic node matches its instance and the consumer node records the revised proof route. The report accurately counts one existing consumer hole closed, two retained holes, and zero new holes or split-off statements. Verdict: pass.

I changed only this second-reading section; no Lean source, DAG node, or change record required repair.
