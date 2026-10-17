## What changed

Completed `AlgebraicGeometry.ProEtale.comparison_basis_isIso` in
`Sheaf.Paper.IntegralScalarContractive`, preserving every existing declaration signature.
The continuous comparison now has a complete proof on the weakly contractible affine basis.

Constructed private, proved, normalized affine-map correspondences using the current
`LocallyConstant.liftPrimeSpectrum` API. Their inverse laws follow from localization at
all primes and characteristic idempotents of clopen fibres. The actual connected-component
quotient is bundled by `pointLanComponents`; the existing proved `kanTerminal` supplies the
terminal Kan-index object. Continuous functions into a totally disconnected ring factor
through the quotient, making the Kan comparison bijective. The existing sheafification
section theorem and left-adjoint uniqueness then prove the original basis comparison.

The only proof imports are now `import all` of
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` and
`Sheaf.Paper.PointLanAffineEvaluation`. The latter gives the proved generic terminal-object
lemma; the former supplies the existing projection, naturality, relative-map and detection
helpers. Simplified the earlier norm nonzero normalization to `simp` to remove its linter
warning. Updated the item's DAG proof, dependencies and proof origin.

Validation: the complete file compiles without errors or warnings. Empty sources, empty
profinite targets and the zero ring are covered by the same inverse-law proof; it requires
neither nonemptiness nor nontriviality. No statement or definition in another module changes.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.ProEtale.comparison_basis_isIso`
(node `lem-weil-pbc-integral-scalar-contractive`). Proved 1 of 1 original sorries; added 0
holes and split off 0 statements. There are no `sorry`s left in any delivered Lean file.
The public `AlgebraicGeometry.ProEtale.CondensedRing.integralRegular_one_sub_nsmul_isIso`
now uses this completed comparison proof.

The proof still uses the library's existing point-component topology and weakly contractible
sheafification results. Their proofs are separate work items; no claim is made here that
all transitive axioms of the target have been discharged.

## No longer needed

Removed the obsolete direct proof dependency
`lem-weil-pbc-condensed-lfp-local-triviality`, whose local-freeness assertions are unused.
The comparison support actually used lives in
`Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`.

Removed redundant original direct imports:
- `WeilConjectures.CategoryTheory.Sites.MonObj`;
- `Sheaf.Paper.ProEtaleSheafificationWcontractibleSections`;
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`;
- `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`.

All declarations and instances needed from these modules remain available through the
retained comparison-support import. In particular the sheafification and covering nodes
remain genuine dependencies, not pruned work. The newly tested direct
`import all Sheaf.Paper.ProEtalePointComponentsMaps` was also redundant and omitted.
No entire imported module is claimed to leave the targets' closure.

The removed upstream `profiniteLocallyConstantHomEquiv`, `specMapEquiv_apply`,
`pointComponentsEquiv_apply`, `canonicalComponentArrow` and
`canonicalComponentArrow_terminal` are not used. Their obsolete commented-out Kan proof
was removed from this item; the replacement is proved with the current API.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt only fixed a linter-level norm proof and retained the item's
sole hole, so it did not satisfy stage 3. The worktree-capacity failure no longer occurs;
the first dry run instead correctly rejected that unchanged hole.

The node's earlier assertion that the comparison helpers were all already proved was stale
after the upstream sync. In particular the old `Profinite.of` expression implicitly required
component-space instances no longer supplied by the source. The replacement uses the
explicit profinite structure from `pointLanComponents` under the actual weak-contractibility
hypothesis and proves the normalized affine correspondence from the current spectrum API.

The dependency modules are currently held by B3 (`ProEtalePointComponentsMaps`) and D2
(`CondensedFieldContinuousRealization`), so they were left unchanged. This delivery's private
helpers repair the integral comparison only; there are no forced adaptations or new nodes.


## Second reading by K1

1. Compared the delivered Lean module with the shared repository using `diff`. The target
`AlgebraicGeometry.ProEtale.CondensedRing.integralRegular_one_sub_nsmul_isIso` and every
pre-existing declaration retain the same signatures; the delivery adds only private proof
helpers and changes proof imports. No target, definition, or interface in another module was
changed. Verdict: pass.

2. Compiled the delivered module with `lcompile.py` successfully and checked the target with
`#print axioms`; its transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`,
and the `sorryAx`s already present in imported open work. Searched the delivered Lean and DAG
files for direct `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and
`debug.skipKernelTC`: none occur. There are no new split-off statements or holes. Verdict:
pass.

3. Read the new affine correspondence and the Kan comparison proof top-down. The explicit
`liftPrimeSpectrum` correspondence has both inverse laws, uses localization at every prime,
and does not choose data from an undetermined existence theorem. The component factorization
uses the quotient universal property and works for empty sources, empty profinite targets, and
the zero coefficient ring; no nonemptiness or nontriviality hypothesis is introduced. The
private helpers are reductions strictly below the target and duplicate no existing public
statement. Verdict: pass.

4. Checked the route against the unit record: it retains the affine weakly contractible
sheafification and covering detection route, while using the generic terminal Kan object and
the current affine map API. The retained proof imports are used; the removed direct imports and
the obsolete local-triviality dependency are not needed by the final proof. Verdict: pass.

5. Compared the node's `proof`, `proof_deps`, and `proof_origin` with the final Lean route.
The new locally-constant prime-spectrum, point-components, point-Lan, sheafification, covering,
and continuous-realization dependencies account for the proof, and the removed local-triviality
dependency is absent. The unit and target identifiers remain unchanged. Verdict: pass.

Changed during second reading: no Lean or DAG repairs were necessary; this section is the only
change made.
