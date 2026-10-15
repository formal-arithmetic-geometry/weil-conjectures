## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_closed_abelian_filteredColimits` in
`lean/Sheaf/AlgebraicGeometry/ProEtaleClosedAbelianFilteredColimits.lean` without changing
its signature or public imports. Added two completely proved private helpers:
`globalSections_preserves_filteredColimits` converts the existing section-calculus
bijection into categorical preservation, and `evaluation_preserves_filteredColimits`
identifies evaluation at a qcqs object with localization followed by global sections.

Localization uses the already proved source instances `ProEt.isContinuous_overMap`
and `ProEt.isCocontinuous_overMap` and Mathlib's
`Functor.sheafAdjunctionCocontinuous`. No object is chosen from an existence theorem.
The identity-on-scheme isomorphism identifies its terminal evaluation with the original
object, and naturality is checked explicitly. Restriction to the affine pro-etale site,
followed by presheaf inclusion, preserves and reflects the relevant colimits. The direct
image followed by this restriction preserves them because the closed fibre of every
affine basis object is affine. Reflection finishes the theorem.

Updated the existing node's proof, proof dependencies, and proof origin to describe
this argument. No definitions, existing statements, or other modules changed.
The final single-file launcher compile passed without warnings in 2.0 seconds against
the published server build. The delivery tool also compiles with its axiom probe;
the final dry run checks the complete delivery and leaves the independent reading
for the second worker.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.proEtale_closed_abelian_filteredColimits`
(node `lem-weil-pbc-proetale-closed-abelian-filtered-colimits`).
There are no `sorry`s in the delivered module and no holes added elsewhere.
This is a proof from existing DAG statements, with zero new split-offs, rather than
a decomposition. Its existing dependency
`AlgebraicGeometry.proetale_qcqs_fp_section_calculus`
(node `lem-weil-pbc-proetale-qcqs-fp-section-calculus`) still has its library `sorry`;
this delivery uses its first, abelian-sections clause as intended by stage 3.
The two private helpers are fully proved.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
Its node `lem-weil-proetale-weakly-etale-localization` is no longer needed by this
item's proof: the already proved source composition-functor continuity/cocontinuity
instances give the required localization adjunction directly. In particular the large
existential equivalence, constant-ring normalization, and module-equivalence clauses
of that theorem are unused here. Its module may still be needed by other parents.

All other original imports remain: the inverse-image module supplies the statement's
functor, ClosedImmersion supplies closed base change and affine-source geometry,
Filtered supplies the statement's filtered-colimit vocabulary, the section-calculus
module supplies global-section continuity, and the source affine-comparison module
supplies affine-basis restriction and detection. Added the proof-only Mathlib import
`Mathlib.CategoryTheory.Sites.CoverLifting` for the cocontinuous sheaf adjunction.
No other planned node or module was bypassed. The proper-base-change unit's realized
statement and steps remain on their existing route.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The plan did not need a new
geometric comparison lemma: the source localization instances and general categorical
reflection APIs already supply its glue. Ambient qcqs hypotheses are unused because
only the affine test objects and their closed fibres need to be qcqs; the original
statement and all hypotheses have nevertheless been kept exactly.

Searches used the prescribed leanfinder, loogle, and grep interfaces, then direct `rg`
and source reading. LeanFinder returned generic coherent-sheaf/AB5 results rather than
the required direct-image assertion; Loogle did not recognize the unqualified query
identifier; grep found no direct pushforward-preservation result. Reading the source
localization instances and affine restriction equivalence yielded the successful route.

The local literature checkout is absent on this machine. Read the original source
online: [Tag 0738](https://stacks.math.columbia.edu/tag/0738), clause (4), and
[Tag 098D](https://stacks.math.columbia.edu/tag/098D). These confirm the finite-cover
section-continuity route already carried by the existing section-calculus dependency.

## Second reading by H4

1. **Interfaces and accidental changes.** I diffed the delivered module against the
repository version. The existing theorem signature and all existing declaration
signatures are unchanged byte for byte. The only source changes are the proof,
one proof-only `Mathlib.CategoryTheory.Sites.CoverLifting` import, and removal of
the unused proof-only localization import. The changed DAG node records the new
proof route and dependencies; no target statement or definition changed. Verdict:
pass.

2. **Proof and trust basis.** The module compiles with
`python3 /home/ubuntu/weil-launcher/lcompile.py` and contains no `sorry`, `axiom`,
`unsafe`, `opaque`, `implemented_by`, or `extern`. The theorem's axiom probe reports
only the permitted foundational axioms plus `sorryAx` inherited from the explicitly
imported section-calculus theorem that remains open. Both private helper theorems
are fully proved. Verdict: pass.

3. **Statements and split-offs.** There are no new public or DAG split-off
statements. The two private helpers are true, strictly smaller reductions: the
first packages the existing bijection as preservation of abelian global sections,
and the second transports that result to evaluation at a qcqs pro-etale object via
the explicit localization functor and a natural isomorphism. No helper merely
renames the target, and no existing library declaration duplicates either result.
Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing qcqs section
calculus, source continuity/cocontinuity instances, affine-site comparison, and
generic pointwise colimit/reflection lemmas. I checked that the removed
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` import and its node are
not referenced by the proof; all remaining imports and `proof_deps` are used.
The proper-base-change unit route and its realized nodes remain intact. Verdict:
pass.

5. **DAG agreement.** The node's four proof steps follow the helper definitions
and the final affine-basis reflection argument in the Lean source. Its
`proof_deps` and `proof_origin` describe the actual imports and route, and no new
node or change record is needed. Verdict: pass.

I changed only this report section after the first reading: no Lean source or DAG
repair was necessary.
