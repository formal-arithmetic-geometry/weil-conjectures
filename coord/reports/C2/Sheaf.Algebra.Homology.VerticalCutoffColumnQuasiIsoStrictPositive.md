## What changed

The assigned theorem `HomologicalComplex₂.verticalCutoff_column_quasiIso_strict_positive`
now has a compiling reduction to the named kernel calculation, with its statement
and public imports unchanged. It still depends on sorryAx through that calculation.
Its proof imports the new `VerticalCutoffComparisonEpi` and
`VerticalCutoffComparisonKernelTwoTerm` modules and Mathlib's homology sequence.
The DAG records this precise route.

Repair of the landing refusal at head 40ff63f19: removed the three duplicate
private lemmas from VerticalCutoffComparisonEpi. Proof-only `import all` of
LowerTruncationTransitionKernel and UpperTruncationStepSES makes their existing
private declarations accessible without changing their modules or visibility.
The epimorphy proof now calls CochainComplex.pi_f_above and
CochainComplex.truncLEXIsoCycles_naturality directly; the latter already uses
CochainComplex.truncLEXIsoCycles_comp_iCycles. No interface adaptation is needed.

`HomologicalComplex₂.verticalCutoff_comparison_epi` is proved without sorry. It is
stated for any integer cochain complex and endpoints a <= t. Its proof checks
interior components by truncation naturality and boundary components by cycles
and homology. In particular, it treats t = a separately rather than assuming
that upper truncation preserves epimorphisms in general.

The target proof derives epimorphy of q from the specified projection equation.
The proved private `acyclic_twoTerm` lemma derives acyclicity from zero terms
away from adjacent degrees and an invertible differential, including the natural
index boundary m = 0. A genuine short exact sequence and its homology exact
sequence then give monicity and epimorphy of every homology map.

## Proved and sorry left

Closed the one original hole:
`HomologicalComplex₂.verticalCutoff_column_quasiIso_strict_positive`
(node `lem-sp-vertical-cutoff-column-quasiiso-strict-positive`).
No sorry remains in the assigned module or the epimorphy module.

Added one hole:
`HomologicalComplex₂.verticalCutoff_comparison_kernel_twoTerm`
(node `lem-sp-vertical-cutoff-comparison-kernel-two-term`), in
`Sheaf.Algebra.Homology.VerticalCutoffComparisonKernelTwoTerm`.
It asserts only the concrete kernel's two-term support and invertible differential,
not acyclicity or quasi-isomorphism of q. Its full image-and-cokernel argument
is in its docstring and node. The delivery is a decomposition, one hole closed
and one added, with the independent epimorphy calculation fully proved.

All three modules compile without warnings via lcompile.py. The boundary cases
checked in the argument are a = 1, b = a + 1, zero differentials and zero image;
the generic acyclicity proof handles m = 0 using the actual natural complex shape.

## No longer needed

None of the original module's imports is removed, and no module is pruned.
The old direct proof dependencies `def-sp-double-complex-vertical-window` and
`lem-sp-double-complex-vertical-tower-maps` are replaced in the assigned node
by the two new lemma nodes. Both old nodes remain statement dependencies and
transitive proof dependencies through the kernel lemma; neither is obsolete. The original definition modules remain necessary for the
statement and the remaining kernel calculation. The epimorphy module keeps its public Mathlib import and now privately imports
all declarations from LowerTruncationTransitionKernel and UpperTruncationStepSES
for the reused private helpers. Its duplicate HomologicalComplex₂.pi_f_above,
HomologicalComplex₂.truncLEXIsoCycles_comp_iCycles, and
HomologicalComplex₂.truncLEXIsoCycles_naturality are removed entirely.
The complementary-truncation comparison is not imported.
No claim is made that these modules can be pruned from other target routes.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated three private lemmas already in the library.
All three duplicates have been removed and their existing declarations reused.
The epimorphy node now records the two corresponding proof dependencies.
No statement error found. The assigned node's proof dependencies originally
provided the definitions but did not state its degreewise kernel calculation.
This delivery makes that concrete step a separately named statement and proves
the epimorphy and homology-sequence steps. It follows the assigned route.
The inherited unit record has empty `realized` lists, so this refinement does
not bypass any realized unit statement or proof step.

The local literature copies of the Stacks truncation section and the original
blueprint document were absent. The cited Stacks Tag 0118 was read directly at
https://stacks.math.columbia.edu/tag/0118, cochain canonical truncations (3) and
(4); the homology sequence is Tag 0111. The kernel calculation remains the
agent-written specialization already recorded by the assigned node.
LeanSearch returned an internal server error, recorded as unavailable. Loogle,
LeanFinder and grep were run; no exact kernel theorem was found. The blueprint
searches for cutoff comparison kernels and for truncation did not reveal an
existing statement of either new result.

## New nodes

`lem-sp-vertical-cutoff-comparison-epi` records the fully proved degreewise
surjectivity of an upper-truncated lower projection for compatible endpoints.
Its module is `Sheaf.Algebra.Homology.VerticalCutoffComparisonEpi`.

`lem-sp-vertical-cutoff-comparison-kernel-two-term` records the remaining concrete
support and invertible-differential calculation, a strict part of the existing
argument. Its module is `Sheaf.Algebra.Homology.VerticalCutoffComparisonKernelTwoTerm`.
Both nodes use the assigned chapter and unit and trace to the spectral-sequences
blueprint statement. No interface changes or forced adaptations are included.


## Earlier second reading (a previous round; superseded)

1. Compared the assigned module against the repository with diff and checked
   each node's stored Lean signature against its source. The existing theorem's
   signature, section variables, visibility, docstring, and public import are
   byte for byte unchanged. The additions are proof imports, a private proved
   helper, and two new theorem modules; there are no changed definitions or
   forced adaptations. Verdict: pass.

2. Compiled all three files in import order with lcompile.py: no errors or
   warnings. A scratch copy with explicit #print axioms shows only propext,
   Classical.choice, and Quot.sound for verticalCutoff_comparison_epi and
   acyclic_twoTerm. The assigned theorem and kernel theorem additionally use
   sorryAx, exactly as reported. Searched all delivered Lean for forbidden
   declarations and sorry: the only hole is the named kernel theorem, whose
   proof is exactly by sorry. No data definitions are added. Verdict: a valid
   decomposition, not an unconditional proof of the assigned theorem.

3. Read Stacks Tag 0118, cochain constructions (3) and (4), and Tag 0111,
   together with the actual verticalCutoff and verticalWindow definitions.
   The kernel statement keeps all endpoint and projection hypotheses. At
   a-1 the quotient is the coimage of d, canonically its image I; at a its
   kernel is I, including when b=a+1 and the target is homology of cycles.
   The differential is the coimage-to-image isomorphism. Checked a=1 (degrees
   zero and one), b=a+1, zero differential, zero complex, and a nonzero image
   (the two-term identity complex); each gives the asserted support and
   differential. The new hole isolates this coordinate calculation, while
   epimorphy, acyclicity, and the homology-sequence deduction are proved.
   Its docstring gives the full argument and matches its node. Verdict: true,
   needed, and strictly a part of the original argument.

   Independently searched using msearch.py LeanFinder for cokernels of canonical
   truncation inclusions, Loogle for shortComplexTruncLEX₃ToTruncGE, and grep
   for shortComplexTruncLE and truncation kernels, with additional rg in lean/.
   Read Mathlib AreComplementary and the existing
   RestrictedComplementaryTruncationComparison, UpperTruncationStepQuotient,
   TwoTermCoimageQuasiIso, and RightExactTruncGEIso APIs. The complementary
   comparison gives quasi-isomorphy of a cokernel into a whole complex's lower
   truncation, but no support/differential identification for this restricted
   nested quotient. The successive quotient API treats adjacent integer
   cutoffs and does not directly identify the present kernel. None duplicates
   the split-off statement or closes it in a few minutes.

4. Read the proof from its conclusion downward. ShortExact.exact_kernel plus
   the homology exact sequence supplies the last step; the private helper
   correctly handles natural degree zero without an incoming predecessor.
   The epimorphy proof separates t=a, where cycles need a homology argument,
   from a<t, where the relevant components are invertible. Every proof import
   is used; the public import is needed by the statement. All old proof_deps
   are accounted for under No longer needed. The inherited unit
   sk-prop-av-pqf-finite has empty realized lists and its route is unchanged.
   Verdict: pass; no justified additional pruning found.

5. Opened all three nodes. Their lean.statement fields are verbatim signatures;
   proof_deps equals the union of proof-step uses. The assigned proof records
   precisely epimorphy, the kernel calculation, the two-term acyclicity helper,
   and the homology sequence. New nodes have source, proof_origin marked agent,
   searches, creation record, blueprint ancestry, chapter/unit, and lean record.
   Only proof, proof_deps, and proof_origin changed in the existing node.
   Verdict: pass.

Changes by the second reader: clarified the report's conditional proof status
and accounted explicitly for the two old direct dependencies retained
transitively. No Lean or node repair was needed.

## Second reading by C2

1. Compared the assigned module with the repository using diff, then checked
   the theorem signature byte for byte by extracting the text before `:= by`.
   It is identical, including both endpoint inequalities, g and hg, q and hq.
   Its public import, section variables and declaration docstring are unchanged.
   The two additional modules are new; no existing definition or public
   interface is changed. The existing node differs only in proof, proof_deps
   and proof_origin. Verdict: pass.

2. Independently compiled all three delivered modules in import order with
   lcompile.py: no errors or warnings. Searched their source for sorry and
   forbidden declarations. Only verticalCutoff_comparison_kernel_twoTerm has
   a hole, exactly `by sorry`; there are no added data definitions. Scratch
   #print axioms checks of inclusion_f_isIso, cycles_projection_epi,
   verticalCutoff_comparison_epi and acyclic_twoTerm show only propext,
   Classical.choice and Quot.sound. The kernel theorem and assigned theorem
   additionally use sorryAx. The assigned theorem is therefore a conditional
   reduction, with one original hole closed syntactically and one new hole
   added, not a net proof completion. Verdict: valid decomposition.

3. Read Stacks Tag 0118, cochain truncations (3) and (4), and Tag 0111,
   alongside verticalCutoff, verticalCutoffι and verticalWindow. With
   E=L extended by zero, the cokernel at a-1 is E.X(a-1)/ker(d), hence the
   coimage of d. The kernel at a is image(d); when b=a+1 it is the kernel
   of cycles-to-homology, and otherwise the kernel of the opcycles quotient.
   The induced differential is the coimage-image comparison, invertible in
   an abelian category. Compatibility hg determines the nested inclusion
   by monicity, and hq determines q by the epic cokernel projection. Thus
   the remaining statement is true and strictly isolates the coordinate
   calculation; it does not restate quasi-isomorphy. Checked a=1, b=a+1,
   the zero complex, zero differential, and the two-term identity complex:
   the last gives an identity differential in the kernel, and zero image
   gives the invertible map between zero objects. Its complete docstring
   argument and its node agree.

   Independently searched LeanFinder for the contractible kernel of a
   canonical truncation quotient comparison, Loogle for
   shortComplexTruncLEX₃ToTruncGE, and grep for coimage/image and truncation
   kernels. Also searched upstream WeilConjectures and lean/Sheaf with rg.
   Read Mathlib's AreComplementary comparison and the library's
   RestrictedComplementaryTruncationComparison, UpperTruncationStepQuotient
   and TwoTermCoimageQuasiIso. The complementary comparison has a whole
   complex as the ambient source; the present map also requires identifying
   lower truncation of an upper cutoff with the stated window. The adjacent
   quotient result gives coordinates for b=a+1 only. Neither directly proves
   the general kernel statement, and closing it would require additional
   coordinate transports rather than a brief application. Verdict: no
   duplicate statement or readily closable remaining hole found.

4. Read downward from the homology conclusion. The short exact sequence uses
   the actual kernel of q and the proved epimorphy of q. Its exact homology
   sequence gives monicity and epimorphy in each degree; acyclic_twoTerm
   proves exactness at both surviving degrees and at every zero term,
   including natural degree zero. The epimorphy proof distinguishes a=t
   from a<t, avoiding an unjustified general preservation-of-epis claim for
   upper truncation. Its import all declarations reuse the existing private
   pi_f_above and truncLEXIsoCycles_naturality, with no duplicates. All proof
   imports are used and all public imports are needed by signatures.
   The two old direct proof dependencies remain necessary for the definitions
   and the kernel calculation, as explained under No longer needed; no
   module can be pruned on this route. The inherited unit
   sk-prop-av-pqf-finite has empty realized lists and is unchanged.
   Verdict: route and pruning pass.

5. Opened all three DAG nodes and checked each stored lean.statement occurs
   verbatim in its delivered module. The assigned proof cites precisely the
   epimorphy and kernel statements it applies. The epimorphy node records the
   two modules whose private helpers it reuses. Each proof_deps is the union
   of its proof-step uses. New nodes carry source, agent proof_origin,
   searches, creation record, blueprint ancestry, chapter, unit and complete
   Lean records. Verdict: nodes agree with the implementation.

Changes in this reading: appended this independent review and recorded the
fresh search and axiom evidence. No Lean or node repair was needed. The
previous reading is retained as historical text, not relied on as evidence.
