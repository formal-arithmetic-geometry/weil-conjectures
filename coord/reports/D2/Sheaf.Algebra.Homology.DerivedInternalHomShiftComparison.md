## What changed

Replaced the sorry in `CategoryTheory.derivedInternalHom_shift_comparison` by a
complete Lean composition of natural isomorphisms, implemented by the fully proved
private generic helper `shiftComparisonOfOneVariable`. The original elaborated signature and
public imports are unchanged; only explicit category/universe annotations were
added to the signature text to avoid slow inference. Added proof-only imports of
`Sheaf.Algebra.Homology.DerivedInternalHomShiftLeft` and
`Sheaf.Algebra.Homology.DerivedInternalHomShiftRight`.

The left comparison treats m with n=0; the right comparison treats n with m=0.
They are independent, strictly simpler one-variable steps, rather than a renamed
simultaneous comparison. The upper proof uses shift addition and whiskering to
combine them, then extracts naturality by `NatTrans.naturality`. Classical choices
occur only within the theorem proof; no definition or object is introduced by
choosing arbitrary data from an unproved existence theorem.

Read the parent's DAG plan and all four dependencies, the HomComplex construction,
DerivedInternalHom representative comparisons, QuasiIsoHomComplexMap, and the
source-library K-injective resolution API. Searches with LeanFinder, Loogle, and
ripgrep found no one-variable internal sheaf Hom comparison. LeanSearch returned
Internal Server Error. The ordinary Mathlib HomComplex shift API concerns groups
of morphisms, and does not directly compare these sheaf-valued complexes.

## Proved and sorry left

Closed the original hole in `CategoryTheory.derivedInternalHom_shift_comparison`
(node `lem-pur-derived-internal-hom-shift-comparison`) by decomposition.
No sorry remains in the item's module.

Added exactly two holes:

- `CategoryTheory.derivedInternalHom_shift_left`, node
  `lem-pur-derived-internal-hom-shift-left`.
- `CategoryTheory.derivedInternalHom_shift_right`, node
  `lem-pur-derived-internal-hom-shift-right`.

Both new declarations have exactly `:= by sorry`, with complete signed
representative arguments in their docstrings and nodes. This is a decomposition,
not a complete proof without lower holes: one hole closed, two holes added.
The two one-variable modules and the composed original theorem compile locally.
An initial dry run hit the 60-second limit when checking the composition directly
against the concrete derived-Hom definition; the categorical composition was then
factored into the generic private helper within the same file to avoid expensive
unfolding of that definition during composition elaboration. Diagnostics then
localized the remaining cost to statement elaboration: explicit category and
universe arguments brought compilation to 10.8 seconds. No experimental options
or local attributes remain. The final set compile passed (3.1 seconds for the
main module after the annotations). A separate temporary module repeated the
original unannotated statement verbatim and proved it by applying the delivered
theorem; it compiled successfully, checking compatibility with the original type.
The temporary verification module was removed before delivery.

## No longer needed

No original import is removed; no module is pruned globally. The following old
parent proof dependencies are no longer directly used by the parent's proof:
`def-pur-derived-internal-hom`, `def-pur-hom-complex`,
`lem-pur-rhom-well-defined`, `prop-pur-kinjective-resolutions-exist`.
They remain needed in the two one-variable nodes' proof plans, so are retained
transitively. The parent now directly depends on the two one-variable comparisons.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the original statement. The current HomComplex
public interface supplies its product/differential data through an existence
specification but no public shift comparison. The representative comparisons alone
do not imply the shift theorem without the signed chain comparison. Naturality
must be included in each one-variable comparison; it would be false for an
arbitrary independently chosen objectwise isomorphism family.

The unit `sk-thm-picard-duality` has empty `realized` lists; this change is below
its unit route and retains the parent's full statement and intended signed route.
Edge cases checked in the chain formulas: m=0, n=0, negative shifts, zero complexes,
and unbounded products. No K-flatness is needed.

The local clone lacks literature/stacks-project/sites-cohomology.tex. Read the
Stacks online sections at https://stacks.math.columbia.edu/tag/0A8X and
https://stacks.math.columbia.edu/tag/08JA instead. The new signed calculation is
an agent-written consequence of the Hom differential and representative
construction, rather than a quotation of a shift lemma at Tag 08JA.

## New nodes

`lem-pur-derived-internal-hom-shift-left` states the natural source-shift comparison
RHom(P,-)[-m] ≅ RHom(P[m],-). Its proof reindexes product components with sign
(-1)^(m*k), then descends through localization and representative comparison.
Module: `Sheaf.Algebra.Homology.DerivedInternalHomShiftLeft`.

`lem-pur-derived-internal-hom-shift-right` states the natural target-shift comparison
RHom(P,-)[n] ≅ RHom(P,-[n]). Its proof uses shift stability of K-injectivity and the
identity comparison on the Hom product factors, then descends through localization.
Module: `Sheaf.Algebra.Homology.DerivedInternalHomShiftRight`.

The annotation-only textual signature change is recorded in
`coord/changes/DerivedInternalHomShiftExplicitArguments.md`, including all
transitive users. There is no semantic interface change or forced adaptation.

## Second reading by D2

1. Compared all three delivered modules with the repository. Only the comparison
module existed. Its one existing theorem has identical hypotheses and conclusion;
the explicit `forget₂` and `derivedInternalHom` universe/category arguments are
inference annotations, declared in the change record. No definition or target
statement changed. The generic helper is private, fully proved, and introduces no
public interface. All public imports are needed by signatures; the two added
imports are proof-only.

2. Read the generic helper's three composed natural isomorphisms: shift addition,
right comparison whiskered by shift(-m), then left comparison whiskered by shift(n).
Their components have exactly the displayed endpoints; naturality is the required
square, with the curried functor map definitionally equal to the bifunctor map.
There are no forbidden declarations or data definitions. The only new sorries
are the two named, documented theorems listed above. Local compilation and axiom
probes are recorded below; `sorryAx` remains through these lower comparisons.
This is one hole closed and two added, a decomposition rather than net closure.

3. Checked both lower statements against HomComplex's product/differential and
DerivedInternalHom's localization and representative-comparison APIs. Read Stacks
Tags 0A8X (Hom-complex differential and quasi-isomorphism invariance) and 08JA
(representative computation). For the left comparison the adjacent-degree sign
ratio is (-1)^m, exactly compensating the source shift; for the right comparison
both postcomposition terms have sign (-1)^n and both precomposition terms have
sign -(-1)^k. Tested m,n=0, odd shifts, negative shifts, zero arguments, and
unbounded products. No boundedness or K-flatness is needed. Naturality is part
of each statement, so arbitrary unrelated objectwise choices are not used.
Each lower statement restricts to one shift variable and is strictly a part of
the simultaneous argument, not a renamed copy. Fresh LeanFinder search for
translation/suspension and Loogle search for `homComplexFunctor`, plus ripgrep
in both source roots, found no existing internal sheaf Hom shift comparison;
the generic derived-functor shift APIs do not supply the missing signed chain
comparison. Each lower theorem has a full representative proof docstring and node.
Closing either lower hole requires the chain comparison and localization argument,
not a short application of an existing theorem found in these searches.

4. All imports are used: DerivedInternalHom in the public statements and the two
one-variable modules in the proof. Listed all four retired direct proof dependencies
under No longer needed and distinguished their continued transitive use.
The unit sk-thm-picard-duality has realized.statement=[] and realized.steps=[[]];
no realized node or unit route is bypassed. The upper proof takes the direct
categorical route from the smaller comparisons, without extra intermediate holes.

5. Read all three node records. The parent's proof/proof_deps/proof_origin match
the categorical composition, and both new records have the correct chapter/unit,
source, creation record, blueprint ancestry, Lean declaration/signature, searches,
and proof-dependency union. Updated each new node's verbatim Lean statement after
adding explicit inference arguments. The statements in words remain unchanged.

Changes made: made universe/category arguments explicit in both new comparison
statements consistently with the parent, wrapped the right comparison at 100 columns,
updated their node signature records, and completed the direct-dependency pruning
report. No proof or mathematical statement was rewritten.

The initial right-module wall-clock timing included waiting for a shared compiler
slot; it does not establish a 60-second compiler timeout or a slow definition.

Validation: deliver3.py --no-push passed: all three modules compiled cleanly,
the delivery axiom probes passed, and preflight returned OK (CODEX).

The separate scratch-copy #print axioms checks compiled successfully and printed
exactly [propext, sorryAx, Classical.choice, Quot.sound] for the parent and both
lower comparisons. No axiom beyond the allowed three and the reported holes occurs.
