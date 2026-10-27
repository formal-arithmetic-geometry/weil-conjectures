# Worker report: lem-trf-injective-resolution-final-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-injective-resolution-final-kernel.json`: completed split, unchanged statement and statement dependencies; six current, genuinely executed Mathlib searches appended to the inherited records.
- `citations.json`: four verbatim excerpts, one for each node cited in each proof step.
- `report.md`: this report. `searches.jsonl` is the search command's own unmodified log.

No new nodes and no new Mathlib leaves. The proof reuses four existing nodes, all Mathlib leaves. The sandbox was empty of item/report artifacts at start; there was no interrupted delivery process to repeat. All writes are in this sandbox; no git commands, Lean edits, compiler, Lake or build commands were run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, final-kernel variants, Baer criteria and dimension shifting. No project declaration states this complete assertion. Mathlib declarations are used through existing DAG leaves and are not reported as project attachments.

## WANTED

None: all source passages used are present in the read clone.

## Findings and changes

The imported item is mathematically correct, including degree zero. Its proof was empty. I kept its full statement, its statement dependencies, source, provenance and precise blueprint ancestry. The current latest blueprint's `lem-trf-local-term-locality` statement and proof were read, as were the chapter, unit and the parent's regular-local assembly: this is a generic algebraic input in the inherited branch, and no geometric route or unit realization is replaced.

Stacks `more-algebra.tex`, Tag 0A5T (`lemma-injective-amplitude`), proof of (3) implies (1), proves the final kernel injective via Ext and Tag 0AVF. Instead of hiding dimension shifting, this split writes an explicit ideal-map correction. For a map f:T→J, extend its composite into the injective I^d to a:R→I^d. The differential descends to a cocycle α:R/T→I^(d+1). Ext vanishing and the existing resolution-computation node give b:R/T→I^d with ∂b=α. Then a−bq takes values in J and extends f; Baer's existing criterion finishes. This is a complete proof of the item, not a restatement in a new lemma. The expansion is marked `proof_origin.by = agent`, since Stacks' displayed proof uses a triangle rather than this explicit correction.

The elementary quotient descent is written as the well-defined formula α(r+T)=∂a(r), with the cocycle equation checked on representatives. The kernel factorization is written as the value h(r) with its zero-differential proof. These are short module calculations, not additional nodes. None of the five steps exceeds 2000 characters; the entire proof text is 1946 characters.

The genuine current searches used LeanFinder with two distinct phrasings, Loogle, LeanSearch, and both broad and targeted grep through msearch.py. I read every returned candidate. `InjectiveResolution.injective` and `instInjectiveXIntCochainComplex` give injectivity of terms, not kernels; `HasInjectiveDimensionLT.mk` and its variants require all source modules and define an Ext bound, rather than prove this kernel criterion. The second semantic query found `injective_iff_subsingleton_ext_one`, which still requires all test objects and Ext^1 into J. None is an exact or one-line specialization of this item. The applicable `InjectiveResolution.extMk_eq_zero_iff` at Mathlib/CategoryTheory/Abelian/Injective/Ext.lean:193 and `Module.Baer.iff_injective` at Mathlib/Algebra/Module/Injective.lean:412 were read in source and are already covered by the cited DAG nodes.

## Not duplicates

No new node was created. DAG and whole-blueprint searches for injective resolutions, Baer, final kernel and cosyzygy found the existing definitions and tool lemmas that are reused. Blueprint search found no node stating the final-kernel assertion in another form, so `blueprint.same_as` remains an empty list. The parent's use of this very item is an application, not a dependency that may be cited back.

## Review by Q153

I read the whole B–E checklist in `coord/delivery-errors.md`, including its repeated new-target copy, against the proposed files. There is no new statement-only node to audit, no restated clause promoted to a child, and no unsearched new fact. TeX remains singly escaped in the mathematical strings; inherited source and maintainer fields are preserved. The statement introduces R, N, the exact nonnegative resolution, d, J and every ideal test; I found no missing hypothesis and made no statement correction.

For the item's source I read Stacks 0A5T (`lemma-injective-amplitude`) through the final-kernel conclusion, and 0AVF (`lemma-characterize-injective-bis`), both the equivalence and its ideal-extension proof. I also read `derived.tex`, Tag 06XR (`lemma-compute-ext-resolutions`), (1), which computes Ext against the given injective resolution. The tag-to-label mapping was checked in `literature/stacks-project/tags/tags`. These sources support precisely the resolution computation and Baer test used here. No SGA source is used.

Step 1 cites `lem-weil-pbc-ring-modules-enough-injectives` for its explicit statement that Mod(R) is abelian and monomorphisms are injective maps, and `def-sp-injective-resolutions` for its explicit Hom-surjectivity definition of an injective object. I opened both statements: the ideal inclusion T→R is injective, the target I^d is injective by the item's hypothesis, and the composite of f with the kernel inclusion is a map of modules, so a genuinely exists. The category theorem is a generic off-unit tool, recorded in split_report.tool_uses, not a replacement for a step of this unit.

Step 2 is elementary: changing a representative r by t∈T changes ∂a(r) by ∂ιf(t)=0, and ∂²=0 gives the cocycle identity. These formulas establish linearity and well-definedness rather than merely saying that the map descends. It uses only the data and equations of the preceding step and the given complex.

Step 3 cites `lem-weil-pbc-ext-via-injective-resolution`. I read its entire statement: it specifies the same kind of integer-indexed nonnegative, augmented exact injective resolution and explicitly identifies H^i(Hom(M,I)) with cocycles modulo the images ∂g. With M=R/T and i=d+1, the vanishing hypothesis therefore says exactly that α is ∂b for some b:R/T→I^d. Since d≥0, i>0 and there is no degree-zero denominator exception. The existing leaf even packages this as `extMk_eq_zero_iff`; I read that source at line 193, including its predecessor-degree condition. No existence of a bounded injective model or injectivity of J is assumed here.

Step 4 is the elementary check ∂(a−bq)=0 and (a−bq)|_T=ιf. Taking the same value in the submodule J gives a linear map, and the inclusion is injective, so equality after inclusion really gives the claimed extension. There is no unproved transport, comparison or concealed lemma. Step 5 cites `lem-sf-baer-criterion`: its statement is exactly the equivalence between extension from every ideal and injectivity, for a commutative ring and a module in the same universe. All those hypotheses hold for the original R and the submodule J. I read the full criterion and checked that it does not demand Noetherianity, finite generation or a local ring.

I checked d=0 separately: α has degree 1 and its boundary b has degree 0, so the identical proof works, with no negative-degree term. Exactness also identifies J with N here, consistently with Baer's Ext^1 test. For T=0 the descent has q=identity and the corrected extension can be zero; for T=R, R/T=0 and a already takes values in J. For N=0 the computation still applies to any given exact injective resolution. For the zero ring every unital module is zero and all the equations and the conclusion hold. None of these tests needs any added hypothesis.

I verified the four citations.json excerpts against the current cited statements, including the explicit cocycle/boundary quotient, rather than quoting a weaker definition or a proof. All proof dependencies are exactly the union of step uses, and none points to the parent or another node depending on this item. There is no new-node same-tag pair needing a distinction. This self-review corrected the potential hidden dimension-shifting gap by writing the cocycle and its correction explicitly. No work remains mathematically unfinished in this split.

## Unfinished work

None. The required server dry run and push follow this report; their final result is reported by the delivery command.
