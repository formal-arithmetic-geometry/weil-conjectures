# Stage-1 delivery: lem-sfb-polynomial-good-locus-localization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-good-locus-localization.json`: existing statement, now split in five steps; not a Mathlib leaf. The statement and statement dependencies are unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each step/node citation.
- `searches.jsonl`: actual Q46 searches recorded by msearch.py; the item's inherited Q110 search records were retained alongside the new records.
- `report.md`: this report. `write_split.py` is a sandbox-only authoring helper, not a project file.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, the id, polynomial localization, good loci, 051X and generic freeness found no declaration giving this equality. The existing `RingTheory/GenericFlatness.lean` concerns generic flatness, not this good-locus identity. The item has no attached Lean declaration to treat as a finished proof.

## WANTED

None. All mathematical sources used are available in the read-only literature tree.

## Findings and changes

The imported statement is correct as written: the general good-locus statement of Stacks Tag 051X, label `lemma-generic-flatness-locus-localize`, specializes to the polynomial algebra. Its two extra conditions on the algebra itself are automatic for a polynomial ring in finitely many variables: its monomials form an R-basis, and its algebra presentation has the given variables and no relations. The proof does not need to invoke the general good-locus theorem as a new black box; it follows its two-inclusion argument for the module conditions directly.

The original node had an empty proof. The source's identifications of successive localizations and its word “clear” about further localization required expansion. Steps 1 and 3 now write the maps and inverse-map arguments; step 2 gives the cited freeness and finite-presentation inputs; steps 4 and 5 give the two prime-ideal arguments. No statement dispute or route change was necessary.

The inherited `blueprint.from.node` is null. `python3 tools/blueprint_refs.py ancestor lem-sfb-polynomial-good-locus-localization` likewise reports None: the `created.item` chain ends at the Lean-module-named creator of `lem-sfb-admissible-direct-image`, rather than at a blueprint id. I preserved this metadata and its explicit place/via chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, whose (3) is the inherited origin of this supporting chain. Searches across the imported blueprint for `good locus`, `good`, `051X`, `successive localization`, `localization of a module` and `localization` found no statement equal to this item. The irrelevant hits and specialized graded-localization coherence do not supply this equality.

Mathlib search hits were read, including `Module.freeLocus_localization` (Prime/FreeLocus.lean:103), `Module.basicOpen_subset_freeLocus_iff` (:166), and `Module.FinitePresentation.exists_free_localizedModule_powers` (Localization/Free.lean:78). The first concerns freeness at prime stalks; the second assumes finite presentation over the base and characterizes projectivity on a basic open; the third assumes finite presentation over the base and a nontrivial localized base. Our module can have infinite rank over the base and is only required to be finitely presented over a polynomial ring on its good charts. Thus these are not the item or one-line specializations of it. Loogle's finite-presentation/localized-map hits do not state a good-locus equality. The iterated-localization search also returned `IsLocalization.localization_localization_isLocalization`; the principal ring and module comparisons needed here already follow in a few lines from existing universal-property statements and are written as elementary steps.

## Not duplicates

No new nodes are proposed. In particular, the elementary polynomial and successive-localization comparisons remain proof steps. The existing generic tool leaves reused are `lem-weil-pbc-ring-localization-universal-property`, `lem-weil-pbc-localization-module-tensor`, `lem-weil-pbc-free-module-base-change-free`, and `lem-trf-localization-preserves-finite-presentation`. No helper restates a clause of the item, and no new dependency can introduce a cycle. The four tools are Mathlib leaves, so their use from other units does not replace the inherited unit's route.

## Unfinished work

None in the stage-1 split. No Lean was written, compiled or built. Server dry-run and push results are recorded below once available.

## Review by Q46

I read Tag 051X in `literature/stacks-project/algebra.tex`, including the preceding equations `equation-flat-and-finitely-presented` and `equation-good-locus`. The first paragraph chooses g=a/f^n and replaces the two localizations by the one at af. The second paragraph starts from a good g over R and further localizes at f. These are exactly the two inclusions of steps 4 and 5, with the source's f renamed h. There are no new nodes requiring separate source verification.

For step 1, I opened the polynomial-ring definition and used its actual evaluation universal property, not merely its name. I also opened the ring-localization universal-property node: it explicitly gives existence and uniqueness for any map making the denominators invertible. The two maps between the polynomial localization and the polynomial ring over A_t are inverse because they fix coefficients and variables. The module-localization definition explicitly gives the fraction equivalence relation and the induced polynomial action is checked on those fractions. These arguments require neither A reduced nor t regular; no cancellation of t in A is used. This is a short elementary comparison, not a separate lemma node.

For step 2, I opened each of its three cited statements. The localization-module-tensor node gives the map m tensor (b/t^e) to bm/t^e, with an isomorphism, and the free-base-change node explicitly allows any basis index set and either order of tensor factors. Thus it applies to an arbitrary free base module, not only finite free modules. The finite-presentation-localization node states preservation for every multiplicative subset; it applies over Q=A[x_1,...,x_n] with the powers of the constant t. Its Mathlib instance is present at Algebra/Module/FinitePresentation.lean:361–364; I read those lines. Step 1 identifies its localized ring and module with the objects the good condition actually uses. The source's module/tensor comparison is Tag 00DK, label `lemma-tensor-localization`, which I read, and the preservation is also consistent with Tag 05G5, `lemma-base-change-finiteness` (2), whose statement and proof I read. Only the existing nodes, not these documents in place of nodes, supply the non-elementary inputs.

For step 3, I opened the ring universal-property node and the module-localization-away definition again. The latter actually states the factorization property for maps to a module on which the inverted element acts bijectively. In R_(ah), both a and h are units, with the displayed inverses. In (R_h)_g, a=gh^r is a unit. Thus both directions of the ring comparison satisfy exactly the hypothesis of the cited ring node. On modules, all corresponding scalar actions are automorphisms, so the module factorization property applies twice. The explicit forward and reverse formulas extend the identity on M; uniqueness makes their composites identities. Polynomial compatibility is checked because the x_i commute with all these scalar inverses. This does not assume M finitely generated or finitely presented.

For step 4, I checked the actual localization-away definition for the existence of g=a/h^r. Under the contracted-prime identification already specified in the item's statement, h/1 is a unit, so g outside q means precisely a outside p. Primality and h outside p give ah outside p. I opened the free-module and finitely-presented-module definitions and verified that their actual basis and finite exact-sequence data are preserved by the explicit ring/module bijections from step 3. Consequently the good witness over R is ah, with no claim that goodness descends from R_h to R without further localization.

For step 5, all inputs are the preceding steps, so its external `uses` list is empty. Applying step 2 over A=R_a has exactly the two goodness hypotheses provided by the chosen witness a. Step 3 with r=0, also interchanging a and h, identifies the two successive localizations. The same elementary transport of bases and finite exact sequences from step 4 applies. Contraction says a/1 is outside q. This proves the reverse inclusion without a finite-presentation descent theorem or a hidden denominator argument.

I checked small cases: for R the zero ring, or h nilpotent, Spec(R_h) and D(h) are empty, so both sides are empty; the comparisons remain valid in the zero localization. For h a unit the two inclusions reduce to the same good charts, and for h=0 they are vacuous. For n=0 the argument is the usual ring-module localization argument and does not use any variable. For M=0 the empty basis and the zero finite presentation work on every chart. Infinite free bases cause no difficulty because the free-base-change statement permits arbitrary index sets. Zero divisors in a or h never require cancellation in R. The formula with r=0 is valid as well as r>0.

Against delivery-errors B–E, I checked self-contained hypotheses, exact citation statements, all non-elementary inputs, preservation of the original statement, absence of a route replacement, and the prohibition on elementary or clause-restatement child nodes. All citations have verbatim quotations in citations.json. No proof step is longer than 2000 characters. The split corrects missing arguments, not the statement. All writes are confined to the designated sandbox.

## Validation

The required `deliver.py Q46 lem-sfb-polynomial-good-locus-localization --no-push` completed successfully: server preflight passed, receipt commit `f510120d99f`. This includes the server DAG and split checks. The final push runs the preflight on the delivery including this validation note.
