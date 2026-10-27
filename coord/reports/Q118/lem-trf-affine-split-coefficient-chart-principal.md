## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-affine-split-coefficient-chart-principal.json`: statement, split into eight steps; no Mathlib match for the whole item.
- `citations.json`: verbatim statement evidence for every dependency of every proof step.
- `searches.jsonl`: actual search-command records, also appended to the item's existing Mathlib-search history.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The proof reuses the existing Mathlib leaves `lem-weil-pbc-flat-module-base-change`, `lem-weil-pbc-flat-module-quotient-flat` and `lem-trf-flat-module-torsionfree-domain`, together with existing definitions. No helper is needed for the explicit finite-sum and fraction calculations.

Attachments: none. Searches of `lean/WeilConjectures/` by the exact blueprint tag, split-coefficient/coefficient-chart terminology, and the blowup/coefficient-ideal terminology did not find a declaration proving the full statement. The Popescu coefficient-chart declarations concern different objects. The existing affine blowup chart definition is a dependency, not an attachment for this theorem.

WANTED: none.

The statement and its six statement dependencies are retained verbatim. The incoming node had no proof. Its source already describes a corrected fibrewise divided-generator assertion; the proof now supplies that assertion without assuming that a divided generator is globally invertible. No named declaration with a missing node was recorded in the incoming item.

Nothing remains unfinished in this one-level split. No Lean was written or compiled. Only this sandbox was written. The required delivery tools perform the server checks.

## Source error

In `literature/stacks-project/flat.tex`, Tag 0810, `lemma-helper-blowup-affine-space`, the chart paragraph asserts that a divided element of the ideal is a unit in the entire base-changed algebra. This fails for R=k, B=k[x], the monomial splitting, J=(x), h=c=a=1. Then C=k and the chart is R itself, but every g in J is divisible by x, so no divided g is a unit in k[x]. It is a unit at the fibre-generic prime (0). The same paragraph's notation `S tensor_S R'` also needs the tensor product over R.

The item was already stated with the correct fibrewise conclusion; no statement correction or weakening was necessary. Steps 4 and 5 construct all divided generators using the retraction, and show that their coordinates jointly generate 1. Step 8 chooses a nonzero divided generator separately for each fibre, then inverts it only at the generic prime. The proof does not assume that the arbitrarily chosen c is one of the original coordinates. The source's erroneous claim is not used as a theorem.

## Searches and blueprint route

I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` unit and `lem-trf-local-term-locality` statement/proof. The item is a pre-existing algebraic tool on the inherited flattening branch of `lem-trf-affine-generic-rank-blowup`; it is not the unit's key statement, and this split changes no unit or chapter. The latest ancestor discusses the contracting local-term theorem; its inherited ancestor metadata is preserved, with the precise Tag 0810 chart paragraph named as the place this tool serves.

`tools/blueprint_refs.py ancestor` identifies `lem-trf-local-term-locality`. Whole-blueprint searches for `split coordinate`, `0810`, `R[I/a]` and `divided` found no blueprint node stating this algebraic result. Whole-DAG searches by Tag 0810 and coefficient/split-coordinate terminology found the existing parent, its coefficient-ideal and Fitting helper nodes, and the fibre-generic localization nodes. I opened the parent and the neighbouring fibre-generic localization statement: neither gives the principalization conclusion independently, so neither is being used circularly. Searches by flat-base-change, flat-quotient and flat-domain titles found the three existing leaves actually used. No new node was created.

The required msearch commands ran for the item with LeanFinder, LeanSearch, Loogle and Mathlib grep, including a second semantic phrasing about primitive divided coordinates of split vectors. All five new searches succeeded. The first semantic searches returned fibre elements, Zariski's main theorem, smooth loci, fractional ideals and faithfully flat ideal facts; none states the chart theorem. The second LeanFinder query returned Smith normal form and regular-sequence facts, with extra PID/finite-rank or regular-sequence hypotheses. Loogle returned flat tensor-product and injectivity facts; these cover ingredients, not the coordinate argument. The algebraic-geometry grep found no blowup/coefficient-ideal declaration. I read the existing leaves' statements and the Mathlib flat base-change and torsion-free declarations cited in their records. Original item searches were retained, and the new queries and actual summaries were appended exactly as logged.

## Not duplicates

There are no new nodes. The elementary chart identities and split-coordinate calculation remain steps of this item. The three flatness facts are citations of existing leaves, not duplicate nodes. The neighbouring coefficient-ideal node concerns Fitting-ideal rank detection before the chart construction; the neighbouring fibre-generic localization node concerns local scalar comparisons, not division of the ideal generators.

## Review by Q118

I reviewed the item against Tag 0810 (`flat.tex`, `lemma-helper-blowup-affine-space`), concentrating on the paragraph beginning “Let a in I”. I also read `algebra.tex`, `lemma-affine-blowup`, `lemma-blowup-add-principal`, and Tag 00HI (`lemma-flat-base-change`), and checked the actual statements of every cited node. These sources justify the route but the proof is marked agent-written because it reconstructs and repairs the source's divided-generator argument. There are no new-node statements to audit.

Step 1 cites the definition `def-nagata-blowup-chart-ring`, whose statement really embeds the chart as a subalgebra of R_a, and `def-weil-pbc-module-localization`, which gives fractions and the zero criterion. A product hc is invertible in R_a, so each factor is invertible there. Restriction to the subring proves injectivity of multiplication without assuming R is a domain or a is regular in R. The inverse chart-localization comparison is explained through the inclusion and the generators R, 1/a, not asserted from a weaker source lemma.

Step 2 again uses precisely the chart definition: hd belongs to I for each d in C, so hd/a belongs to the chart, and c(hd/a)=d. This proves both ideal inclusions in two lines. It is elementary, not a new principalization node.

Step 3 uses the statement of `lem-weil-pbc-flat-module-base-change`, which applies to an arbitrary ring map R to R*, with no flatness hypothesis on the chart map. Its tensor factors are reversed by the displayed elementary interchange. I checked that `def-weil-pbc-flat-ring-map` explicitly says tensoring an injection is injective: it supplies exactly the tensor argument for the three multiplication maps. Thus this step does not cite a definition for an unstated preservation theorem.

Step 4 uses the map and composition clauses of `def-weil-module-base-change`. The coordinate and retraction maps are written explicitly on pure tensors and finite-support vectors, so no uncited theorem about tensoring arbitrary products is needed. Every original i(b) has finite support, and an element of a tensor product is a finite sum of pure tensors, so the displayed coordinates do lie in the direct sum. The identities rho* i*=1, c g_nu=j_nu and c(i*g_nu-v_nu)=0 follow by finite sums and linearity. Cancellation is on each R* coordinate, using step 1; it never takes place modulo a prime containing c. These are elementary equations rather than a hidden lemma with extra hypotheses.

Step 5 expresses c as a finite linear combination of the actual generating coordinates of C. Substituting step 2 and cancelling c gives the displayed unit-ideal relation. This is why the proof works even when c was not one of the original coordinates. It neither assumes a single divided coordinate is 1 nor mistakes the joint unit-ideal relation for an invertible element in B*.

Step 6 uses the residue-field map explicitly stated by `def-weil-residue-field` and the balancing/maps in `def-weil-module-base-change`. The inverse image of p* is a prime p; the residue-field map is a field homomorphism, so E is a field extension of kappa(p). This checks the precise hypothesis needed for geometric integrality. The two tensor formulas give the fibre ring itself, not the quotient by p* alone. All its field extensions are allowed by the item, so no finite-type or Noetherian assumption is introduced.

Step 7 cites `lem-weil-pbc-flat-module-quotient-flat` with the already flat R*-module B*, then `lem-trf-flat-module-torsionfree-domain` over D=R*/p*. Both statements give exactly these conclusions, with arbitrary modules and no finiteness hypotheses. D is a domain because p* is prime; R* itself need not be a domain. The zero criterion from `def-weil-pbc-module-localization` proves the injection. I wrote both fraction formulas for the identification with the fibre so that “natural map” is checked, not inferred from an abstract isomorphism. The quotient is nonzero because its injection is unital into the nonzero fibre domain. Consequently p*B* is prime.

Step 8 uses the scalar-extension map of `def-weil-module-base-change` to reduce coordinate functions and the fractions of `def-weil-pbc-module-localization` to invert a generator outside q*. The finite unit-ideal relation cannot have all its coordinates vanish in the residue field. Hence one g_nu is nonzero in that fibre, and the injection of step 7 identifies this with g_nu outside p*B*. Each inclusion of the desired ideal equality is then written explicitly. All citations use node statements, not constructions hidden in their proofs; `citations.json` copies those statements verbatim.

I tested the edges relevant to delivery-errors B–E. If a=0 or is nilpotent, R_a and the chart are zero, multiplication is injective on the zero ring/module, and the primewise conclusion is vacuous. This also handles h=0, c=0, C=0, J=0 and an empty list of generators. Infinite A causes no infinite sum: only finite supports occur. For R=k[s], B=R[x], J=(sx), h=1 and a=c=s, the chart is R and c lies in the prime (s); although j vanishes in the fibre there, its divided element x does not. This checks the order of division and reduction used in steps 4–8. The example R=k, B=k[x], J=(x), a=h=c=1 checks that the final localization is essential and catches the source's global-unit error. The two non-elementary steps cite existing flatness leaves; every other step consists of the displayed fraction, finite-sum, balancing or ideal-inclusion computation. No non-elementary step exceeds 2000 characters, no argument was moved into a restatement node, and no induction or circular appeal occurs.

Corrections made during this review: replaced the source's choice of a single globally invertible divided generator by a joint coordinate relation and a fibre-dependent choice; explicitly established the quotient-to-fibre injection before identifying the prime; kept cancellation before residue reduction; and kept R_a, rather than an unjustified R_h, as the chart's localization. The incoming statement already incorporated the last two intended conclusions, so its text remains unchanged.
