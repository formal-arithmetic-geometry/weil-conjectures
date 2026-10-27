# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-subcurve-dualizing-adjunction.json`: split the item in five steps; statement unchanged; Mathlib verdict: no match.
- `citations.json`: every proof-step citation with the verbatim supporting node statement.
- `report.md`: this report. The search wrapper also wrote `searches.jsonl`.

## New nodes

None. Zero Mathlib leaves. All supporting results already have nodes. In particular I reused the closed-immersion coherent equivalence, coherent sheaf Hom, closed-embedding cohomology, and the module/abelian cohomology comparison instead of creating four duplicate nodes. No Lean was written and no compiler or build was invoked.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the exact blueprint tag and for dualizing/subcurve terminology, including the curve modules. The dualizing-complex hits concern constant-coefficient etale or pro-etale Verdier duality, not coherent structure-sheaf duality on a singular curve. No declaration states this item.

## WANTED

None: the relevant Stacks sources are present locally.

## What changed and what was wrong

The imported statement is correct: it is the reduced pure-one-dimensional specialization of Stacks 0E33(2), `curves.tex`, label `lemma-closed-immersion-dim-1-CM`. Its proof was empty. No hypothesis or conclusion was changed. I retained the original parent, citations, search records and blueprint provenance. The sandbox initially contained only dispatcher markers, so there was no previous split or report to repair and no prior search log to reuse.

The source's proof uses derived right adjoints. The item's own hypotheses already choose dualizing modules together with their ordinary H^1-dual representing isomorphisms. I wrote the corresponding ordinary representing-functor argument explicitly, marked `proof_origin.by = agent`, instead of introducing derived duality objects that this statement does not need. This is a choice below the unit-level route, not a replacement of a unit step. The current blueprint unit and chapter were read under `literature/blueprint/latest/`; the item supplies the existing support-of-dualizing-map prerequisite on the alteration/curve-linear-series branch. The ancestor command returns None for the inherited provenance chain, which I preserved, rather than inventing an ancestor. `same_as` remains empty after the whole-blueprint searches.

## Searches and duplicate checks

I searched the whole DAG by statements and titles, and searched the Stacks tags/labels and the existing parent. I ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for dualizing, closed subcurve, and annihilator. None is an exact blueprint duplicate. The nearby nodal-subcurve annihilator lemma assumes nodal/Gorenstein hypotheses and does not replace this item for all reduced curves.

The required msearch wrapper was run for the item: LeanFinder with a closed-subcurve dualizing-sheaf formulation, a second LeanFinder formulation about quotient canonical modules, Loogle with `AlgebraicGeometry.IsClosedImmersion, "Hom"`, grep with `dualizing|dualising|canonicalModule`, and LeanSearch with the annihilator formulation. All five services returned successfully. I read their hits: they concern quotient ideal sheaves, closed embeddings, Noetherian quotients and ordinary linear-dual annihilators. None gives the coherent dualizing-module theorem. The new search entries reproduce the queries in `searches.jsonl`; original imported searches are retained.

## Not duplicates

No new nodes, hence no new/existing node pairs. The existing results listed above are cited, not recreated.

## Review by Q07

I read Stacks `curves.tex`, Tag 0E33, label `lemma-closed-immersion-dim-1-CM`, its statement and full proof, and 0BS2/0BS3 for the chosen dualizing modules. The source allows arbitrary fields and does not assume connectedness or Gorensteinness in 0E33. The item's stronger reduced pure-dimension-one hypotheses are exactly those under which its chosen representing modules are supplied by the existing reduced-curve-dualizing-module node. I also read the use of this identification in 0E3E. There is no statement dispute.

Step 1: I opened the statements of `lem-trf-proper-field-invertible-coherent`, `lem-sfb-reduced-curve-dualizing-module`, `lem-weil-pbc-closed-immersion-coherent-equivalence`, and `lem-weil-pbc-coherent-sheaf-hom-coherent`. The first gives Noetherianity and coherence of O for both proper k-schemes, with O invertible by the local basis 1; the second gives coherent omega modules; part (1) of the third really includes coherent direct images; the fourth really gives coherence of sheaf Hom. I read Stacks 087T (`coherent.tex`, `lemma-i-star-equivalence`) and 01CQ (`modules.tex`, `lemma-internal-hom-locally-kernel-direct-sum`) against these uses. Both schemes are locally Noetherian before 087T is applied, and both Hom inputs are coherent before 01CQ is applied. No finite type or smoothness condition was inferred from reducedness alone.

Step 2: I opened `def-pur-sheaf-hom` and `def-sbc-closed-immersion-ideal-sheaf`. Together with the explicitly cited `def-weil-closed-immersion`, they give the sectionwise sheaf-Hom rule, the kernel ideal, and the surjectivity needed to identify the quotient. The first dry run passed; my final reading added this explicit surjectivity citation rather than attributing surjectivity to a kernel definition. The argument actually proves the evaluation identification: j f(1)=f(j)=0, and an annihilated section defines the inverse by a local lift of a quotient section. I explicitly used local lifts and gluing; I did not assume global sections of a quotient sheaf lift globally. This is elementary algebra with sheaf gluing, so the step is marked elementary. Stacks 0A75 (`duality.tex`, `lemma-compute-sheaf-with-exact-support`) confirms the same annihilator formula and adjunction, but the proof step proves that elementary part rather than treating this tag as an uncited theorem.

Step 3: I re-read part (1) of the coherent-equivalence node. Its exact essential image is J-annihilated coherent modules, not merely modules with set-theoretic support in Y. Step 2 has established precisely JH=0, so descent to a coherent D is justified. Full faithfulness and coherence of i_*G are assertions of this same equivalence. The remaining Hom factorization is written out: J kills i_*G, so every map to omega_X lands in its annihilator, uniquely. It is not an unstated finite-duality theorem.

Step 4: I opened both comparison nodes. `lem-sc-cohomology-closed-immersion-pushforward` states the full cohomology isomorphism for a closed topological embedding; it is not an etale-only claim. `lem-sc-zariski-module-abelian-cohomology-agree` gives natural module/abelian comparisons in every degree, so no preservation of injectives by scalar forgetting is assumed. I read Stacks 02UV (`cohomology.tex`, `lemma-cohomology-and-closed-immersions`) and 03FD (`sites-cohomology.tex`, `lemma-cohomology-modules-abelian-agree`). Naturality for multiplication by each element of k makes their composite k-linear. The reduced-curve-dualizing-module node really states Hom(F,omega)=Hom_k(H^1(F),k) for every coherent F, and step 3 proved i_*G coherent. All proper, reduced, pure-one-dimensional and nonemptiness assumptions for X are already hypotheses, and for Y they remain available for step 5.

Step 5: I used the explicit uniqueness clause of the dualizing-module node and also wrote the two inverse maps by evaluating the natural Hom bijection on identity morphisms. Thus I did not cite a Yoneda node that only states full faithfulness for scheme representables. The inverse identities follow by precomposition naturality, and applying ordinary pushforward to these inverse maps gives the requested module isomorphism. The identification respects the specified representing structures, so the word natural is justified even when arbitrary representatives of omega are chosen. The entire proof uses no invertibility of omega_X or omega_Y.

Small-case checks: for i=id, J=0 and evaluation identifies Hom(O,omega) with omega, as it should. For an open-and-closed union of connected components the annihilator is the direct summand on those components, and H^1 splits the same way. At the node A=k[x,y]/(xy), with Y cut out by (x), Hom_A(A/(x),A)=Ann_A(x)=(y), not A/(x) viewed as a literal submodule with the same generator; the proof only asserts the canonical dualizing-module identification and does not trivialize omega or confuse pullback with annihilator. The reasoning also applies to a reduced non-Gorenstein curve: the sole inputs on omega are coherence and representability. Arbitrary characteristic and nonalgebraically closed k cause no scalar-extension assumption. The nonempty pure-dimension-one hypotheses exclude a zero-dimensional Y; no illicit argument uses such a Y. The quotient algebra calculation itself also handles the empty closed subscheme, though that is outside this item's hypotheses.

I checked delivery-errors B through E: self-contained unchanged statement, no new unsplit proof sketches, every non-elementary input cited by its actual statement, no newly created clause of the item, no shifted coefficient category, and no dependence on the item in the supporting nodes. Each step is below 2000 characters. The five cross-unit generic tools are declared in split_report.tool_uses for the maintainer to review; no tool_uses field was added. There was no earlier return to repair. I corrected a potential citation gap by including the module/abelian comparison explicitly; citing only topological cohomology would not have sufficed for the module cohomology used here.

## Unfinished work

None for this stage-1 split. The reused dualizing-module prerequisite remains its own DAG item; this delivery does not claim to have proved or formalized it. The first server dry run passed at 45bc2dfa1f3. A final explicit closed-immersion citation was then added and is validated by the final dry run.
