# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-sf-strict-dvr-reduction-triangles.json`: statement, split into seven proof steps; not a Mathlib leaf. The statement is retained verbatim.
- `citations.json`: one verbatim statement quotation for each node used by each numbered proof step.
- `searches.jsonl`: the required search command's actual log; five searches run in this session.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files, repository files, chapter records or unit records were written, and no compiler was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and the notions strict DVR, residue triangle, and K-flat models. The library contains general K-flat/tensor constructions, but I found no declaration stating all the simultaneous quotient-realization and residue-kernel clauses. Partial/general declarations are not attachments.

## WANTED

None for this split. The sources used for the argument are present in the read clone.

## Findings and changes

The item was unsplit, and this sandbox had no existing item or report to continue. I copied the current item, preserving its statement, source, blueprint ancestry and inherited searches. I read the chapter record and `sk-rem-sf-pf-done`: the latter is an interface-discharge remark with no numbered proof steps. This supporting coefficient lemma is not its key statement, so no `realized` fields were changed. I also read the ancestor's current-blueprint evaluation-naturality paragraph and kept the recorded route through the local-projective-model/completion/residue-bound inputs.

The source of the item is Stacks sites-cohomology.tex, Tag 0942, label `lemma-bounded`, proof (1). Its displayed triangle uses the successive ideal quotient. I refined that argument explicitly for the present finite constant quotients without assuming that an inverse-limit coefficient sheaf is the discrete constant ring. The authored refinement is marked `proof_origin.by = agent`. Tags 06YS (`lemma-K-flat-resolution`) and 06YU (`definition-derived-tor`, with its preceding construction) provide the common-resolution computation. In sites-modules.tex I read Tag 093J (`lemma-constant-exact`), Tag 03EI (`lemma-sheafification-exact`), the module-sheafification/scalar-action discussion, Tags 03DA/03DB (`lemma-abelian`, `lemma-limits-colimits`), and the tensor/flatness statements. In derived.tex I read Tag 0152 (`lemma-derived-canonical-delta-functor`). No SGA source is used.

No statement dispute was found. In particular, no invertibility of ell on X is needed: these are coefficient-module calculations on its pro-etale site. No completeness of K, Tor-amplitude bound, constructibility or quasi-compactness enters the proof.

## Existing-node and Mathlib searches

I searched all `dag/nodes/` by K-flat/flat-term resolution, constant/exact sheafification, restriction of scalars, and short-exact-sequence triangles; I opened the statements of every cited node. I ran whole-blueprint searches for `K-flat resolution`, `constant sheaf exact`, `short exact sequence of complexes`, `simultaneous`, `residue kernel`, and `quotient transition`, and the ancestor query. No blueprint node states this entire item. General resolution, constant-realization, tensor-comparison and triangle results already have nodes, so none was recreated.

The Mathlib search log records LeanFinder with two genuinely different phrasings, LeanSearch, Loogle and a grep of Algebra/Homology/DerivedCategory. All five services/commands answered successfully. I retained the imported searches, including their recorded unavailable LeanSearch result, rather than claiming that result had been a successful search. The current LeanSearch/LeanFinder hits include `Module.Flat.lTensor_shortComplex_exact` and `rTensor_shortComplex_exact`; I read RingTheory/Flat/CategoryTheory.lean, which treats ordinary ModuleCat objects. These do not state the ringed-site simultaneous tower. The grep leads to `DerivedCategory.triangleOfSES`, `triangleOfSES_distinguished` and its naturality; I read Algebra/Homology/DerivedCategory/ShortExact.lean:33-116. That generic fact is already the Mathlib leaf `lem-weil-pbc-complex-ses-triangle`. Adic-completion flatness and local-cohomology-diagram hits also omit the required sheaf/tower/kernel clauses. The item therefore remains a split statement rather than a Mathlib leaf.

## Not duplicates

There are no new nodes. The elementary DVR kernel, B-linearity and degreewise tensor argument remain proof steps, not renamed clauses in new nodes.

## Review by NI

I checked the item against the displayed triangle in Tag 0942, then checked the more explicit claims that are not written there: the injection is the multiplication-by-varpi^n map from the residue quotient; it is linear for the inverse-limit coefficient action; a single flat-term resolution computes every reduction; and its actual transition map remains the second triangle arrow. None of these was replaced by an existential unnamed map.

Step 1 uses the full statement of `lem-pc-kflat-resolution`: every complex over any sheaf of commutative rings on a site has a K-flat resolution with flat terms. It applies to B itself, regardless of whether B is a constant sheaf. `def-weil-abstract-derived-category` supplies a representative of K and makes Q(f) invertible. I checked both the unboundedness and flat-term clauses in the cited statement and in Tag 06YS.

Step 2 is elementary cancellation inside the field E, using exactly the ring embedding and nonzero uniformizer specified in `def-weil-l-adic-coefficient-extension`. The change-of-lift, injectivity, image/kernel equality and A_(n+1)-linearity calculations are written in the step. Cancellation occurs in R inside E before quotienting; the proof does not cancel a nilpotent element of A_(n+1). I did not create a separate node for this coefficient calculation.

Step 3 uses `def-sfb-site-derived-constant-module-functor` for its explicit assertion that the constant module functor is additive and exact, not merely for its name. `def-sf-site-constant-module-functor` specifies its underlying abelian sheaf and action. `lem-weil-pbc-module-sheaves-colimits-forgetful` explicitly preserves kernels and cokernels, so its application to the exact constant-module sequence really gives underlying abelian exactness. The relevant source is Tag 093J, not an assertion about exactness of arbitrary inverse limits. Its site-size hypothesis is satisfied by the small skeleton and module universe already fixed for X_proet.

Step 4 uses only the unique extended constant action, the coordinate identities of `def-pur-sheaf-inverse-limit`, and the sectionwise action in `def-pc-sheaf-restrict-scalars`. For u_n I checked the C_(n+1)-linearity identity in step 2 with its source acted on through C_(n+1) -> C_1, so restriction along pi_(n+1) really gives the pi_1 action. For q_n the requisite identity is q_n pi_(n+1) = pi_n. Kernel/cokernel computation in `def-weil-sheaf-of-modules-category` justifies reading the already exact underlying sequence in Mod(B). This is an elementary change of actions; u_n is never treated as a ring homomorphism.

Step 5 uses `def-pc-flat-sheaf-modules` whose statement defines flatness as exactness of the fixed-factor tensor functor. Thus applying exactness needs no unmentioned flatness theorem. I read `lem-pc-sheaf-modules-tensor-closed` to verify that it supplies the symmetry needed to put P^i on the left. The two composites with the differential are displayed on elementary tensors, and `def-pur-sheaf-tensor-product` sheafifies those same maps. This proves an actual degreewise short exact sequence of complexes. Only P^i is assumed flat; no flatness of C_n is smuggled in.

Step 6 uses the K-flat computation assertion of `lem-pur-derived-change-of-rings`, the localization/scalar-restriction comparison explicitly stated in `lem-pe-restricted-kflat-tensor-identification`, and the coefficient-map naturality explicitly stated in `lem-sf-ringed-kflat-single-tensor-comparison`. I opened all three statements. The specialization in the second is B -> B -> C_n with first map the identity; the same P and the same e Q(f) are used at every n. The third node applies to arbitrary B-linear sheaf maps, including q_n, with no requirement that C_n be flat. Its comparison is normalized by K-flat computation, as is the change-of-rings comparison, so the arrow equation is the canonical quotient transition. The scalar-swap/inverse in the restriction comparison cancel; no change of model or unrelated objectwise isomorphisms is hidden here.

Step 7 uses the existing Mathlib leaf `lem-weil-pbc-complex-ses-triangle`, whose statement explicitly gives Q(f) and Q(g) as the first and second arrows for every degreewise short exact sequence in an abelian category. It is not the weaker degree-zero-only triangle node. Mod(B) is abelian by its definition node and the chosen site size. The change of vertices is justified by the isomorphism characterization of distinguished triangles in `def-weil-abstract-derived-category`. Substituting the equation of step 6 computes the second arrow, so this step does not silently discard transition-map compatibility.

For small cases I checked n=1: 0 -> R/(varpi) -> R/(varpi^2) -> R/(varpi) -> 0 has the claimed multiplication-by-varpi injection; it need not split, and the triangle lemma does not require splitting. For ramified E the same cancellation uses varpi rather than ell and remains valid. For X empty all three coefficient sheaves and all reductions are zero objects and the argument still applies. For K=0 one may take P=0; for arbitrary unbounded K the resolution theorem has no degree bound. These tests expose the two tempting mistakes: cancelling varpi in the quotient ring and assuming split coefficient sequences. Neither is used.

I checked delivery-errors B through E against the actual files: no new-node format or duplication issue arises; every non-elementary step cites a statement giving its input; the two elementary sheaf/tensor steps spell out their short arguments; there is no restatement moved into a child node; and the hypotheses above hold at each application. All seven proof steps are below 2000 characters. Generic off-unit tools are declared with their purposes in `split_report.tool_uses`; they implement this coefficient argument without replacing the unit's route. The changes made during this reading were to state explicitly the scalar-action factorization in step 4 and the naturality equation and restriction comparison in step 6. No source or target statement was altered.

## Unfinished work

None for this stage-1 split. The existing cited nodes retain their own independent DAG work; this delivery does not claim to prove them or to finish any Lean declaration.
