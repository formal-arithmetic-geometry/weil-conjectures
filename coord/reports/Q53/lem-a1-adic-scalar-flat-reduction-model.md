# Q53 stage-1 delivery: lem-a1-adic-scalar-flat-reduction-model

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-adic-scalar-flat-reduction-model.json`: statement, split into nine steps; not a Mathlib leaf. No new DAG nodes and no new Mathlib leaves.
- `citations.json`: 21 entries, one for each step/dependency pair; each quote is copied verbatim from the cited node's statement.
- `searches.jsonl`: the required search command's records, retained without modification.
- `report.md`: this report.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the exact blueprint tag, adic scalar/flat reduction language and finite-projective terminology. Existing `FlatModel`, scalar-extension and derived-change-of-rings declarations supply parts, but no declaration found states all the arithmetic, completed ring-sheaf and normalized chain-map clauses of this item. No source declaration with `sorry` was treated as finished.

## WANTED

None for this delivery. The arithmetic is taken from existing DAG theorems, whose own reports already record their local-field literature needs; this delivery creates no arithmetic lemma.

## Corrections and scope

The item statement is unchanged. Added statement dependencies defining projectivity and Noetherianity. Preserved the inherited source, title, chapter/unit, creation record and blueprint ancestry. There was no earlier sandbox split or report to reuse, and no repair note for this item.

The inherited item source mentions Stacks 093M (flatness of completed constant coefficients), but this statement does not require flatness of the completed ring over the constant ring: the terms are already finite-free retracts over their respective coefficient ring sheaves. I read 093M to check the distinction, and prove the needed flatness directly. I do not infer a whole-complex splitting from degreewise retractions. I also do not identify the completed coefficient sheaf with the constant sheaf of the valuation ring.

Two existing helper source labels need care: `lem-weil-pbc-finite-type-constant-exact` names 093U, whereas the constant exactness lemma read in sites-modules.tex is 093J (`lemma-constant-exact`). Some bounded-flat helpers use 06YS; the actual `lemma-bounded-flat-K-flat` is 06YQ. I cite the correct existing helper statements and use 06YQ in the proof sources; these other nodes were not edited. No SGA source is used.

## Search results and reuse

The item's inherited searches were retained. Q53 additionally ran LeanFinder twice with different formulations of the whole comparison, Loogle on `"SheafOfModules", "flat"`, LeanSearch on derived reduction after completed scalar extension, and two source greps, the second within `CategoryTheory`. Read all returned hits: the closest ones are `Module.Flat.of_projective`, `Module.Projective.tensorProduct`, presheaf tensor, and generic derived categories; these do not state a comparison in the derived category of quotient-ring sheaves, let alone its transition/unit normalizations. No whole-item Mathlib match was found. These exact queries and their actual result summaries are recorded in the item and in the search command's unmodified log.

Before considering new facts I searched the whole DAG by statement/title, tag (093M, 06YQ, 0G7E) and finite-projective, constant-section, flat-retract and tensor-cancellation concepts. Ran `tools/blueprint_refs.py ancestor` and whole-blueprint searches for K-flat, coefficient extension, finite projective, bounded above flat, finite constant, scalar tensor and adic scalar. The existing finite constant sections, constant module exactness, valuation-ring, finite quotient, independent K-flat and derived change-of-rings nodes suffice. The finite-generator splitting, exactness of a finite-free retract and the inverse tensor formulas are explicit short arguments in the proof, not new nodes.

## Not duplicates

No new nodes. Existing general statements are cited rather than duplicated; no clause of the item was moved into a replacement node. The inherited `blueprint.same_as = []` remains appropriate: no blueprint node found states this entire combined normalized comparison.

## Review by Q53

I read the stage-1 brief and delivery-errors B--E in full, the chapter and unit records, the three route levels in SETUP.md, and GOAL.md. I read the current ancestor's finite-map-purity proof and the parent completed-perfect-scalar-pullback statement and assembly proof. This item supplies its arithmetic and finite quotient computation, without replacing the affine-line unit's route. The proof origin is marked agent because the assembly and its explicit normalization calculations are written here, using existing generic results and the listed literature.

For Step 1 I opened `lem-weil-l-adic-extension-integers-dvr` and `lem-weil-valued-dvr-finite-quotients`. The former explicitly gives a PID/domain, finite residue field and uniformizer factorization; the latter gives the actual finite quotients. I checked that the extending absolute value sends ell to ell^(-1), so the exponent of pi in ell is positive, not merely an arbitrary valuation. The argument proves that ell^n kills A_n even in a ramified extension. I read the Noetherian, perfect-complex and adic-datum definitions: principal ideals imply the required Noetherianity, and injectivity of pi^n with its quotient augmentation proves the displayed two-term resolution. The adic datum requires finiteness and perfectness at every positive level and torsion of the first quotient, all verified here. No regularity or flatness of an inverse limit is being assumed.

For Step 2 I read Bhatt--Scholze Lemma 4.2.12 (PDF page 30, printed page 30) and the full statement of `lem-pur-proetale-finite-constant-sections`. Its discrete-space clause applies without a qcqs assumption; the extra qcqs qualification in the lemma's totally-disconnected clause is not needed here. Our pi_0 has explicitly the quotient topology, so factoring a discrete-valued continuous function through components is a direct topological argument for every site object. I checked that the helper preserves constant values and site restriction; postcomposition then gives the coefficient transitions locally on constant sections. I read the adic datum and inverse-limit definition: both limits are the same compatible families, so all projections are identified, not only the underlying object.

For Step 3 I read Stacks algebra.tex `lemma-characterize-projective` (05CF), the beginning of `lemma-finite-projective` (00NX), and the projective-module definition node. Lifting the identity through the finite generating surjection produces exactly the required retraction. I read constant exactness at sites-modules.tex 093J and the full statement of `lem-weil-pbc-finite-type-constant-exact`, which explicitly preserves finite sums as finite colimits. Functoriality of constant realization and scalar extension retains the splitting equation. The displayed formula with an arbitrary coefficient map checks transition compatibility for each splitting map. It does not assert compatibility of these splittings with the differential.

For Step 4 I checked flatness against its definition, not against an unrelated module-flatness theorem. A retract of the finite identity-sum tensor functor is exact: the proof spells out injectivity and local kernel and epimorphism lifts using the inclusion/retraction. This uses only the displayed splittings, the standard finite basis and sheaf tensor's definition, and remains an elementary step. Finite many lifts have a common covering refinement; no infinite product exactness is used. It applies both before completion and over B_T itself. No node for a new flat-retract theorem is warranted.

For Step 5 I opened `lem-weil-pbc-independent-bounded-flat-kflat` and read Stacks sites-cohomology.tex `lemma-bounded-flat-K-flat` (06YQ). The node explicitly allows independently varying site object, morphism and coefficient universes. Our complex is bounded above because constant realization and tensor preserve its zero terms, and Step 4 supplies every term's flatness. I read the size convention as well. This is the actual K-flatness theorem used, not its definition alone.

For Step 6 I read sheaf tensor's definition and the balanced identity in sites-modules.tex `lemma-flat-change-of-rings` (05V4). I verified both balancing relations, both inverse composites and the degree-r differential equation. The coefficient rings occur in degree zero, so these maps do not permute two graded factors and introduce no Koszul sign. Restriction-compatible balanced maps of the sectionwise tensor presheaves induce the stated maps after sheafification. This is an elementary inverse calculation, not an uncited cancellation theorem.

For Step 7 I opened the entire `lem-pur-derived-change-of-rings` statement and checked clause (2): it explicitly computes on any K-flat resolution and gives an isomorphism in D(O'), the target ring-sheaf module category. Applying it to the identity resolution of the K-flat M_T proves the needed derived comparison in D((A_n)_T). The identity resolution needs no boundedness on arbitrary target objects. This is stronger and more precise than merely an isomorphism of underlying abelian derived objects.

For Steps 8 and 9 I substituted a tensor generator into each route of the transition, unit and chain-map squares; the text records the actual equal expressions. The limit projections satisfy q pr_(n+1) = pr_n by Step 2. Ordinary equality of chain maps survives localization, while the cited derived-change-of-rings functor provides the K-flat computation. The inverse formulas contain no splitting choices, proving independence. I checked that these assertions preserve the supplied scalar differentials rather than choosing new ones.

I tested n=1, E=Q_ell, ramified finite E, the zero module/zero complex (where m=0 is allowed), a single nonzero degree, nontrivial differentials such as multiplication by pi, disconnected schemes and the empty scheme. In particular I did not replace a complex by its cohomology, assume that finite coefficient section sets are finite on arbitrary objects, assume invertibility of ell on T, or use a whole-complex free splitting. All nine steps are below 2000 characters, and none hides a further comparison or standard lemma. The cited dependencies' actual statements were opened and their relevant verbatim portions placed in citations.json. The five generic off-unit theorem uses are declared in split_report.tool_uses with their reasons; definitions and the existing Mathlib finite-quotient leaf are the remaining tools.

## Unfinished work

None in the stage-1 split. No Lean file was written, no compiler was run, and no repository or launcher file was modified.
