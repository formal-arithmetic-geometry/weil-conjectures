# Stage-1 delivery Q74

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adic-smooth-fixed-residue-lifting.json: item, four proof steps; statement unchanged, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-square-zero-small-extension-reduction.json: statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for every cited node in every item step.

## Attachments

None. Searched lean/WeilConjectures by the blueprint tag and fixed-residue/Artinian/adic-smoothness terminology, then inspected the RingTheory formal-smoothness modules. No finished declaration states this item or the new reduction.

## WANTED

None. All mathematical sources used are available locally.

## Corrections and scope

No statement dispute. The imported item had no proof. Its source 0DYL refers to 0DYG; the latter's genuine hard input is (3) implies (2), reducing small Artinian extensions to local square-zero tests whose maximal ideal is nilpotent. The new node states only this reduction, not the item's equivalence. The arbitrary-test-ring inverse-image subring construction remains explicitly in the item's proof. No SGA source, Lean writing, compiler, or build was used.

Read the chapter and unit records and the current latest blueprint unit and direct-images proof. The latest direct-images text uses compactification, whereas the inherited supporting ancestry records the older alteration/moduli route. This low-level split realizes the already assigned 0DYL prerequisite without changing the unit. The ancestor search reports None; the inherited null blueprint ancestor and via chain are retained faithfully. Blueprint searches for formal smooth, 0DYG, Artinian, small extension, maximal ideal, fixed residue, and square zero gave no matching blueprint result.

## Not duplicates

lem-sfb-local-square-zero-small-extension-reduction vs lem-sfb-adic-smooth-fixed-residue-lifting: the new node assumes small-extension lifting for a general local map and concludes lifting only for local square-zero tests with nilpotent maximal ideal; it does not state adic formal smoothness or the fixed-residue equivalence. The item supplies the passage from marked maps to those tests and the passage to arbitrary rings.
lem-sfb-local-square-zero-small-extension-reduction vs lem-sfb-versal-unobstructed-adic-criterion: that node compares a versal deformation category's unobstructedness with smoothness of its hull; it has no general local square-zero lifting conclusion. It mentions 0DYG only as supporting source context.
lem-sfb-local-square-zero-small-extension-reduction vs lem-sfb-artin-local-test-algebra: factorization of surjections between already Artinian rings does not reduce non-Artinian bounded-local square-zero test rings to Artinian tests.
lem-sfb-local-square-zero-small-extension-reduction vs lem-sfb-smooth-fixed-residue-artinian-test: the latter proves scheme smoothness for a locally finite type map over a locally Noetherian scheme, not lifting for arbitrary Noetherian local algebras and possibly non-Artinian test rings.
lem-sfb-local-square-zero-small-extension-reduction vs lem-sfb-fixed-residue-lifts-truncated-section: sections of truncated Noetherian quotients are not lifting into arbitrary local square-zero test rings.
lem-sfb-local-square-zero-small-extension-reduction vs lem-weil-pbc-smooth-at-prime-artinian-lifting: finite-type algebra smoothness at a prime is a different conclusion and does not cover arbitrary Noetherian local target algebras or the bounded-local-test reduction.

lem-sfb-local-square-zero-small-extension-reduction vs lem-weil-pbc-smooth-artinian-lifting-at-point: the existing node is a scheme smoothness equivalence for locally finite type morphisms over locally Noetherian bases; the shared 02HS citation merely defines small extensions. It does not state the reduction to bounded local square-zero test rings for an arbitrary Noetherian local algebra.

## Review by Q74

I read Stacks formal-defos.tex, Tag 0DYL (lemma-smooth), including its proof of (1) iff (2), and Tag 06GC's category definition. I read more-algebra.tex, Tag 0DYG (lemma-fs-local), statement and complete proof, and algebra.tex, Tag 02HS (definition-small-extension). The new node is precisely the last paragraph's implication (3) to (2); its hypotheses include S Noetherian, a local base map, a residue isomorphism, square-zero J, and a nilpotent maximal ideal in A. It intentionally does not assert A Artinian. The hard argument retained as this statement-only obligation is filtration of J by m_A powers, restriction to the inverse image of the source image, one-dimensional quotient tests and the product/retraction construction for an arbitrary residue vector space. This is strictly smaller than the item; it is not the whole 0DYG equivalence renamed.

For step 1 I opened the existing Artinian-local Noetherian/nilpotence leaf and read its complete statement, and read algebra.tex Tag 00J8's proof. The step uses exactly the claimed maximal-ideal nilpotence. I checked I is contained in the maximal ideal, so I^N=0, and (I^j/I^{j+1})^2=0 for j>=1. Step 2 cites the complete adic formal-smoothness definition: its square-zero lift applies to each continuous intermediate map; killing a tth power implies the next lift kills the 2tth power. Residue compatibility proves locality instead of assuming a lift is local. This finite induction starts at u and ends at A', including the isomorphism case N=1.

Step 3 cites the new node's exact local-square-zero conclusion and the same nilpotence leaf. I checked that the small extension in its hypothesis is an Artinian surjection, that the chosen residue identification is alpha composed with the inverse of the residue map of g, and that the marking on B' uses the quotient residue isomorphism. Thus the assumed h_C-surjectivity really applies; no larger residue field or separability hypothesis has been smuggled in. Locality gives continuity because the Artinian target's maximal ideal is nilpotent. The hypothesis S Noetherian holds with S=C.

Step 4 cites the adic definition to specify the arbitrary diagram being tested; the local-square-zero property has already been proved in step 3. I checked E is the inverse image of g(C), J is its square-zero ideal, its maximal ideal M satisfies M^{2t}=0, and the unit correction 1-j proves locality. The R-structure is local because its residue map factors the given local R->C and a residue isomorphism. Inclusion E->D converts the local lift into the requested arbitrary-ring lift. The zero-ring case is treated separately. This is the explicit elementary inverse-image construction of 0DYG (2) implies (1), not an uncited comparison theorem. Each proof step is below 2000 characters and contains no hidden additional theorem.

For small cases I checked fields C=k, the identity R=C, J=0, and the isomorphism p case. For a negative test, C=k[epsilon]/epsilon^2 over k fails the assumed lifting: the identity to C does not lift through k[t]/t^3 -> k[t]/t^2, since any lift of epsilon has square t^2 modulo t^3. Thus neither the item nor the new reduction silently declares singular complete rings smooth. Infinite-dimensional J is allowed only in the new node's conclusion, matching the source's product argument; no finite length is assumed for it. Completeness and finiteness of the residue extension are retained in the item although this ring argument does not need them.

Mathlib searches were run through msearch.py and their hits read. Smooth/Basic gives discrete formal smoothness (iff_comp_surjective at lines 371-374); Smooth/AdicCompletion assumes discrete formal smoothness before constructing lifts, and Smooth/Local's cotangent criterion at lines 34-40 concerns that same discrete notion. None states the new reduction or the item. The five new-node searches include all four required tools and a second semantic phrasing. Existing inherited item searches are preserved, and their exact queries were rerun where necessary so the local log supports them. No unrun search was recorded.

## Unfinished

The one new statement-only prerequisite joins the stage-1 queue, as required. No other part of the assigned split remains unfinished.
