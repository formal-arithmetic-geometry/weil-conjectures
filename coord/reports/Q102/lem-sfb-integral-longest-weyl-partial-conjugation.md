# Stage-1 delivery: lem-sfb-integral-longest-weyl-partial-conjugation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-longest-weyl-partial-conjugation.json: item, statement retained, five proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-simple-reflection-gauss-chart.json: new statement-only node, unsplit; no Mathlib match. It supplies one simple-reflection Gauss chart with its coordinate-support refinement, not the longest-element construction.
- citations.json: verbatim statement excerpts for every step/node citation.
- searches.jsonl: search-command log; all searches read, including the second semantic phrasing.

## Attachments

None. Searched the live project WeilConjectures/ for the item id, longest Weyl, partial conjugation, Chevalley and Weyl/root-calculus terms. No project declaration gives the item or the new chart. Mathlib's RootPairing.weylGroup, reflection and GeckConstruction.ωConj concern root-pairing automorphisms and conjugation of matrices as a Lie algebra, not these integral schemes. Read WeylGroup.lean lines 49--105, GeckConstruction/Basic.lean lines 374--410 and the returned Base/reflection signatures. They do not give this theorem in one specialization.

## WANTED

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.220--222, for the item and lem-sfb-integral-simple-reflection-gauss-chart. Read these pages online; no local copy was present. No download or literature edit was made. No Stacks tag states this specialized root-coordinate calculation. The generic-fibre uniqueness node already states the scheme-theoretic result used here; its existing source is Stacks Tag 01RH.

## Problems found and corrections

The item already corrects the source paragraph that identifies a product of every simple reflection once with the longest element. In type A2, s_a s_b sends a to b, so does not reverse the positive roots. The item also already distinguishes n-conjugation from inverse n-conjugation, whereas the displayed source statement repeats n. I retained these corrections and every clause of the item; there is no new statement dispute. I did not import the source's deferred proof or consult its prohibited reference. The proof follows Conrad's rank-one calculation and supplies an independent explicit word-domain induction.

The important missing argument was containment of the whole E_+ and E_- in the iterated domains. Containment of the root axes alone does not imply it. The new smaller chart has an explicit positive-system support assertion, which is precisely what this induction needs. No global integral root model, opposite-sign multiplication, envelope, or construction depending on this item is used.

The blueprint ancestry is already null at the nearest imported ancestor. I preserved that value and the full existing via chain rather than inventing an imported id. Read latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md and its direct-image route; the new prerequisite serves the existing from.place chain. Blueprint searches for Weyl, simple reflection, conjugation, Gauss and root, and DAG searches by the same terms and 6.3.8/6.3.9, found no imported duplicate.

## Not duplicates

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-integral-longest-weyl-partial-conjugation: one simple reflection and its coordinate support, versus construction of a longest word, two domains containing whole one-sign groups, inverse maps and group compatibility. The item proves the word induction; the new node does not state any longest-element clause.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-rank-one-normalized-gauss-chart: the existing node concerns an actual rank-one reductive group over the base; the new node works on the explicit full-root product scheme over Z without an ambient integral group and controls mixed positive-system coordinate subspaces.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-split-root-subgroup-weyl-calculus: the existing node assumes a reductive group over the base. Here only the rational group and the two separate integral one-sign groups are available; no integral opposite-sign law or reductive model is assumed.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-rational-chevalley-one-sign-integrality: the existing node gives one-sign laws and rational rank-one identities. It does not give a mixed-sign chart over Z, its domain, or invariance of the mixed coordinate-support subschemes.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-chevalley-integral-rank-one: the existing statement constructs a representation of SL2 over an algebraically closed field using an admissible lattice; it does not address this given rational realization or its integral product chart.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-integral-chevalley-weyl-atlas: that statement is about the closure model and its atlas, not a rank-one partial conjugation on the separate root-product scheme. Using it here would assume an ambient model before construction.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-relative-block-gauss-chart: block matrix factorization of arbitrary GL schemes does not provide the root-coordinate chart or support preservation on this product of root groups.

lem-sfb-integral-simple-reflection-gauss-chart vs lem-sfb-longest-weyl-open-cell: the existing result is over an algebraically closed field and gives a Bruhat open immersion, with no integral chart or domains.

## Review by Q102

I read Conrad's printed pp.220--222 online, including the coordinate reordering (6.3.4), the opposite-simple-root denominator, and the short word-induction paragraph. For the new node I checked the actual rational Gauss identity and signed parameters in the existing one-sign integrality statement, rather than assuming a full integral group. The chart can be built by putting the negative simple axis last and the positive simple axis first. Conjugation leaves the remaining roots in their respective signs; applying the rational rank-one formula to the middle pair uses only 1+vu chi_a(t). Its inverse is an actual localized integer coordinate function, and the remaining operations are the given one-sign laws and torus action. The square n_a^2=a^vee(-1) is a rank-one assertion in this smaller prerequisite, not an unproved elementary inference left in the item. An early scratch derivation of that square from a rearranged Gauss identity was not correct; I removed it and kept the square in the rank-one prerequisite where its proof belongs.

The support refinement is a genuine additional input of that new node, not an argument silently ascribed to the source's bare statement. Its mathematical reason is as follows (recorded here as research, not as a proof inside the new unsplit statement). A Weyl-translated positive system P contains no opposite pair and is closed under sums that are roots. One-sign reorderings are torus-equivariant polynomial maps. Their coordinate of weight gamma is a sum of monomials of that weight. A sum of roots in P cannot equal a root outside P, by the positive functional defining P. Hence those maps preserve the coordinate subspaces in question. On C_P the torus is 1 and at least one of the a,-a coordinates is zero, so the Gauss denominator is 1 and its torus correction is 1. Signed reflection and one-sign collection therefore take support P to support s_a P. The cube of the same partial chart gives its inverse on these subspaces since n_a^4=1, with equality checked on their torsion-free polynomial coordinate rings. This explains why this is a smaller rank-one lemma and how a later worker can prove its support clause.

For Step 1 I opened the finite-root-datum Weyl-group node: it explicitly states finiteness for exactly the lattice reflection group at issue. The simple-reflection subgroup is consequently finite. The coefficient argument proves the needed permutation of all other positive roots, and maximization then proves the existence of a word reversing all signs. There is no assumption of a rational conjugator over an algebraic closure or descent from one, and no silent use of a Coxeter presentation.

For Step 2 I checked the new chart's statement for its torus map, normalizer representative, full C_P containment, and support isomorphism. It gives every feature used by the recursion. The recursive inverse images really are open domains, and its induction begins with C and the two original sign groups. Each whole intermediate support scheme remains in the next domain, which is stronger than preservation of each root axis. The final product order is n_{a_r} ... n_{a_1}, consistent with the order of conjugation composition.

For Step 3 I checked the new chart's square identity and support clause. The cube is defined on its recursive open, not asserted globally. Applying the support clause three times keeps every C_P in the whole cube domain. The fourth-power identity then makes this the inverse rational conjugation. Reversing the list of letters yields n^{-1}, not a second copy of n. The proof does not require n^2=1 or the false assertion that all simple representatives commute.

For Step 4 I opened lemma-nagata-ext-scheme-theoretically-dominant-separated and quoted its exact separated-target uniqueness sentence. C and the one-sign groups are affine, hence separated; all sources of the compared maps are open in Laurent-polynomial schemes over Z, with torsion-free coordinate algebras and scheme-theoretically dense rational fibre. This applies both to homomorphism diagrams with variable pairs and to the two compositions on their actual inverse-image domains. Thus preservation of group laws is proved on whole schemes, not merely on characteristic-zero points. The support maps put the final images inside whole E_+ and E_-; these are contained in the inverse domain, so the composition identities make the subgroup maps inverse.

For Step 5 I opened the one-sign integrality node and verified its zero identity, and the new chart for its fixed identity section. The zero-root case forces M=0 under the spanning hypothesis, so all indicated maps are identities on Spec Z. In rank one the mixed chart has d=1+vu chi_a(t) and contains both whole sign axes. In type A2 a true longest word has three letters, and the support induction remains defined even when intermediate supports mix signs; this tests the exact failure of the source's two-letter word. Bad characteristics 2 and 3 create no issue: signs may coincide but remain units, and on every C_P the only denominator is 1. No reducedness of test algebras is used. I did not add a condition on the item or drop any conclusion.

I checked delivery-errors B--E against the files: the new statement introduces all objects and references the given definition nodes; it has no proof or proof dependencies, all logged searches are actual searches, no Mathlib candidate was promoted without a match, every item citation quotes the statement it uses, and neither a duplicate, a source reference, nor the proof of another node substitutes for a cited lemma. I checked the dependency closures of the cited inputs for a path back to the item and found none. All five proof steps have fewer than 2000 characters. The scheme uniqueness lemma is declared as a generic tool use in split_report; it is not a change to the unit route.

## Unfinished work

No part of the item's assembly proof remains open. The new rank-one chart is deliberately statement-only and unsplit, as required by the one-level stage-1 contract. No Lean was written or compiled, no git command was run in the shared repository, and no file outside the authorized sandbox was edited.
