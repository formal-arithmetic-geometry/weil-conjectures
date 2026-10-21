## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-sp-open-exceptional-scalar-locality.json` (statement, split; no exact Mathlib match), `citations.json`, and this report. The sandbox initially had no item copy or earlier report. The current repository item was copied and all its statement, source, provenance and earlier search records were retained.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. The proof uses existing lemmas rather than introducing another version of mate pasting, open counit normalization, or coefficient/composition coherence.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for exceptional/open/scalar comparisons did not locate a declaration of the whole assertion. The open exceptional inverse-image declarations concern the underlying open adjunction, not this equality of coefficient-change morphisms. Mathlib's `CategoryTheory.mateEquiv_counit` and `CategoryTheory.mateEquiv_hcomp` supply abstract categorical tools, but do not identify the specified geometric maps. Their source in `Mathlib/CategoryTheory/Adjunction/Mates.lean`, lines 123–132 and 209–217, was read. Searches through msearch.py are recorded verbatim in searches.jsonl and appended to mathlib_searches; both semantic phrasings returned unrelated module/scheme comparisons. None of these searches was unavailable.

WANTED: none.

The statement needs no correction. Its imported proof was empty. The blueprint Locality paragraph had compressed the proof into “transposes of composites are composites of transposes”; the delivery replaces that compression with the actual counit calculation. No statement or coefficient-category identification has been changed. The unnecessary Tate-line setup is retained because the item statement is unchanged; it is not used by the locality calculation. The broader imported det-sfb-coefficient-comparisons-exceptional claims invertibility and listed-coefficient compatibility and is not used: it would obscure the elementary argument and the arbitrary finite-ring normalization.

Nothing remains unfinished in this one-level split. The existing open-counit and coefficient/coherence nodes remain separate DAG obligations, as intended by stage 1.

## Blueprint and reuse searches

Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-lem-sp-reduction.json` and the current main-20261015 `sk-lem-sp-reduction-exceptional.proof.md`. This item serves the Locality paragraph in unit proof step 2, before checking smooth coordinate charts. The ancestor command identifies det-sp-reduction-exceptional. Whole-blueprint searches for mate, counit scalar and open restriction, together with DAG statement/key-word searches and inspection of the relevant nodes, found the existing open-counit and coefficient/composition assertions. No new nodes were needed. The same_as field stays empty: no other blueprint node states exactly this arbitrary-f coefficient-mate equality without an invertibility assertion.

## Not duplicates

No new nodes; there are no new/existing node pairs requiring a duplicate comparison.

## Review by Q10

I read the current blueprint Locality paragraph against the item, including the absence of a smoothness hypothesis and the specified choice of compactification comparisons. I also read the statements of every node used by the proof, rather than relying on their proofs: def-weil-pbc-composite-adjunction, lem-sp-et-proet-coefficient-compatibility, lem-sp-open-proetale-counit-scalar and det-sp-reduction-direct-image. For the categorical source I read Stacks categories.tex Tag 0DV0, label lemma-compose-counits, including its displayed counit formula. For the geometric route I read more-etale.tex Tag 0F7J, label lemma-shriek-composition, and Tag 0GL6, label remark-Rf-lower-shriek-change-of-rings. Those tags explain the underlying constructions; I do not claim they alone state the pro-etale normalization square. The existing coefficient-compatibility node explicitly supplies that stronger square.

Step 1 uses the composite-adjunction definition for the actual counit and the displayed composition/refinement clauses of lem-sp-et-proet-coefficient-compatibility for b_g = F_f(b_j) b_f. The latter node states the square with canonical compositors and common refinements, so the step is not choosing an arbitrary isomorphism between the composite functors. Its pro-etale input class is the etale-origin finite-Tor class used by the item's stipulated site/composition identifications. The item already fixes these identifications and the adjunction transfer; the proof does not assert coherence on all unbounded pro-etale objects.

Step 2 uses exactly the equation in lem-sp-open-proetale-counit-scalar at M = G_f,A K, with L = U_A M. That node has the same arbitrary finite commutative ell-primary coefficient map, separated finite-type setting and quasi-compact open immersion. It specifically concerns the actual pro-etale counit and the normalized compact-support map b_j. Its equation permits composing with b_j inverse; it does not require inverting c_f.

Step 3 expands the composite counit, applies naturality of the given counit v_B at the actual map c_f, and substitutes step 2 and the defining equation for c_f. The two citations are the composite-adjunction definition and the open-counit lemma already read. Everything else in that step is the displayed naturality equation or substitution of an identity from the item's hypotheses. In particular, the result has source F_f,B J_B T_U L and target T_Y K.

Step 4 uses the explicit naturality assertion in det-sp-reduction-direct-image at v_A,M: J_A L to M. The naturality square is written with the two b_f inverses, with their order checked. The composite-adjunction definition replaces epsilon_f,A F_f,A(v_A) by epsilon_g,A. The coefficient-composition lemma from step 1 identifies the remaining inverse factors with b_g(L) inverse. Thus the only cancellations are of b_f and b_j, whose invertibility is given; no flatness, finite projective dimension of B over A, or invertibility of an exceptional mate is used.

Step 5 uses the Hom bijection stated in def-weil-pbc-composite-adjunction. A bijection is injective, so equality of the two computed counit transposes is equality of the specified maps. This argument is elementary from that definition and the item's defining equation for c_g. It does not import an uncited uniqueness theorem. Every proof citation has an exact statement quotation in citations.json.

For B1–B10 there are no new statements needing searches, sources, or new definition dependencies. The original statement dependencies are retained and every proof dependency is the union of the five steps' uses. For C1/C4 the non-elementary geometric inputs are isolated in steps 1 and 2 and each appears verbatim in its cited node. Steps 3–5 are finite naturality, functoriality and injectivity calculations, not hidden lemmas. All five steps are below 2000 characters. For D1/D2 no clause was moved to a newly named equivalent assertion. The steps themselves carry the proof. No cycles are introduced by citing the parent exceptional-comparison theorem: that theorem is deliberately not used.

For section E I checked the quasi-compact open, all finite-type/separated scheme hypotheses, and both coefficient maps at each geometric application. The functors and right adjoints are precisely those assumed in the item, so M and L belong to their indicated finite-Tor domains. The algebraic test cases are j = identity (open counit and a_j become identities and the equality reads c_f = c_f), U empty (the two maps lie in the zero category), identity coefficient map (all coefficient comparisons reduce to unit identifications), and K zero (all displayed morphisms are zero). The calculation also remains typed for a nonflat map such as Z/ell^2 to Z/ell, because it never computes scalar extension by an underived tensor. None of these checks requires smoothness of f or any c_f inverse.

No mathematical defect or statement dispute was found. The correction made during self-review was to keep the inverse factors in the order b_f(J_A L) inverse followed on its right by F_f,B(b_j(L) inverse), precisely the reverse of the composition formula. The source, retained statement and canonical maps now agree at every substitution.
