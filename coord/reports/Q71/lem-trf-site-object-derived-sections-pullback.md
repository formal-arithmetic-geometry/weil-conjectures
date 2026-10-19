# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-site-object-derived-sections-pullback.json`: item, statement, split; no Mathlib match. The mathematical statement is unchanged. Added the definition citation for cocontinuity, which the original statement used without a corresponding definition dependency.
- `dag/nodes/sec-trace-formula/lem-trf-site-pullback-injective-evaluation-acyclic.json`: one new statement-only node, unsplit; no Mathlib match. This is Stacks 0D6X for abelian sheaves, not the derived comparison itself.
- `citations.json`: verbatim statement excerpts for every node cited by every numbered proof step.

## Attachments

None for the item or the new node. Searched the slopmaster2 `WeilConjectures/` source by the exact blueprint tag and item id, by continuous/cocontinuous, derived sections, same cohomology, and injective evaluation concepts. The pro-etale-specific `isZero_rightDerived_sectionsFunctor_of_upperStar` in `SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean` concerns localization for a scheme object and only a vanishing implication; it does not state the arbitrary-site derived comparison. Its other comparison-upper-star theorem uses a sorry. Neither supplies an attachment. The existing generic right-derived acyclic-unit node already records `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`, so no duplicate source-attachment node was made.

## WANTED

None. All sources used are present locally.

## Faults found and repairs

The original item was statement-only. Its mathematical assertion agrees with Stacks 0DD8(1), restricted to the bounded-below case, and needs no finite-limit preservation of the site functor beyond continuity as defined for covering fibre products. It does not need the stronger fibre-product condition on the lower-shriek functor from the immediately preceding total-acyclicity result. I added only a citation to clause (1) of `def-weil-pbc-special-cocontinuous-functor`, which actually defines cocontinuity; clauses (2)(c)--(e) and an equivalence of topoi are not assumed.

The ordinary pullback map on derived sections is written in the opposite direction to the arrow in the item. The item already asserts an isomorphism, so its displayed comparison is the inverse of this canonical map. Step 4 now specifies that normalization explicitly on an injective representative, rather than silently identifying two cohomology objects. No hypothesis or conclusion was changed.

## Unfinished work

The new node is deliberately not split: it gives only injective evaluation acyclicity (0D6X), with no proof or proof dependencies. Its later split can follow the source's covering Cech complexes, injective Cech vanishing and the Cech-to-derived vanishing criterion. The item itself has a complete four-step argument. No Lean was written, no compiler or Lake was invoked, and no shared project or launcher file was changed.

## Searches and duplicate review

I searched all DAG chapters for `0DD8`, `0D6X`, `lemma-pullback-injective-pre-limp`, pre-limp, continuous/cocontinuous inverse images and injective evaluation acyclicity. I also ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for derived-section comparisons, pullback-same-cohomology, `0D6X` and pullback injectives; the keyword searches returned no blueprint equivalent of either statement. Searched the current `main-20261015` and historical blueprint texts for the same comparison. The current smooth-curve unit statement and its normal-cone ancestry were read and retained.

The existing continuous-cocontinuous adjunction node supplies the underived formula and is reused. Existing pro-etale/etale comparison acyclicity nodes concern specific comparison morphisms, not an arbitrary continuous-cocontinuous site functor. The existing direct-image-injective evaluation-acyclicity node is about a **direct image** along a ringed-site morphism; this helper concerns an **inverse image** and is not its specialization. The new node has no existing same-0D6X-tag pair.

For both statements I ran msearch LeanFinder, LeanSearch, Loogle and grep, plus a second semantic phrasing before concluding no match. All new records are copied from the actual `searches.jsonl` entries. Hits for `sheafAdjunctionCocontinuous` were read in Mathlib `CategoryTheory/Sites/CoverLifting.lean` around lines 290--345; they give the adjunction and its unit, not evaluation-cohomology vanishing. `isLocallyInjective_whisker` was read in `PreservesLocallyBijective.lean` around lines 25--68; local injectivity of a natural transformation is not injectivity of an object in an abelian category. The second phrasing returned cover-density equivalences with extra hypotheses and the cohomology-presheaf definition, neither of which supplies the new lemma or the item. No Mathlib leaves were claimed.

## Not duplicates

There is no existing node carrying the new node's source Tag 0D6X. Conceptual near hits:

- lem-trf-site-pullback-injective-evaluation-acyclic vs lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic: inverse image under a continuous-cocontinuous site functor versus direct image under a ringed-site morphism; neither functor or variance is the same.
- lem-trf-site-pullback-injective-evaluation-acyclic vs sk-lem-pe-injective-acyclicity: all arbitrary site objects and evaluation cohomology versus the particular etale/pro-etale comparison and its derived direct image.
- lem-trf-site-pullback-injective-evaluation-acyclic vs lem-trf-site-object-derived-sections-pullback: an individual injective sheaf's positive cohomology vanishes versus a canonical natural comparison for every bounded-below derived object. The item proves the comparison using the helper and Leray; it is not an application of a newly named copy of its own conclusion.

## Review by Q71

I read `sites-cohomology.tex` Tag 0DD8, label `lemma-pullback-same-cohomology`, including the bounded-below proof sentence, and Tag 0D6X, label `lemma-pullback-injective-pre-limp`, including its full Cech proof. The new node is exactly the latter's specialization to the integer ring sheaf: abelian sheaves and integer-module sheaves have the same objects, morphisms and injectives, because the integer action is determined by addition. The item takes only part (1) of 0DD8 and only bounded-below objects; it adds no finite-connected-limit, ring-flatness, torsion, coefficient finiteness, or common-annihilator hypothesis. I also read Sites 00XR (`lemma-when-shriek`) and Derived Categories 015E (`lemma-leray-acyclicity`) and 05TI (`lemma-enough-injectives-right-derived`). The proof follows the bounded-below route actually specified in 0DD8, not its unbounded lower-shriek/derived-Hom route.

For step 1 I opened `lem-weil-pbc-continuous-cocontinuous-topos-adjunction` and checked both its explicit formula for L and its conclusion g inverse = L. Its statement is about sets; I wrote out how addition, zero and negation give the identical abelian formula. I did not take abelian exactness from that set-only statement. I opened `lem-pe-constant-left-module-inverse-image`: its statement expressly gives exactness and termwise bounded-below derived inverse image for every constant unital ring. With the integer ring this supplies exactly the abelian exactness needed. The sheaf categories are small-site categories in the common universe, so its site and coefficient hypotheses hold. The underived evaluation identity is consequently an identity of additive functors, not just a bijection of underlying sets.

For step 2 I opened the site-sheaf enough-injectives node, the Mathlib injective-representative node and the right-derived-plus-injective node. The first applies to both sites without a terminal object. Clause (1) of the second gives a complex of injective terms with the chosen lower bound, not merely an unbounded K-injective representative. The third supplies existence of ordinary right derived evaluation, its **natural** comparison unit, computation on bounded-below injective complexes and uniqueness. These are all in those statements. Step 1's exactness makes the termwise pullback a representative of inverse image. Zero terms below the bound stay zero since the functor is additive.

For step 3 I compared the new node's statement literally with the hypothesis used: each I^n is injective on D, and the same u is both continuous and cocontinuous; the conclusion is precisely H^p(U,LI^n)=0 for p>0. I opened `def-weil-pbc-sites-and-cohomology` and checked that it defines H^p as R^p of additive left-exact evaluation. I opened `src-right-derived-functor-plus-acyclic-unit` and read the associated source theorem in slopmaster2 `PlusHomology.lean`: it states that the **canonical unit** is an isomorphism on a bounded-below complex of acyclic objects, with no Grothendieck condition. This avoids using a theorem that only compares numerical homology groups or requires an unstated Grothendieck hypothesis. I wrote the chain-map equation for e against every differential; localizing a chain isomorphism and composing the computation isomorphisms is elementary.

For step 4 the cited right-derived-plus-injective statement explicitly includes the natural transformation and uniqueness of its normalization. The acyclic-unit node specifies that same unit. On r:LI -> J, its naturality equation identifies its canonical comparison with Gamma(U,r), followed by the injective computation. Thus the explicit e-inverse followed by Gamma(r) is the ordinary pullback of sections, and the constructed arrow is its inverse as required by the displayed direction. Naturality follows from the natural units and e, including after changes of representative; it is not asserted from equality of cohomology groups. I copied verbatim statement portions for every use into `citations.json` and checked they are substrings of the actual cited statements.

For the B--E checks, the single new node introduces all objects and hypotheses, gives only a statement, defines its cohomology through the existing definition node, cites the correct Stacks tag and label, carries all blueprint ancestry and no proof sketch in its statement. It is smaller than the derived comparison: only acyclicity of individual injectives is deferred. No duplicate or clause-restating helper was created, and no Cech comparison proof is smuggled into an elementary step. Every proof step is under 2000 characters (714, 695, 769 and 960 on initial writing), so none of the long-step checks hides an extra lemma. The off-unit uses are declared as generic tools in `split_report.tool_uses`, not as maintainer-owned accepted tool uses.

I tested the statements on u = identity (injectives are evaluation-acyclic and the comparison is identity), zero M, an injective sheaf in degree zero, and arbitrary shifts of such a sheaf (the chosen lower bound can be negative). I checked the empty category/site (no U, so the assertion is vacuous) and an object admitting an empty cover (all abelian sheaf sections at that object, and therefore both evaluation functors, are zero). The construction never assumes global sections of a terminal object or exactness of evaluation. The stronger total-acyclicity lemma immediately before 0DD8 has an additional fibre-product hypothesis on g_!; I explicitly did not use or assume it. No statement dispute or source error remains.

The first dry run rejected four citation excerpts solely for being under its 40-character minimum. I replaced each with the full verbatim cited statement; no mathematical step changed.
