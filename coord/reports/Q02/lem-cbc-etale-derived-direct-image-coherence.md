# Stage-1 report: lem-cbc-etale-derived-direct-image-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-etale-derived-direct-image-coherence.json`: statement, now split into eight proof steps. The statement is unchanged; added statement dependencies for injectivity and fibre products. No Mathlib match for the full item.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch output records, read before recording verdicts. Also retained all inherited Mathlib searches in the item.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All substantive inputs already exist in the DAG.

## Attachments

None claimed. The project source `WeilConjectures/SixFunctors/Etale/Derived/LowerShriekCoherence.lean:515–529` proves `AlgebraicGeometry.Etale.rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc`, but this is only the associativity clause, not the full item. I also read the normalization and identity interfaces in `Etale/Derived/UpperLowerStarCoherence.lean` and the generic `CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusComp.lean`. These support the proof but I do not treat an individual partial interface or a sorry declaration as an exact attachment.

## Literature wanted

None.

## Corrections and scope

The starting item had a statement and searches but no proof. Stacks 0D6E proves derived composition by uniqueness of right adjoints; it does not explicitly state the requested normalization or coherence equations. I supplied an agent-written bounded-below injective-model proof, with the exact normalization maps and both coherence calculations. The origin is therefore `agent`, not a claim that Stacks contains this expanded proof verbatim.

No statement dispute was found, and the mathematical statement is unchanged. The constant-ring module condition is essential to step 3; this proof does not assert that arbitrary structure-sheaf pushforward preserves injectives. In particular I rejected `lem-weil-pbc-module-pushforward-injective-acyclic` as the needed input: it concerns Zariski structure modules and gives acyclicity, not preservation of injectivity. The correct inputs are `prop-weil-pbc-inverse-image-modules-exact` and `lem-exc-rg-right-adjoint-preserves-injectives`.

I read the item's chapter and unit records and the ancestor's refinement/pasting paragraphs. The current main-20261015 blueprint places the ancestor in sec-six-functors-basics/sk-prop-sf-cbc; the inherited item's chapter/unit and blueprint ancestry have been retained as required. This item supplies ordinary direct-image coherence inside the ancestor's compactification comparisons; it changes neither the compact-support theorem nor its proof route. No SGA source is used.

## Unfinished work

None within this one-level split. The existing child nodes retain their own status. No Lean was written or compiled.

## Not duplicates

No new nodes were created. Searches of the whole DAG and blueprint identified the already existing injective-model tools; those are reused rather than restated. The blueprint searches for derived direct-image and composition/coherence did not find another blueprint node stating this entire normalization/coherence package.

## Review by Q02

I read Stacks `sites-cohomology.tex`, Tag 0D6E (lemma-derived-pushforward-composition), including its adjunction argument. For the expanded proof I read `derived.tex` Tags 013K (lemma-injective-resolutions-exist), 05TH (lemma-injective-acyclic), 05TI (lemma-enough-injectives-right-derived), 070I (lemma-K-injective), and 070J (lemma-bounded-below-injectives-K-injective); `homology.tex` Tag 015Z (lemma-adjoint-preserve-injectives); `sites-modules.tex` Tag 04JC (lemma-flat-pullback-exact); and `injectives.tex` Tag 01DU (theorem-sheaves-modules-injectives). There are no new-node sources to audit. I opened the statement of every cited DAG node and checked the following uses against it.

1. The direct-image definition explicitly gives the sectionwise formula for constant-ring module sheaves. The fibre-product node states uniqueness of a map with specified projections. These give the map a and its inverse, sheaf restriction naturality, and linearity. The direction is contravariant: F(a) goes from the composite direct image to the iterated image. This is a direct construction, not an unquoted comparison theorem.
2. The same fibre-product statement proves equality of the two maps by their projections to V and X. Applying the sheaf functor yields the associativity equation, and the two unit maps reduce to the identity map on the fibre product. No omitted associativity lemma is needed.
3. Clause (3) of the inverse-image proposition states both exactness and the module adjunction for constant coefficients. The adjoint-preserves-injectives node assumes preservation of monomorphisms, which exactness supplies. Thus it applies to arbitrary scheme maps with this same coefficient ring. The direct-image definition supplies additivity. Neither properness nor a flat scheme map is assumed.
4. The enough-injectives node is explicitly about sheaves of modules over the constant ring on the small etale site, so it gives the hypothesis of the generic right-derived node. That node states existence of the natural alpha and its invertibility on bounded-below complexes of injectives. Step 3 supplies that hypothesis also for f_*I. The displayed t and D formulas have the required source and target, and every factor is invertible. Naturality is ordinary substitution of the cited naturality equation and the comparison constructed in step 1.
5. The injective-representative node gives both a representative and K-injectivity. The K-injective-Hom node explicitly gives the Hom bijection in D+ as well as D. It therefore represents the transition between two resolutions and any input morphism by a homotopy class. Substituting e=e'Qk in the conjugation formula proves independence, and the same equation proves naturality. This is a few-line consequence of those existing statements, not a new unsplit lemma. Naturality at e also proves the normalization uniqueness.
6. The derived computation node applies to the identity edge and gives the inverse alpha used in the formula for d_T. The two representative/Hom nodes have the same hypotheses as in step 5 and extend this formula. Identity comparison on sheaves is exactly the one constructed in step 1.
7. I expanded both associativity paths, rather than asserting compatibility of unnamed identifications. The naturality equation for alpha^h moves c_{g,f} across its computation map. Naturality of d_{h,g} at alpha^f, followed by its formula on f_*I, gives the second expansion. Both have the same outside factors t and the inverse alpha^{hgf}; their middle factors are exactly step 2's equality. The representative node lets equality extend to every object by naturality. All intermediate injectivity conditions come from step 3.
8. The left identity uses naturality of d_Y at alpha^f; the right identity uses naturality of alpha^f at u_X. The displayed two middle factors are precisely the underived unit composites from step 2. Their cancellation gives actual identities of natural transformations, not merely isomorphism classes of functors. Again injective representatives extend the calculation.

For B–E of delivery-errors I checked self-contained objects, real source labels, single TeX escaping, existing-node reuse, actual searches, acyclic dependencies via server checks, and explicit formulas for every comparison used. No non-elementary source fact is cited only by a tag. The off-unit exactness and enough-injectives tools are declared in split_report.tool_uses; Mathlib injective/Hom/derived tools and notion definitions are reused in their existing form. Every proof step is shorter than 2000 characters, and the conjugation and cancellation steps contain their full routine arguments.

Edge cases checked: a zero ring or empty scheme gives zero/terminal module data and the same formulas; an identity edge gives exactly u_T and hence the two stated unit equations; arbitrary negative lower bounds stay lower bounds because additive direct image sends zero to zero. Arbitrary nonproper and nonfinite-type scheme maps are allowed throughout. No boundedness-above, constructibility, coefficient torsion, residue-characteristic or coefficient-invertibility condition appears in any application.

The preliminary server review_split check passed with 0 new nodes. Required deliver.py dry-run and push results are recorded by the delivery tool.
