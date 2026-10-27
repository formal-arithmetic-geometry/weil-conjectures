# Stage-1 delivery: lem-sfb-flat-fp-purity-open (Q56)

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-fp-purity-open.json`: existing statement, unchanged; seven-step split of Stacks 05MC; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-fibre-projective-etale-cover.json`: new statement-only node, Stacks 05KW; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-purity-etale-assassin-criterion.json`: new statement-only node, Stacks 05L4; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-purity-flat-point-descent.json`: new statement-only node, Stacks 05J9(1); no Mathlib match.
- `citations.json`: one entry per step/node citation, quoting the complete verbatim statement to include all hypotheses and the precise clause used.

## Attachments

None. Searched `lean/WeilConjectures` by item tag, purity/open keywords, relative/universal purity, and projective etale neighbourhood terminology. No declaration states the item or any of the three new inputs. The projective-module lifting and smooth-purity declarations found concern different assertions. No Lean was written, compiled or built.

## Literature

No WANTED source. Read `literature/stacks-project/flat.tex`, Tag 05MC (lemma-flat-finite-presentation-purity-open), statement and complete proof. Read the statements and surrounding proofs of 05KW (lemma-finite-presentation-flat-along-fibre), 05L4 (lemma-criterion), and 05J9 (lemma-flat-descend-pure). Read 05K6 (lemma-affine-locally-projective-pure) and 05MD (proposition-finite-presentation-flat-pure-is-projective), which support the reused projectivity/purity equivalence. Read `more-morphisms.tex` 05KR (lemma-relative-assassin-constructible), and `morphisms.tex` 05LW (lemma-constructible-containing-open). Confirmed each tag against `literature/stacks-project/tags/tags`.

The current blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its proof file. The direct-image/compactification paragraph is the inherited ancestor route. The item's recorded chapter/unit and its supporting stable-moduli/flattening ancestry were retained; `blueprint_refs.py ancestor` actually returns None for this preexisting chain. New nodes inherit this null ancestor and prepend the item to `via`, rather than inventing an ancestor. Searches of the entire imported blueprint for 05MC, 05KW, 05L4, 05J9, 05LW, pure along, relative assassin, flat purity, purity descent and projective fibre found no blueprint statement to reuse. Broader purity/projective searches were also read; their hits concern other notions or hypotheses.

## Problems and corrections

The imported statement is correct and stays unchanged, including finite presentation and the absence of a Noetherian hypothesis. Its proof was empty. The source's last application of 05L4 is compressed: an arbitrary point of an elementary etale neighbourhood need not have the same residue field as its image. Step 6 applies the criterion to the base-changed family with the identity elementary neighbourhood, and step 7 uses pointed flat descent. It does not pretend all the points of the original etale neighbourhood are elementary over their images.

The source's 05MC proof says W once for W-prime; the split consistently names W as the image in the fibre product Y. It proves W quasi-compact over the base using images of preimages of affine opens, rather than merely asserting it. The 05LW conclusion is proved in three lines from existing spectral-space and constructibility statements, so no duplicate neighbourhood lemma is added. No statement dispute and no change of the chapter or unit route.

## Mathlib searches

For the item and each new node, ran the logged `msearch.py` leanfinder, leansearch, loogle, and grep searches, plus a second semantic phrasing. The exact queries, outputs and verdicts are in each node and the unaltered `searches.jsonl`; full outputs are retained in sandbox text files. All services answered. None is recorded unavailable or claimed to match.

The plausible projectivity hit `Module.Flat.projective_of_finitePresentation` was checked at Mathlib/RingTheory/Flat/EquationalCriterion.lean:287 (also verified by a logged grep). It requires finite presentation over the same base ring over which projectivity is concluded. Here sections need only be finitely presented over the source algebra; e.g. the section module of the structure sheaf of an affine line over a field has infinite base dimension. Thus this is not a one-line specialization of Mathlib. Free-locus openness, smooth/etale loci, openness of flat finitely presented morphisms, faithful flatness, going down and etale permanence likewise do not state fibrewise purity or construct its chart. The Loogle Pure/Flat hits concern iterator operations, and Pure/IsOpen concerns a pure filter, not this notion.

## Not duplicates

lem-sfb-flat-fibre-projective-etale-cover vs lem-sfb-finitely-presented-flat-point-projective-etale-neighbourhood: 05KW occurs in the latter's proof/review, but its statement gives a chart around one point; the new node covers the entire fibre by an affine etale source with projective sections. The existing node cites this item, so it cannot replace the new input.

lem-sfb-flat-fibre-projective-etale-cover vs lem-sfb-flat-point-projective-etale-source-chart: the existing statement is the pointwise 05ID input, with a chosen source point and residue-field isomorphism; it does not provide coverage of a whole quasi-compact fibre, and mentions 05KW only as context.

lem-sfb-flat-fibre-projective-etale-cover vs lem-trf-flat-algebra-etale-projective-neighborhood: the existing algebra assertion treats only the structure algebra at a single prime; the new result treats a general finitely presented sheaf and covers a whole fibre.

lem-sfb-purity-etale-assassin-criterion vs lem-sfb-affine-flat-fp-projectivity-purity: the latter is a projectivity/purity equivalence on an affine source and base, not a criterion comparing a pure etale source chart with associated points of an arbitrary finite type family.

lem-sfb-purity-flat-point-descent vs def-sfb-scheme-relative-purity: the definition gives the absence of impurities; it does not assert flat descent. Whole-DAG searches found no existing statement of 05J9 or 05L4. No new node restates openness or a clause of the item.

## Review by Q56

I reviewed all of delivery-errors B through E against the actual files and sources, not just the field shape. The three new statements introduce their schemes, morphisms, sheaves, fibre points and coefficient rings and cite definitions for the notions used. They contain no proof steps or hidden proof sketch. Each is a proper input in the 05MC proof, not an openness assertion transferred to a new name. Sources use Stacks tags and labels, TeX is encoded once, and the new statement dependency lists match their bracketed definitions.

Step 1 uses the full statement of the new 05KW node. Unlike the pointwise existing chart lemma, it expressly gives coverage of X_s and projectivity over the base sections. Flatness on the entire fibre follows from the item's global flatness assumption. No purity assumption is needed for this construction.

Step 2 uses the statements of pullback quasi-coherence and pullback finite presentation for G, the definition of etale for local finite presentation, composition of locally finitely presented morphisms, the over-base local finite presentation lemma, and affine qcqs plus morphism permanence for finite presentation of p. All these statements were opened. Projective-module flatness and the affine chart relative-flatness equivalence supply exactly the extra flatness hypothesis in the existing affine projectivity/purity node. That node expressly includes projective implies universally pure, without finite generation over the base. The directions actually used were checked against 05K6 and 05MD; no proof of that existing node is being used as its statement.

Step 3 uses etale base change for Y to X and cancellation for h, and etale openness for W. Its quasi-compactness argument is written out on each affine base open using the quasi-compact p obtained in step 2. Finitely presented base change and both sheaf pullback permanence statements give precisely the hypotheses of the existing scheme assassin constructibility node, whose statement requires an affine base and a quasi-compact open over it. S-prime is affine; no unjustified Noetherian inference occurs.

Step 4 uses 05L4 at the original elementary neighbourhood. Its finite type, relative flatness, source purity, etaleness and associated-point coverage hypotheses have all been obtained. The definition of relative assassin expressly gives its union of fibrewise associated points, hence identifies the criterion's conclusion with generalizations lying in E.

Step 5 uses affine qcqs and spectrality, the Boolean complement clause of constructibility, and the proconstructible closure-specialization statement on a one-element family. Every one of these statements was read. A point in the closure of C would specialize from an element of C and contradict step 4. Taking the complement of the closure gives the neighbourhood. This is an elementary assembly of the cited facts, not a new theorem being left uncited.

Step 6 uses relatively flat module base change for F_Y and the same criterion, now with the identity elementary neighbourhood at t. The pullback-composition statement identifies h-star F_Y with G; I added that citation during review so this identification is not hidden. The chart sheaf is pure along every fibre by step 2. Membership t in E gives coverage of associated points, and stability of the open V under generalization gives the criterion's right-hand containment. Neither field extensions nor fibre associated points are silently identified across an arbitrary base change here.

Step 7 uses the flatness included in the etale definition, the exact pointed descent assertion of 05J9(1), and etale openness. Descent needs only a flat point above the chosen base point, so arbitrary residue extensions at t are permitted. It then produces an open neighbourhood e(V) inside the purity locus, which proves openness.

I checked the zero sheaf, empty source/fibre, identity base change, and a field base. With F zero the assassin sets are empty and purity is vacuous; E is the whole base. Empty fibres impose no false nonemptiness demand on the chart. With identity base change the descent and criterion statements specialize without adding hypotheses. A field base illustrates why projective sections need not be finite over the base. No new statement asserts finite rank, Noetherianity, or purity of a morphism in place of purity of a module. Each proof step is under 2000 characters; there is no long step hiding an additional lemma.

Off-unit citations are generic scheme, module or topology tools and are declared individually in split_report.tool_uses, with the identifications they supply. No unit realization is edited because this item is a supporting input rather than the unit's key statement.

## Unfinished work

No portion of this item's assembly proof remains unfinished. The three new inputs are deliberately statement-only stage-1 items for later splitting. Independent maintainer review remains part of the delivery process.
