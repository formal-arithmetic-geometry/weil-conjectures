# Q23: lem-sfb-space-sum-extension-geometric-stalk

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-sum-extension-geometric-stalk.json: statement, split into five steps; statement unchanged; no Mathlib match for the whole formula.
- dag/nodes/sec-six-functors-basics/lem-sfb-site-point-abelian-sheafification-fibre.json: statement, Mathlib leaf. CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso, Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean:281, specialized to AddCommGrpCat. The actual unit-map isomorphism is at lines 272-275 and the component formula at lines 283-285.
- citations.json: one exact statement quotation for every citation in each numbered proof step.
- searches.jsonl: actual msearch results; no fabricated searches. prepare.py is a sandbox-only JSON preparation script, not a project or launcher edit.

## Attachments

None. Searches of WeilConjectures for the item tag, extension/sum/stalk terminology, and the generic fibre/sheafification names found no project declaration stating the item. The finite-etale constant-coefficient formula is not this arbitrary representable-etale structure-module statement. No Lean was written or compiled.

## WANTED

None. All sources used are present locally.

## Findings and changes

The live item was unsplit and had no proof or Lean declaration. The sandbox initially contained only dispatcher markers, so I copied the live item and retained its statement, old searches, citations in the source field, and inherited blueprint provenance. There is no released repair note for this item.

I read sites-modules.tex, the whole statement and proof of 0710 (lemma-stalk-j-shriek), and spaces-perfect.tex, the Mayer–Vietoris introduction through 08GU and its preceding restriction formula. The source's “O_X-module” typo at the introduction to 08GU is already correctly recorded in the item source: the input lives on Z. This delivery changes no statement and raises no new statement dispute.

The general site-point sheafification comparison is a distinct tool. I read sites-modules.tex 04EP (lemma-stalk-exact-abelian), especially (3), and the stalk construction immediately before it; I also read sites.tex 00Y8 and its adjunction proof as corroboration. I read Mathlib's Point/Skyscraper.lean lines 245-290 and the point/colimit definitions in Point/Basic.lean. Unlike the older online search result putting the instance in Basic, this checkout has the comparison in Skyscraper. The final grep over the directory verifies its actual file and line; earlier single-file grep results misparse the filename because rg omits the filename for a single file, and are not used as line evidence. The new leaf records the verified directory grep. Products and small colimits in AddCommGrpCat and the assumed abelian sheafification discharge the generic declaration's hypotheses directly.

I read the chapter record and unit record and the current latest blueprint unit sk-thm-sf-ctf-stability. This is the inherited supporting calculation on its direct-image/alteration route, not a replacement of that route. The ancestor tool returns null for this inherited created-node chain; I retain it and prepend the item to the new leaf's via list. Whole-blueprint searches for sum extension, stalks, localized, stalk sheafification, sheafification, cofiltered, pointed etale, neighbourhood, site point, point fibre, etale restriction, sheafification fibre, and 04EP found no blueprint node giving the new general abelian-presheaf statement. The existing normalized space sum-stalk theorem depends on this item; citing it would be circular. The existing scheme/constant-coefficient sum-stalk theorem does not cover structure modules on algebraic spaces.

Exploratory logged searches also tested whether an etale-neighbourhood initiality lemma would be needed. It is not used and no such node is created: the direct-sum comparison and its inverse follow directly from the colimit and direct-sum universal properties. In particular the proof does not insert the whole formula as a new auxiliary lemma. The original item's searches provide multiple phrasings for the full formula; the new msearch calls reconfirm the lack of an exact match. The leaf's searches find the actual more general Mathlib comparison.

## Not duplicates

lem-sfb-site-point-abelian-sheafification-fibre vs lem-weil-pbc-sheafification-geometric-stalk: the existing statement assumes the small etale site of a scheme and its pointed geometric neighbourhoods; the new statement covers an arbitrary small site and site-point functor, needed for an algebraic-space site.
lem-sfb-site-point-abelian-sheafification-fibre vs lem-weil-pbc-sets-sheafification-geometric-stalk: the existing statement concerns set presheaves on a scheme's etale site; the new statement concerns abelian presheaves at an arbitrary site point.
lem-sfb-site-point-abelian-sheafification-fibre vs lem-cbc-proetale-sheafification-geometric-stalk: the existing statement is for the small pro-etale site of a scheme; the new statement has no scheme or pro-etale restriction.
lem-sfb-site-point-abelian-sheafification-fibre vs lem-trf-site-point-fibre: the existing statement identifies fibres of sheaves with constant coefficients and assumes finite limits of the site; it does not assert that the sheafification unit of an abelian presheaf induces an isomorphism.
There is no existing node citing source Tag 04EP. No new node restates a clause of the item: the single new node is a general Mathlib sheafification tool with no etale morphism, structure ring, or sum-extension assertion.

## Review by Q23

I checked delivery-errors B–E with the actual statements and sources open. The new node is self-contained: it specifies its universe, site, point functor, category of elements, covering-lift condition, presheaf, colimit, sheafification and comparison on representatives. It has no proof steps or proof dependencies. Its generality is directly that of the Mathlib theorem, specialized once to abelian groups; it is not an unproved identification with a different definition. The only new source tag is 04EP, checked against the tags table and the local lemma label. TeX is written with ordinary single TeX backslashes after JSON decoding.

Step 1 uses the full ringed-site localization statement of lem-trf-space-enlarged-etale-ringed-site-model and the full inverse-image-at-geometric-point statement of lem-sfb-space-geometric-points-conservative. The first identifies the inverse image of the actual structure ring with O_Z, not merely an abstract equivalent category. The second identifies its stalk with O_X at the image point and explicitly includes canonical ring maps and algebraic operations. Together they give exactly the structural ring isomorphism used by the rest of the proof. Both apply to arbitrary algebraic spaces over the same scheme and require no separation or finiteness.

Step 2 uses chartwise etale permanence to ensure every section value M(W,a) is legitimate on Z and later that composition gives the right X-neighbourhood. It uses the actual cofiltered-small-neighbourhood statement for algebraic spaces, not the corresponding scheme-only statement. To apply the new leaf I checked both point axioms: cofilteredness comes from that node, and any covering of a scheme object W is a jointly surjective etale family of schemes, so the scheme covering-lift lemma applies with exactly the same algebraically closed field. Module sheafification has the underlying abelian sheafification and a linear unit by its definition node; thus the abelian stalk isomorphism supplies the module comparison. The restrictions that merge lift indices remain well-defined by finite summation and the semilinearity of the module restrictions.

Step 3 uses only the stated colimit universal property after writing its cocone explicitly. Its restriction equation keeps the lift label fixed at the geometric point and sends the section to its genuine germ. No unproved commuting-colimit/direct-sum interchange is invoked. Step 4 uses the composition part of etale permanence and the colimit universal property to construct the inverse one lifted-point stalk at a time. Every Z-neighbourhood becomes an X-neighbourhood; every transition is over Z and hence maps the selected presheaf summand to the selected restricted summand. Taking the direct sum is an elementary universal-property operation, not a new node.

Step 5 checks both composites on the very same section generators, rather than assuming a compatibility from the source. The colimit uniqueness statement cited here really asserts determination by all cocone maps. For the scalar check, cofilteredness puts scalar and module representatives at a common pointed neighbourhood, and the elementwise filtered-module-colimit node applies with R = Z to the underlying abelian diagrams. I do not apply a fixed-ring module-colimit theorem to the varying structure rings. Semilinearity and the canonical ring identifications then prove linearity. Naturality is checked on each section-to-germ map, which determines the map. All step texts are below 2000 characters; none hides a separate comparison theorem.

I tested the empty space (no geometric point, so the assertion is vacuous), the empty lift set (the direct sum and presheaf stalk are zero by the constructed inverses), j the identity (the maps reduce to the identity stalk comparison), a disjoint union of arbitrarily many etale components (only finite supports occur), and nonseparated etale j. The proof uses no diagonal closedness, finite number of branches, quasi-compactness or scheme assumption on Z or X. It assumes no constant coefficients and does not confuse structure stalks with residue-field fibres. The generic leaf also handles the zero abelian presheaf and arbitrary small point-element categories.

I read every cited node's full statement and recorded it verbatim in citations.json. I checked the dependency closures of the ringed-site model, geometric-point comparison and etale permanence: none reaches this item, so these citations introduce no cycle. The ringed-site model and etale permanence are generic off-unit tools; their exact uses are declared in split_report.tool_uses, along with the scheme covering-lift tool. No unit record or maintainer-owned field is changed, and no forbidden source is cited.

## Dry-run repair

The first server dry run required an explicit mathlib_match.line field. I added line 281, already verified in the pinned Mathlib source and named in the match explanation. No mathematical statement or proof changed.

## Unfinished

No mathematical work remains for this one-level split. The required server dry run and direct delivery follow this report; the maintainer independently reviews the result.
