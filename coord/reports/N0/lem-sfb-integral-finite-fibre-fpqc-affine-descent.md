# Stage-1 delivery: lem-sfb-integral-finite-fibre-fpqc-affine-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-finite-fibre-fpqc-affine-descent.json: existing statement, split into eight steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-descent-finite-point-orbits.json: statement-only prerequisite; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-descent-invariant-quasiaffine-charts.json: statement-only prerequisite; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-finite-set-affine-reflection.json: statement-only prerequisite; no Mathlib match.
- citations.json: 29 step/dependency entries, quoting the actual statements of the cited nodes verbatim.
- searches.jsonl: actual msearch.py outputs, retained with their returned declarations. The JSON node records preserve query/tool text and results.

## Attachments

None. I searched the project under lean/WeilConjectures for the blueprint tag, integral descent, fpqc representability and finite-set affine neighbourhoods. The scheme-property descent declarations do not prove the effectivity or (FA) clauses. No claim is made that an existing sorried project declaration is a proof.

## Sources wanted

WANTED: Michel Raynaud, Un critère d'effectivité de descente, Séminaire Samuel 1967/68, exposé 5, Theorem 4.1 and its invariant-neighbourhood construction, printed pp.16–21, for lem-sfb-integral-descent-invariant-quasiaffine-charts and the item; suggested archive path literature/raynaud-critere-effectivite-descente.pdf.

WANTED: the same Raynaud exposé, Theorem 4.1(ii), pp.16–21, as context for the separately agent-formulated finite-orbit prerequisite lem-sfb-integral-descent-finite-point-orbits. The finite-orbit lemma is a prerequisite formulation, not a purported verbatim quotation of Theorem 4.1.

WANTED: the same Raynaud exposé, Corollary 3.8, printed p.15, for lem-sfb-integral-finite-set-affine-reflection.

WANTED: S. Anantharaman, Schémas en groupes, espaces homogènes et espaces algébriques sur une base de dimension 1, Propositions 4.1.1 and 4.1.3, printed pp.54–55, for the item; literature/anantharaman-groupes-dimension-un.pdf.

Both primary texts were read through their Numdam PDFs, without downloading or writing to literature: https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf and https://www.numdam.org/article/MSMF_1973__33__5_0.pdf. Consequently proof_origin is agent, and the missing local archives are explicitly requested. No SGA source is used.

## Corrections and blueprint audit

The item's mathematical statement is unchanged. There is no statement dispute. The source scan calls the finite-subset proposition 4.1.3 (OCR renders 4.1.5); the Raynaud cross-reference is Corollary 3.8, not the OCR's 5.8. These are bibliographic clarifications.

I used literature/blueprint/latest, including the direct-images proof (3), and the inherited trait-descent chain. blueprint_refs.py ancestor returns no imported ancestor for this chain, so I retained its null from.node and its full via chain, and prepended the item for each new node. The from.place describes the supporting integral-descent argument. Whole-blueprint searches included integral descent, affine neighbourhoods, Raynaud, finite orbits, invariant quasi-affine and affine reflection. No equivalent blueprint node was found.

The existing item leaves the integral effectivity mechanism implicit. The split now separates finite orbit images, construction of invariant quasi-affine charts, effective descent of those charts and gluing. In particular, the chart lemma concludes with charts and a restricted datum; it does not conclude that F is representable. The finite-set reflection lemma concerns an already existing integral surjective map, without sheaves or descent data. The orbit lemma requires neither (FA) nor an fpqc model on a second cover. None of the three restates the representability or full (FA) conclusion of the item.

## Unfinished work

No Lean implementation or compilation is part of this stage. The three new nodes are intentionally statement-only and require later stage-1 splits. There are zero new Mathlib leaves. Source archival requests above remain for the maintainer; their mathematical statements and the sources actually read are recorded now.

## Not duplicates

lem-sfb-integral-descent-finite-point-orbits vs lem-sfb-integral-finite-fibre-fpqc-affine-descent: the new statement is only finiteness of the orbit image for an arbitrary locally finitely presented datum; it assumes neither (FA), an auxiliary representing model, nor a set sheaf, and gives no effectivity or affine-neighbourhood conclusion.

lem-sfb-integral-descent-invariant-quasiaffine-charts vs lem-pd-invariant-affine-neighbourhoods: the existing statement uses a finite flat locally finitely presented cover and constructs affine neighbourhoods there. The new statement transfers orbit neighbourhoods along an arbitrary integral surjection to invariant quasi-affine charts on the separate fpqc model. The auxiliary integral cover need not be finite or locally finitely presented.

lem-sfb-integral-descent-invariant-quasiaffine-charts vs lem-pd-effective-invariant-open-cover: the existing lemma assumes a suitable invariant covering whose restricted data are effective and glues it; the new lemma constructs the covering and asserts no effectivity. Both are used in different steps.

lem-sfb-integral-descent-invariant-quasiaffine-charts vs lem-trf-quasi-affine-fpqc-effective-descent: the existing lemma descends an already quasi-affine datum. It does not construct quasi-affine invariant opens from affine orbit neighbourhoods on another cover.

lem-sfb-integral-finite-set-affine-reflection vs lem-sfb-space-integral-universally-closed: integral morphism permanence for existing algebraic spaces does not reflect existence of one affine open containing a prescribed finite subset. The new lemma has the essential locally Noetherian target and finite underlying fibre hypotheses.

New nodes cite no Stacks tag shared with a separate new statement. Whole-DAG searches by source names and orbit/affine-neighbourhood keywords found no exact or more general finite-orbit or finite-subset-reflection statement to reuse.

## Review by N0

I read Anantharaman's two propositions in the original scan and Raynaud's Theorem 4.1 proof and Corollary 3.8. The former supplies the orbit criterion and the finite-subset application; Raynaud's proof supplies invariant quasi-affine neighbourhoods before its final effectiveness invocation. The chart-transfer node records that intermediate output, localized on the base and transferred back from affine refinements. This is a genuine construction input, not the full theorem renamed. For the finite-orbit node I used the algebraic-field-fibre prerequisite: each reduced fibre of the integral cover has finitely many points with algebraic residue fields; the locally finitely presented descent datum has continuous point action after passing to an algebraic closure, so point stabilizers are open and orbits finite. This remains a substantive statement-only prerequisite, rather than being passed off as an elementary observation or a quoted source theorem. Corollary 3.8 states exactly the finite-subset reflection with a locally Noetherian target and finite fibres; flatness is not needed there.

For Step 1 I opened the representability definition, the uniqueness-of-representers lemma, the descent-datum definition, the fpqc base-change lemma, the morphism-permanence lemma, and the local finite-presentation descent lemma. The uniqueness lemma supplies the actual scheme isomorphisms on overlaps; their uniqueness supplies the cocycle. The permanence lemma's base-change clause and the property-descent lemma apply between Y and its existing pullback, so this step does not assume representability on S. I corrected the initial draft by explicitly citing uniqueness rather than treating it as part of the definition of representability.

For Steps 2 and 3 I checked the complete statements of both new inputs against the schemes actually present. Y/T is locally of finite presentation by Step 1, Y is locally Noetherian by the item, and q is the original integral fpqc cover with finite underlying fibres. Thus it is the finite image of each orbit that (FA) encloses. The chart input allows an arbitrary integral surjection q and uses the given P/S' locally of finite presentation and canonical overlap identifications. Its output explicitly includes equality of inverse-image opens and the cocycle, exactly what is required to restrict the datum. No assertion that arbitrary base change preserves finite point fibres is used.

For Step 4 I opened both generic effectiveness statements. The quasi-affine effectiveness node accepts a singleton fpqc covering with no finite-presentation requirement; the invariant-open-cover node accepts a set-indexed covering and arbitrary effective restricted data, with no finite or affine cover hypothesis. These statements supply respectively each local model and their global scheme. I corrected the Stacks label for 0AP4 to lemma-effective-for-fpqc-is-local-upstairs. Their generic use is declared in split_report.tool_uses; they do not replace the construction of the chart covering.

For Step 5 I opened the fpqc representability-descent statement: it requires the actual cartesian invariant projection P to X, which Step 4 supplies. It therefore identifies the constructed scheme with F rather than merely descending its underlying topological space. I also opened the local finite-presentation definition and the locally-Noetherian locally-finite-type source theorem. A finitely presented algebra has finitely many displayed generators, giving the elementary implication to locally finite type. The base S is locally Noetherian, exactly as required for X to be locally Noetherian.

For Step 6 I opened all seven cited statements: integral base change, fpqc base change, the affine definition of an integral morphism, Noetherian rings of affine opens in a locally Noetherian scheme, Noetherian fibre rings, the integral-extension dimension bound, and finiteness of a zero-dimensional Noetherian scheme. Over an affine open of X, the inverse image is affine because the projection is integral, and its ring is Noetherian because Y is locally Noetherian. The actual fibre ring is then both Noetherian and integral over a field. Thus the cited dimension and zero-dimensional results really apply to the fibre scheme. This supplies finiteness for Y to X without making the false general inference that finite underlying fibres survive arbitrary base change.

For Step 7 the new reflection statement has precisely the now-verified hypotheses: existing schemes, integral surjectivity, locally Noetherian X and finite underlying fibres. The finite union of those fibres over E is finite, so (FA) for Y applies to its whole inverse image. The reverse implication gives one affine open containing E, not merely separate neighbourhoods of its points.

For Step 8 I opened the flatness, separatedness, local finite-presentation and quasi-compactness descent nodes. All concern existing morphisms after an fpqc base change, and q satisfies the singleton covering hypotheses. Finite presentation upstairs includes quasi-compactness and local finite presentation. The separatedness statement specifies its diagonal as a closed immersion, and the closed-immersion definition includes its affine quotient description. This makes that diagonal quasi-compact; the finite-presentation definition then combines local finite presentation, quasi-compactness and quasi-separatedness. No additional finite-presentation descent node is needed.

I tested the new statements with the identity cover, an empty represented functor, empty finite subsets, nonreduced bases, and algebraic field covers. For an infinite algebraic extension, the relation's fibre may have infinitely many points even though its image orbit in a locally finitely presented form is finite; this is why the first new node says image finiteness explicitly. The finite-subset criterion permits the empty affine open. The fibre argument allows the zero ring and the empty fibre, as the zero-dimensional node explicitly does. I checked that the source local-Noetherian hypotheses occur on the correct targets at both uses. The three prerequisites are non-elementary; the remaining finite-union, restriction-of-cocycle, finite-generation and diagonal arguments are written as steps. No step exceeds 2000 characters or hides an unlabelled auxiliary comparison. Searches of all new statements used both semantic phrasings, Loogle and the required logged Mathlib grep; the returned finite-morphism and quasi-affine-construction declarations do not specialize to these statements. Every cited statement was opened, and citations.json quotes the actual statement rather than a source paraphrase.
