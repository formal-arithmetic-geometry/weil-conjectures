## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-point-residual-substack.json: item, statement, split in six steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-self-relation-quotient-embedding.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-representable-lft-fppf-source-descent.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-reduced-locnoeth-fppf-descent.json: statement-only, unsplit; no Mathlib match.

citations.json contains a verbatim statement quote for every step/node pair. Searches were run using msearch.py; actual full outputs are retained in the sandbox and recorded in the nodes. No new Mathlib leaves; the proof reuses the existing finite-type-over-Noetherian algebra leaf and the current DAG quotient lemma.

## Attachments

None. Searches in lean/WeilConjectures by blueprint tag, residual-gerbe terminology, algebraic-stack terminology and field-point terminology found no exact completed declaration. No Lean was written or compiled.

## WANTED

None; all proof sources were available locally.

## Corrections and scope

The item statement is unchanged. The proof follows Stacks 06G3's field self-relation quotient construction, starting directly from the locally finite type field representative in the hypothesis rather than first changing it to a closed point in a smooth chart. Both self-relation projections are then locally finite type immediately by base change. This removes an unnecessary closed-point existence input, without changing the argument or imposing separation, perfectness, or Noetherian conditions.

The latest blueprint direct-images proof and the chapter/unit records were read. This deeply created prerequisite has blueprint.from.node = null, as printed by blueprint_refs.py ancestor; its existing via chain and detailed place are retained. Each new node inherits that origin with the item prepended to via. Whole-blueprint searches for residual gerbe, finite-type point, quotient stack, flat groupoid, fully faithful, fppf-local source, 04T4, 04Y5, 06EW, 06G4, 034C, 06MP and 06MJ gave no equivalent blueprint statement. The fully faithful search returned categorical/sheaf adjunction statements, not this stack quotient assertion. No unit key-node realization is owned by this item.

## Source error

The final source-descent paragraph of stacks-morphisms.tex, lemma-point-finite-type-monomorphism (06G3), cites spaces-descent lemma-locally-finite-presentation-fppf-local-source (06EV) to infer local finite type. The composite has only been shown locally of finite type; one cannot infer that it is locally finitely presented over an arbitrary base. The adjacent lemma-locally-finite-type-fppf-local-source (06EW) is the correct input. Explicitly take A = k[x_1,x_2,...]/(x_i x_j for all i,j). Its square-zero maximal ideal m has the infinitely many x_i as a k-basis. The quotient A to k is finite type but not finitely presented, since m is not finitely generated. Thus Spec k to Spec A is locally finite type but not locally finitely presented. The delivery uses 06EW explicitly; there is no dispute with the item's statement.

## Review by Q84

I read the whole construction in stacks-morphisms.tex Tag 06G3, and stacks-properties.tex Tags 06MT and 06MU and their surrounding residual-gerbe discussion. I also read 06MP and its proof to check why the quotient is reduced and locally Noetherian, rather than assuming that any singleton stack automatically has those properties. The existing quotient statement and three new supporting statements were checked respectively against criteria.tex 06FI/06FH, algebraic.tex 04T4/04Y5, spaces-descent.tex 06EW, and stacks-properties.tex 04YF/06MP with spaces-descent.tex 06MI/06MJ and descent.tex 034C/034E. The last statement is their general scheme-cover version: for a smooth scheme atlas W, V times_Z W is smooth over the reduced locally Noetherian V and therefore reduced and locally Noetherian; its flat lfp surjection to W descends the two properties. This argument is recorded here as motivation, not hidden inside a new unsplit statement.

For step 1 I opened the statements of the existing diagonal/space-source representability node and the representable chartwise calculus node, and of the new self-relation node. The first gives representability of a from its algebraic-space source; the second gives base-change preservation of local finite type for precisely such representable morphisms; the third supplies R, the groupoid operations and the quotient map. I did not use the existing stack-finite-type calculus, which restricts its objects to Deligne--Mumford stacks: the present stack need not be DM.

For step 2 I opened the algebraic-space chart-test statement: it gives exactly the chart criteria for flatness, local finite presentation and local finite type, without any simultaneous auxiliary property. On affine charts of R over Spec L, local finite type gives a finite-type L-algebra. I opened the existing Noetherian finite-type algebra node: its statement makes that algebra finitely presented since a field has only two ideals. Flatness is the elementary vector-space argument: all L-vector spaces are free, so tensor is a direct sum of copies of the original map and preserves injections. This step does not require R to be a scheme and does not confuse finite type with finite presentation over S. The supporting source 06G4 was read, but no unnecessary duplicate algebraic-space lemma was created.

For step 3 the current existing quotient node states both algebraicity and the representable surjective flat lfp property of q; it needs flat lfp source and target, verified in step 2. The embedding node states full faithfulness and representability once the quotient is algebraic, so every property claimed for i is present in its statement. In particular there is no assumption that a general quotient stack is algebraic. The fppf stackification in these two nodes cites the existing stackification/local-description statement. I read its statement, including local essential surjectivity, isomorphism-sheaf comparison and factorization into a stack.

For step 4 the reduced/locally-Noetherian descent node applies to q because it is an fppf scheme cover and u is a field spectrum. Reducedness and Noetherianity here follow directly from the ideals and nilpotents of a field. For step 5 I use the explicit field-lifting meaning of surjectivity in the quotient node, and the factorization iq = a in the embedding node. These identify the point class without asserting that a subset-theoretic inclusion gives a scheme-theoretic factorization. For step 6 the source-descent node has precisely the two representable morphisms, surjective flat lfp first morphism, and locally finite type composite available here. It does not need q to be quasi-compact. All citations in citations.json were copied literally from the corresponding statements.

I tested the new statements on the identity groupoid (quotient U), the empty groupoid (empty quotient), and the groupoid of an imperfect-field point with nonreduced stabilizer (flat quotient still algebraic, not necessarily smooth or DM). The embedding of the self-relation of an arbitrary field extension into a point yields that point, rather than incorrectly retaining the extension field. The descent statements include empty targets and impose surjectivity so that an empty source cannot prove reducedness or Noetherianity of a nonempty target. Fppf covers need not be smooth; reducedness is descended using a smooth atlas after base change, never asserted to ascend along every flat morphism. None of the three new nodes restates the residual-substack conclusion: the item's construction and the singleton/image verification remain in its proof. Every step is below 2000 characters.

I checked delivery-errors B through E: new nodes are self-contained statements only, include the notions and relevant Stacks labels, have real logged searches of all requested kinds, and preserve JSON TeX escapes. The existing Mathlib candidates concern schemes or ordinary categories, not algebraic stacks; the chart comparison would require additional proof. I read the relevant source for the scheme descent candidate in Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean: DescendsAlong is descent on the target by pullback, whereas our statement descends local finite type from a composite along an fppf source cover. It is not an exact match. The generic representability candidate in CategoryTheory/MorphismProperty/Representable.lean discusses relative representability inside a category, not the faithfulness criterion for algebraic-stack morphisms. No C4 citation was stretched to cover either gap. The current dependencies were checked for a path back to the item; the reused chart calculus and finite-type algebra nodes do not reach it.

## Repair of returned delivery

The returned sandbox corresponds to dry-run head 1b5cad6fd56; repair-baseline.json preserves its node files, report and citations. I compared those retained files with the current read-only DAG. The item remains unsplit there and its statement is identical. The former new node lem-sfb-flat-groupoid-algebraic-quotient now exists in the DAG with a differently worded statement, an additional self-relation equivalence, and its own origin record. I removed the obsolete sandbox node file rather than delivering an edit to an existing node. The item still cites that id in steps 3 and 5, using its current statement.

I reread every current proof-dependency statement. In particular, the current quotient statement assumes flat locally finitely presented source and target maps (step 2 supplies both) and concludes algebraicity, representability, surjectivity, flatness and local finite presentation of the object map. It explicitly defines surjectivity by lifting field objects after a field extension, exactly what step 5 uses. I replaced the two outdated quotient quotes in citations.json with a verbatim passage of this current statement. The other six cited statements agree with the retained verbatim quotes and continue to support the same uses described above. The proof route and all six mathematical steps are retained; the split report now records reuse of the existing quotient theorem and three new nodes.

The first repair dry run identified four new same-tag pairs, all read in full: representable-fppf-etale-open-descent, singleton-stack-finite-field-homeomorphism, smooth-reduced-dense-pullback and singleton-stack-flat-lfp-field-cover. Their statements give respectively descent of other morphism properties, a field-gerbe structural conclusion, smooth ascent with density, and construction of a field cover from already known stack properties. None supplies either of the two new descent statements. The exact differences are recorded under Not duplicates. The retained logged Mathlib searches and their full results were reread and reused because neither the remaining new statements nor the search questions changed. No new search is claimed.

This repairs the landing failure: the quotient lemma is no longer an added or modified file in this delivery, so no --drop-nodes treatment is needed. Only the item, three genuinely new nodes and this report are delivered. I checked the cited Stacks constructions again at 06G3, 06FI/06FH, 04T4/04Y5, 06EW and 06MP; the same field, groupoid and cover hypotheses hold after rebasing. All proof steps remain below 2000 characters. No repository or launcher file was written, and no Lean was compiled.

## Not duplicates




lem-sfb-self-relation-quotient-embedding vs lem-sfb-action-groupoid-quotient-criterion: the existing node assumes an etale locally surjective finite constant action groupoid presentation and proves equivalence with torsors; the new node allows any map from an algebraic space and proves full faithfulness into its target, without local surjectivity.

lem-sfb-self-relation-quotient-embedding vs lem-sfb-finite-formal-quotient-pullback: the existing node identifies finite pullbacks of a specified complete local finite-group quotient chart; the new node constructs the self-relation quotient embedding for any algebraic-space map.

lem-sfb-self-relation-quotient-embedding vs lem-sfb-etale-smooth-atlas-fppf-descent: the existing node upgrades etale descent to fppf descent with smooth atlas; the new node gives the canonical fully faithful quotient embedding and its representability.

lem-sfb-self-relation-quotient-embedding vs lem-sfb-stack-isom-space-locally-finite-type: the existing node gives local finite type of Isom algebraic spaces, not the self-relation quotient or its embedding.

lem-sfb-representable-lft-fppf-source-descent vs lem-sfb-smooth-cover-flat-lfp-descent: the existing node descends flatness and local finite presentation through a smooth surjection; the new node descends local finite type through an arbitrary flat lfp surjection.

lem-sfb-representable-lft-fppf-source-descent vs lem-sfb-stack-fibre-regular-slice-flat: the existing node constructs a flat lfp slice from a fibre regular sequence; it has no local-finite-type source-descent assertion.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-etale-local-noetherian-descent: the existing node descends local Noetherianity under etale scheme coverings of a scheme; the new node allows arbitrary flat lfp scheme covers of a stack and also descends reducedness.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-log-structure-fixed-scheme-enhancement: the existing node glues fine log structures on a prescribed scheme from etale lifts, including local Noetherianity in that special setting; the new node allows arbitrary algebraic-stack targets and fppf scheme covers and also proves reducedness.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-etale-reduced-cartier-descent: the existing node concerns reduced induced subschemes and Cartier divisors under etale scheme maps; the new node concerns reducedness and local Noetherianity of a stack from an fppf scheme cover.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-etale-reduced-regular-center: the existing node proves regularity and equality of center ideals using etale charts of locally Noetherian schemes; the new node needs no specified center and permits flat lfp covers of stacks.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-log-tower-effective-center-descent: the existing node descends compatible log blowup towers under strict etale covers of locally Noetherian log schemes; it is not a stack reducedness or local Noetherianity criterion.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-labelled-coordinate-boundary-globalization: the existing node globalizes labelled coordinate boundaries and regular intersections on a Noetherian scheme; it neither assumes an fppf stack cover nor concludes the two stack properties in the new node.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-nc-maximal-branch-blowup: the existing node constructs a maximum-branch blowup center of a normal crossings divisor on a Noetherian regular scheme; the new node descends two properties of arbitrary stacks.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-resolution-word-maximum-center-descent: the existing node identifies the regular maximum center of a specified characteristic-zero resolution history; it has no general stack property descent criterion.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-polarized-fine-log-etale-descent: the existing node descends polarized fine log schemes and morphisms under strict etale covers; it does not descend reducedness or local Noetherianity of algebraic stacks.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-sfb-noetherian-space-finite-scheme-cover: the existing node starts with a separated Noetherian algebraic space over a field and constructs a finite scheme cover; the new node deduces reducedness and local Noetherianity of a stack from a given fppf cover.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-sc-brauer-zero-all-curves: the existing node states vanishing of the cohomological Brauer group of curves over an algebraically closed field; it is not a stack property descent result.

lem-sfb-representable-lft-fppf-source-descent vs lem-sfb-representable-fppf-etale-open-descent: the existing node descends flatness and local finite presentation on the source, and four properties on the target; it has no local-finite-type source-descent conclusion, which the new node supplies.

lem-sfb-representable-lft-fppf-source-descent vs lem-sfb-singleton-stack-finite-field-homeomorphism: the existing node constructs a finite residue field and universal point-space homeomorphism for a reduced singleton stack over a field; the new node is a general local-finite-type source-descent criterion for representable morphisms, without singleton or field-base hypotheses.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-trf-smooth-reduced-dense-pullback: the existing node ascends reducedness and local Noetherianity under smooth scheme maps and proves density assertions; the new node descends the two properties under an arbitrary representable surjective flat locally finitely presented scheme cover of an algebraic stack.

lem-sfb-stack-reduced-locnoeth-fppf-descent vs lem-sfb-singleton-stack-flat-lfp-field-cover: the existing node assumes a reduced locally Noetherian singleton stack and constructs a flat lfp field cover; the new node starts from a flat lfp cover by a reduced locally Noetherian scheme and concludes stack reducedness and local Noetherianity, with no singleton hypothesis.

## Unfinished work

No part of this one-level split is left unfinished. The three new nodes are intentionally statement-only and await their own stage-1 items. Delivery requires the final full dry run and push.
