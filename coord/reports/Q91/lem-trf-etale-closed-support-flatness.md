## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-closed-support-flatness.json`: statement, split; five proof steps, ten existing dependencies, no new nodes and no Mathlib leaves. The statement and statement dependencies are unchanged.
- `citations.json`: twelve step/node entries, each quoting the precise portion of the existing statement used; checked as literal substrings.
- `searches.jsonl`: actual search command records, retained unchanged.

## Attachments

None. Searched project `lean/WeilConjectures/` by the exact blueprint tag and by etale/source/base/closed-support flatness notions. No declaration states the complete item with a closed proof. The existing declaration `AlgebraicGeometry.closedImmersion_pushforward_stalks` belongs to `lem-weil-pbc-closed-pushforward-stalks` and is a reused ingredient, not an attachment of this item. Read its full statement and proof in `ClosedPushforwardStalks.lean`; it has no sorry and supplies both zero stalks and the base-linear germ identification.

## WANTED

None. All sources needed are present in `literature/stacks-project/`.

## Corrections and source audit

The imported statement is correct, including its unrestricted non-cartesian diagram and its lack of affine, finite-presentation and Noetherian hypotheses. No STATEMENT-DISPUTED correction is needed. It had no proof. The new proof expands the etale source and closed-support part of Stacks Tag 057U (`flat.tex`, `lemma-devissage-flat`), rather than applying that lemma beyond its elementary-devissage hypotheses. The two neighbourhood equivalences have explicit topological arguments. In particular flatness at a point is never asserted to imply flatness on a neighbourhood.

Read chapter `sec-trace-formula`, unit `sk-i-curve-zero`, and the current latest ancestor `lem-trf-local-term-locality.md` and `.proof.md`. Its normal-cone specialization route is the inherited ancestor of this supporting flatness branch; this proof changes no chapter, unit, or ancestor statement. The current ancestor has no literal flatness clause and is not misrepresented as stating this algebraic fact. The inherited precise supporting place is retained, and `same_as` is empty. Whole-DAG keyword/tag searches and whole-blueprint searches for `057U`, `relative flatness`, `flatness`, and `closed pushforward` found existing ingredients, not another complete blueprint statement. No new nodes or unit edits were required.

Mathlib search commands were actually run for this item, through the prescribed `msearch.py`: Loogle `Module.Flat, AlgebraicGeometry.Etale`, grep for flat/pushforward/closedImmersion/etale in AlgebraicGeometry, LeanSearch on base flatness detected on an etale neighbourhood/closed support, and two different LeanFinder phrasings. All five services answered successfully. Read the returned types: `AlgebraicGeometry.Flat` and its stalk/base-change criteria concern flat scheme morphisms; `Module.flat_iff_of_isLocalization`, `Module.Flat.of_isLocalizedModule`, and `Module.flat_of_isLocalized_span` are localization ingredients. None states the relative module assertion including neighbourhoods and closed support. Opened Mathlib `Morphisms/Etale.lean`, in particular `Etale.iff_flat_and_formallyUnramified` at lines 140–143, confirming that the grep result is an ingredient only. No search has been invented, and earlier recorded searches are retained alongside today's actual log records.

## Unfinished work

None in the stage-1 split. All non-elementary inputs already have DAG nodes. No Lean was written or compiled. The required server preflight and delivery are run after this report is written.

## Not duplicates

No new nodes. Reused `lem-trf-relative-flatness-source-cover`, `lem-trf-etale-local-ring-flatness`, `lem-weil-pbc-etale-morphism-open-map`, `lem-weil-pbc-closed-pushforward-stalks`, and `lem-weil-pbc-module-pullback-quasi-coherent`. The algebraic-space lemma `lem-sfb-space-closed-pushforward-relative-flatness` uses small etale module categories; its full text was read but it is not cited as if it were the ordinary Zariski closed-support assertion. The parent `lem-trf-elementary-devissage-flatness` and sibling `lem-trf-finite-pushforward-flatness-singleton` need extra devissage or finite-singleton data and are not invoked, avoiding a cycle through the parent.

## Review by Q91

I read Stacks `flat.tex` Tag 057U, both triples and its full proof. I also read Tags 05B9 and 05BA (`lemma-etale-flat-up-down` and `lemma-etale-flat-up-down-local-ring`), Morphisms Tag 02JZ (`lemma-flat-permanence`), Sheaves Tag 00AE (`lemma-stalks-closed-pushforward`), and Modules Tag 01BG (`lemma-pullback-quasi-coherent`). The closed germ linearity is also checked directly in the project theorem following the germ rule used by Modules 08KS. No SGA route is involved.

For Step 1 I opened all four cited statements. The pullback lemma says H is quasi-coherent for an arbitrary scheme morphism. The etale definition explicitly includes flatness. The source-cover node gives a pointwise equivalence for an arbitrary flat source map, with no cartesian-square hypothesis; substitute h=g and its base f. The etale-local-ring node accepts an arbitrary module over the base local ring, so it applies to H_w with its action through a. The equality fg=ea identifies the action restricted along e with the action from f and g. This checks all the hypotheses and scalar maps at every w, not just at the marked point.

For Step 2 the flat-over-base definition explicitly states the all-stalk characterization, and the etale-open node explicitly states openness of images of arbitrary open subsets. Inverse images supply the forward neighbourhood and the open image g(W) supplies the reverse. Each point of the image has a lift, so the pointwise equivalence from Step 1 suffices without quasi-compactness or flat-locus openness.

For Step 3 I read the closed-immersion definition, the entire closed-pushforward stalk statement, the module-stalk functor statement, and the tensor-injectivity definition of module flatness. The first supplies the closed embedding hypothesis; the second supplies both stalk vanishing off the image and the O_U-linear bijection on the image. The stalk functor takes the given isomorphism and inverse to mutually inverse linear maps. Restricting scalars makes their composite O_T-linear because the stalk map of ai is the composite of those of a and i. Tensor conjugation proves invariance of flatness under this isomorphism, and the same definition proves flatness of zero. Neither fact is hidden in a new node.

For Step 4 I checked the exact topology needed: since i is a homeomorphism onto a subspace, an open W of Z equals i^{-1}(V) for some ambient open V, and z in W forces i(z) in V. The image need not be an open subset of U. At every point in V, Step 3 either identifies the stalk with a stalk in W or makes it zero. This is a few-line elementary assembly using the explicit flatness criterion and the definition of a closed immersion. Step 5 is just transitivity and specialization of previous steps. No step exceeds 2000 characters, and no independent sublemma is concealed in a long step.

I tested the zero modules, i the identity, g and e identities, and empty Z (where there is no marked z, hence the marked assertions are vacuous). For a non-flat closed immersion Spec(F_2) into Spec(Z), G=F_2 over base Spec(Z) fails flatness at its nonzero stalk and the closed pushforward fails at the same stalk, as required; this proof never assumes i is flat. A nonreduced closed immersion behaves the same way because the stalk comparison respects the quotient scalar action. General etale maps with nontrivial residue-field extensions are allowed by the exact arbitrary-module 05BA statement. These checks confirm that none of the absent finite-type, finite-presentation, residue-field-isomorphism, or Noetherian hypotheses was silently used.

I checked B1–B10: no new-node statement, search, or source defect arises; the existing statement is self-contained and unchanged, the exact Lean attachment test fails for the complete item, and searches and blueprint provenance are recorded. For C1–C8 I read each dependency statement, wrote every substantive input as a node citation, verified all twelve quotes literally, avoided the parent and its descendants as proof inputs, and used only same-unit statements or closed/Mathlib tools from elsewhere. For D1–D5 the five steps are actual proofs: no clause is renamed as a new lemma and the neighbourhood details omitted by 057U are written out. For E1–E7 I checked the hypotheses, scalar rings, points, and topology at each application as above. No mathematical correction or missing source remains.
