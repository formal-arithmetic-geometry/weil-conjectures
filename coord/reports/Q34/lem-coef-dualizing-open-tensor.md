# Q34: lem-coef-dualizing-open-tensor

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dualizing-open-tensor.json`: existing statement, split into five steps; no statement change. Mathlib verdict: no match for the whole item.
- `citations.json`: one entry per step/dependency pair, with verbatim statement quotations.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit realization update: this auxiliary is not the unit's key statement. No Lean written or compiler invoked. All writes are in the assigned sandbox.

## Attachments

None for this item. I searched the live `lean/WeilConjectures/` for the blueprint id, open/tensor terminology and extensionByZero. The project has open tensor and other coefficient comparisons, but no declaration giving this item's constructibility and both Tor bounds together with its pre-localization evaluation clause. The existing DAG node lem-coef-etale-open-tensor has its own Lean declaration recorded in lean/Sheaf/SixFunctors/EtaleOpenTensor.lean; it supplies a cited input, not an attachment of this larger item. I did not claim a declaration in Sheaf as an upstream attachment.

## WANTED

None. The main-20261015 blueprint and all Stacks sources used are available locally.

## What was wrong or incomplete

The imported auxiliary had no proof. Its statement needs no correction. Its mentions of structural exceptional adjoints and compact-support coefficient comparison are context, not extra inputs to the open-tensor argument, so they remain statement dependencies and are not invented proof uses.

The suggestion in the ancestor's review to cite lem-trf-open-ctf needs a site check: that node's coefficient conventions lead to the pro-etale category, whereas this item explicitly uses ordinary small etale modules. I instead prove the etale ctf conclusions from the ordinary-etale lem-sp-etale-scalar-flat-model, open tensor flatness, exact extension, and explicit stratification restrictions. No conversion between those coefficient categories is silently assumed.

I searched the full DAG by extension-by-zero, scalar/coefficient/constructibility, flat models and Tor-amplitude terminology, and the blueprint using `blueprint_refs.py search` for extension by zero, K-flat, open tensor and flat model. The ancestor command confirms lem-coef-finite-dualizing. No imported blueprint node states the whole strengthened auxiliary. Existing lem-coef-etale-open-tensor and lem-coef-etale-open-scalar-coherence state exactly the needed scalar/open comparison, counit and K-flat normalization inputs, so I created no duplicate nodes. Existing lem-sp-etale-scalar-flat-model states the flat-model and non-flat scalar-extension input, so no new model node was needed.

The inherited Mathlib searches were preserved. Additional searches were run only through the prescribed msearch.py command and recorded from searches.jsonl, including two LeanFinder phrasings, LeanSearch, two Loogle queries, and grep. Loogle's first query reports an unknown identifier `tensor`; this diagnostic is recorded, and the second query returned no hits. The LeanFinder hits concern Ext or ordinary module sheaves; LeanSearch's promising restrictAdjunction_counit_app_app is about scheme structure-module restriction, not ordinary-etale extension by zero. I read Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:447 and Mathlib/AlgebraicGeometry/Modules/Tilde.lean:175: neither states the item. The grep for extensionByZero|torAmplitude returned no hits. No service outage was relabelled as absence.

## Unfinished work

None in this one-level split. The pre-existing cited inputs retain their own statuses and are not re-split here.

## Not duplicates

No new nodes were created, hence there are no new/existing duplicate pairs.

## Review by Q34

I read the assigned brief, stages/1-dag.md, SETUP.md including its three blueprint levels, GOAL.md, the worker role, the named chapter and unit records, and both copies of delivery-errors B through E. I read the current main-20261015 proof of lem-coef-finite-dualizing: the auxiliary realizes locality and the identification of the canonical local/global morphisms by counits. I read Stacks sites-modules.tex Tag 03DI (lemma-extension-by-zero) and the explicit section description of its counit, Tag 0E8I (lemma-j-shriek-and-tensor), sites-cohomology.tex Tag 0GL1 (lemma-j-shriek-and-tensor) and its representative proof, and the restriction/pullback K-flat discussion around Tags 0G7E and 07A4. I also read etale-cohomology.tex Tag 03TT (lemma-when-ctf), Tag 0GKB (lemma-tensor-constructible) and the extension-by-zero discussion giving Tag 03S5. The proof is marked agent-written because it combines these inputs and writes the missing evaluation calculation, rather than claiming one source proves this entire strengthened statement. There are no new-node sources to audit and no forbidden SGA source is used.

For step 1, I opened the statements of lem-sp-etale-scalar-flat-model, prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback and lem-kun-flat-bounded-tor-amplitude. The first supplies a bounded flat constructible representative with a chosen interval, including K-flatness; the third explicitly says pullback of K-flat complexes with flat terms has the same properties. Exact open restriction identifies cohomology and restriction of the finite constructibility partition. The final cited lemma gives the Tor bound from this representative. The hypotheses are met because Y is Noetherian and A is finite, and restriction to an open preserves the coefficient ring. Taking intersections with U preserves the locally closed finite stratification. This establishes L's finite-Tor hypothesis before applying any scalar flat-model assertion to L.

For step 2, I read lem-pc-kflat-resolution (flat-term K-flat resolution), the pullback node, lem-coef-etale-open-tensor (flat and K-flat preservation and the B-linear comparison), lem-pur-derived-change-of-rings (scalar extension computed in the B-module category), lem-pur-etale-open-derived-tensor (the actual sheaf-comparison-induced direct-sum derived projection), and lem-coef-etale-open-scalar-coherence (the explicit K-flat representative normalization). They say what this step uses: none merely defines flatness or states an unrelated fully faithful functor. The pure tensor formula is linear for the B-action. I checked that the ordinary B-linear comparison and the canonical derived comparison coincide by the cited representative normalization; forgetting B does not define a second arbitrary map. No assumption that B is A-flat is made.

For step 3, I opened the full adjunction statement. It explicitly gives the identity-on-sections counit when the etale object factors through U, and the zero-source formula otherwise. The extension definition explicitly says sheafification of that presheaf and degreewise extension. The two paths send every pure section tensor to the same element, so their sheafified maps and resulting chain maps are equal. The differential has the same tensor sign on both paths; B is placed in degree zero. This addresses the special final clause of the item at the chain level. It is not an argument that arbitrary derived morphisms are equal when their stalk maps agree.

For step 4, I reopened the scalar-flat-model, open-tensor, exact-extension and flat-bounded-Tor statements. U is Noetherian as an open of Y (and is quasi-compact by hypothesis); both finite rings are Noetherian. For an arbitrary interval [a,b] for L, the flat-model input gives that exact interval, not just some finite interval, and its scalar extension has flat B-terms and constructible cohomology. Extension by zero preserves flat terms and quasi-isomorphisms by the cited statements. Applying the bounded-flat Tor lemma separately over A and B proves precisely the two requested intervals. No claim is made that derived tensor by a non-flat quotient is t-exact on every object.

For step 5, I opened the exact-extension statement, the exact-functor/cohomology statement, and sbc-prop-extension-by-zero-and-arbitrary-base-change. The last explicitly allows every scheme base change and complexes; it is applied to each locally closed stratum and to the reduced closed complement. The pulled-back open is respectively the identity or the empty scheme, so those restrictions are the original finite locally constant modules or zero. Finite intersections of the finitely many partitions give a common partition; strata remain constructible locally closed in the Noetherian Y. Thus the argument proves the cohomology stratification assertion without borrowing a pro-etale ctf theorem. The same base-change statement applies to underlying abelian sheaves and the identifications preserve the constant coefficient action.

I checked delivery-errors B's self-contained-node and duplicate issues (no new nodes), C1/C4 by reading each cited statement and generating citations.json from its verbatim text, and D by writing the actual section calculation and the two-ring flat-model argument instead of restating clauses as new tasks. All five steps have fewer than 2000 characters. I checked there is no dependency path from any chosen proof input back to this item. Off-unit generic site and model tools are declared with explanations in split_report.tool_uses; the unit's dualizing-object locality route is preserved. No target, statement, chapter route or unit record was changed.

For E's hypothesis and small-case checks: U empty gives zero sources and zero open extensions throughout, including the zero stratum; U=Y gives identity comparisons and the ordinary tensor identity. The zero complex admits every interval claimed. When m=n the comparison is the unit coefficient identification and the evaluation equation is the original counit. For the genuinely non-flat quotient Z/ell^2 -> Z/ell, a finite-Tor input is handled by its flat model; the step does not assert finite Tor dimension for the residue field as a module over Z/ell^2. Ramification of E causes no change because only finite quotient rings and their actual ring map are used. The proofs impose neither smoothness nor regularity on Y.
