## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-anodyne-factorization.json — item, statement preserved, six proof steps, split; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-section-restriction.json — new statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- citations.json — twelve exact statement quotations, one for every step/node citation.

One new node; zero new Mathlib leaves. The existing Mathlib leaf lem-coef-small-object-cell-factorization is reused.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item id, right anodyne, right fibration and right cofinal terminology found no matching declaration. The node has no recorded project declaration. The master checkout is reference material only; no sorry declaration was counted as a proof. No Lean file was written and no compiler was run.

## WANTED

WANTED: an archived copy of Kerodon Corollary 7.2.1.15 (02NE), Proposition 4.2.4.7 (014Z), Corollary 7.2.1.14 (02ND), Proposition 4.2.5.4 (0154), and Proposition 4.4.2.14 (01NU), for lem-coef-infinity-equivalence-anodyne-factorization. All these pages were read online. They provide respectively the factorization route, horn replacement, section contraction, exponential boundary lift, and contractible-fiber criterion.

WANTED: an archived copy of Kerodon Corollary 7.2.1.13 (02NC), Definition 7.2.1.1 and Corollary 4.4.2.5 (01GZ), for lem-coef-infinity-equivalence-section-restriction. Their online statements were read, together with the surrounding cofinality subsection. The report and nodes distinguish these Kerodon identifiers from unrelated Stacks tags. The item proof_origin is agent because this online material is not archived in literature/.

## What was wrong or incomplete

The item was a true statement with no proof. No statement dispute or change was needed. The online display of 02NE is the left-handed version; its right-handed proof is obtained by using right horns throughout. I checked the two handedness conventions explicitly, rather than treating an ordinary Kan anodyne map as a right anodyne map. The proof uses the same section-contraction argument as 02ND, with 0154 to retain the exact base map. It does not assume that a right anodyne inclusion is a categorical equivalence (that would be false).

The historical blueprint ancestor and via list are preserved. I read the chapter record, unit sk-prop-sf-biduality-general, the old ancestor statement/proof, and the current main-20261015 prop-coef-integral-exceptional-adjoint.proof.md in sk-thm-sf-package. The derived mapping-complex adjunction in paragraph 2 is the ancestry of this local coherent-cone tool. The item is not a unit key statement; no unit record is changed. Its split does not replace any chapter or unit step, alter any coefficient category, or involve a base-change transformation. No SGA source is used.

## Not duplicates

lem-coef-infinity-equivalence-section-restriction vs lem-coef-infinity-equivalence-anodyne-factorization: both cite Kerodon 02NC, but the new lemma states equivalence invariance of the actual strict section Kan complexes for every right fibration; the item constructs a right-anodyne/trivial-fibration factorization and does not state section restriction.

lem-coef-infinity-equivalence-section-restriction vs lem-coef-infinity-relative-cone-equivalence: both mention 02NC, but the existing node concerns relative colimit/limit predicates, prescribed extension diagrams and opposite duality. It has no strict right-fibration section-space theorem, and its proof depends on this item, so it cannot be used here.

lem-coef-infinity-equivalence-section-restriction vs lem-coef-infinity-cofinal-colimit-restriction: the existing statement gives contractibility of comma quasicategories under equivalences; it does not identify strict section simplicial sets or give a homotopy inverse to their restriction map.

lem-coef-infinity-equivalence-section-restriction vs lem-coef-infinity-cofinality-space-test: the existing statement gives universal-colimit, spaces-colimit and comma tests, not the strict section-space test for right fibrations.

Before creating the new node I searched the whole DAG for 02NC, 01GZ, section restriction, cofinality and right-fibration terminology and searched the whole blueprint using blueprint_refs.py for right anodyne, right cofinal, section spaces, cofinal, 02NC and 01GZ. None states the new lemma. The new result is not an elementary reformulation of any cited definition: lifting strict section spaces along a categorical equivalence is the substantial cofinality input. It is not a clause or a renamed factorization of the item. Its statement introduces every object and the operators of its section complexes, and it contains no proof sketch, proof steps or proof dependencies.

## Review by Q28

I read Kerodon 02NE and its proof, 014Z and its complete horn-attachment construction, 02NC and the definition of right cofinality in 7.2.1.1, 01GZ, 02ND and its strict section argument, 0154, and 01NU. The item agrees with the right-handed factorization consequence: e is an actual equivalence of small quasicategories, no monomorphism is assumed of e, the intermediate object stays in the same universe, the left factor is right horn generated, and the right factor lifts boundaries including the empty zero boundary. The new node is exactly 02NC specialized to equivalences between quasicategories, unpacking right cofinality, with Kan-ness from 01GZ. Its q need only be a right fibration; the strict equations in its displayed section formula are essential. The homotopy inverse is a simplicial map with actual simplicial cylinder homotopies, not just a bijection of isomorphism classes.

Step 1 uses the statement of the existing small-object leaf, not an unrecorded construction inside its proof. I checked its small Hom, small colimit, generating-set and regular-cardinal hypotheses. The horn family is countable, omega is small and regular, and finite face images plus their overlap equations witness domain smallness. The degreewise quotient formula explicitly verifies the ordinary colimit definition. Nothing here requires M to be Kan. The first factor is a genuine cell composite, so right-horn generation will be available in the next step.

Step 2 cites the actual right-anodyne closure definition, the horn definition of right fibration, and the quasicategory definition. The coproduct in the cell theorem is covered by well-ordering its small family and successively pushing out its summands. Set pushouts add complements and do not identify old elements; at limit stages equality is witnessed at a common stage. These elementary checks prove injectivity. To show N is a quasicategory, only inner horns are projected to M and lifted; those all have indices 0<j<d and hence lie in the right-horn family. Thus no extra fibrancy assumption has appeared.

Step 3 cites the new node for precisely its restriction equivalence. The given e has the required quasi-inverse and both A=L and B=M are small quasicategories. Applying the new node to q=r is legitimate because step 2 proved r is a right fibration. The input vertex i has r i=e. Its image under the homotopy inverse is therefore an actual strict section s, not a section only up to equivalence. Evaluating the inverse homotopy yields P over the fixed e; either endpoint orientation works in the next boundary problem.

Step 4 uses exactly the exponential map displayed in lem-coef-infinity-right-fibration-exponentiation. I read that entire node statement: it applies to arbitrary small simplicial sets, requires a right fibration and a right anodyne map, and concludes a trivial Kan fibration. Its target pair is (constant r,P). The overlap equality is rP=e and both proposed source vertices have composite r. Their restrictions to L are se and i because ri=e. Consequently the dimension-one boundary-lifting clause of def-weil-pbc-trivial-kan-fibration gives H with BOTH prescribed endpoints and the exact equation rH=r pr. No unspecified transport of base homotopies is used.

Step 5 uses only the Kan-fiber clause in lem-coef-infinity-right-fibration-fibers. That node assumes three quasicategories; I verified them by taking E=F=N, B=M after step 2. I do not take an unproved equivalence of r from that node. The exact base equations restrict H to every strict fiber. The statement of lem-cbc-simplicial-homotopy-equivalence-weak then applies with A=N_m, B=Delta^0, maps the projection and the chosen s(m), and the two specified homotopies. It concludes realization weak contractibility in exactly the convention used by the fiber criterion. This is a declared generic tool from unit sk-prop-sf-cbc, since no statement of the item's unit supplies that conversion.

Step 6 invokes the actual statement of lem-coef-right-fibration-contractible-fibers. Both its hypotheses have been established: all right-horn lifting and weakly contractible Kan strict vertex fibers. Its conclusion includes dimension-zero surjectivity, so the proof has not omitted an empty-boundary requirement.

I tested the item on L=M empty (the construction stays empty), identity equivalences, and the equivalence from the nerve of a two-object contractible groupoid to a point, where e is not injective and i must be a new factor. For the new node, identity e makes restriction the identity; empty right fibrations over nonempty equivalent bases can give two empty section spaces, so no nonemptiness is inserted; for a right fibration over a point the claim reduces to invariance of mapping Kan spaces along an indexing equivalence. Ordinary discrete equivalences and an equivalence adding an isomorphic object give the same section data up to coherent homotopy. Each actual fiber in step 5 has the exhibited point s(m), resolving the empty-fiber case rather than silently excluding it.

I checked B1-B10 by keeping the new node statement-only, self-contained, sourced, and with recorded searches; C1-C8 by opening every cited statement and copying the precise clause into citations.json; D1-D5 by retaining the horn construction checks, the section and exponential lifting argument, and the fiber contractions in the item; and E1-E7 by the hypothesis checks and examples above. I checked dependency closures before writing: none of the reused proof dependencies reaches this item. Searches were made only through msearch.py; their actual logs are recorded, including the second phrasings. The all-horn Quillen and abstract model-category hits do not supply either one-sided theorem, and the ordinary section adjunction and 2-truncated edge-homotopy hits do not supply strict section invariance. I corrected the initial search-record grouping to select by query content, because concurrent search completion order differs from launch order; no unrun query was added.

## What remains

The one new node is deliberately unsplit and awaits its own worker. The completed item awaits the required independent second reading; nothing has been pushed. The server dry-run result is recorded below after it finishes.

## Validation

The server review_split check passed. The required deliver.py --no-push dry run printed `OK (not pushed) deliver/Q28/lem-coef-infinity-equivalence-anodyne-factorization at bfcd10dea9: preflight passed`. After final citation-quotation cleanup and search-record deduplication, a final dry run was requested against the finished sandbox. Nothing was pushed; the second reader should review this sandbox and deliver it using the normal procedure.

## Second reading by Q28

- Item statement: checked against Kerodon Corollary 7.2.1.15 (02NE), Corollary 7.2.1.13 (02NC), and the right-handed simplicial-opposite form; the factorization, exact equality `ri=e`, right-anodyne mono, trivial Kan fibration, universe, and quasicategory hypotheses all match.
- New node `lem-coef-infinity-equivalence-section-restriction`: checked against Kerodon Corollary 7.2.1.13 (02NC), Definition 7.2.1.1, and Corollary 4.4.2.5 (01GZ); the strict section formula, right-fibration hypothesis, Kan conclusions, homotopy inverse data, and allowance of empty section spaces are self-contained and match.
- Step 1: checked the small-object leaf statement, the simplicial-set colimit definition, and Kerodon Proposition 4.2.4.7 (014Z); the countable right-horn family, finite-domain smallness, chain-colimit equality test, and degreewise injection argument supply exactly the cited factorization data.
- Step 2: checked the definitions of right anodyne, right fibration, and quasicategory; the coproduct well-ordering, transfinite injection argument, horn lifting, and inner-horn projection are elementary from those statements.
- Step 3: checked the new node’s displayed `Gamma_a(q)` definition and 02NC/02ND; `i` is a strict section over `e`, and evaluation of the section homotopy gives the required edge over the fixed base map.
- Step 4: checked the full statement of `lem-coef-infinity-right-fibration-exponentiation`, the boundary-lifting definition, and Kerodon 0154; the pullback edge and both prescribed source endpoints have the required restrictions and exact projection equation.
- Step 5: checked the fiber theorem, the simplicial homotopy-to-weak-equivalence theorem, and 02ND; `N`, `M`, and each strict fiber have the required hypotheses, and the chosen section vertex handles dimension-zero nonemptiness.
- Step 6: checked `lem-coef-right-fibration-contractible-fibers` and Kerodon 01NU; right-horn lifting and weakly contractible Kan fibers imply the full boundary lifting conclusion, including dimension zero.
- Edge cases: rechecked empty indexing simplicial sets, identity equivalences, a noninjective equivalence adding an isomorphic object, and fibers over every base vertex; no hypothesis is silently added and empty section spaces remain allowed.
- Existing-node audit: searched the DAG and blueprint for section restriction, right cofinality, right fibrations, and the cited Kerodon identifiers; the new section-space lemma is substantial and not duplicated or elementary.
- Changes: clarified the proof steps’ Kerodon source-place fields and the proof origin to record that the web pages display the left-handed theorem and that the delivered argument uses the simplicial-opposite right-handed dual; no statement, proof argument, dependency, or citation quotation was otherwise changed. The item’s maintainer-owned source field is preserved.

- Independent Mathlib audit: ran a new LeanFinder query about slice mapping objects, Loogle `"HomotopyEquiv"`, and source grep for right-fibration/section-equivalence names; hits were Dold–Kan components, ordinary structured-arrow equivalences, short-complex homotopy equivalences, and cylinder comments. None states the new node. Recorded the actual three new searches in the auxiliary and `searches.jsonl`.
- Second-reading validation: the required server dry run printed `OK (not pushed) deliver/Q28/lem-coef-infinity-equivalence-anodyne-factorization at 0fe718227b: preflight passed`. This covers the maintained preflight, DAG checks, and split review; no local compiler or checker was run.
