## Files written

- `dag/nodes/sec-six-functors/lem-coef-presheaf-simplex-hocolim-resolution.json`: item, statement; split into six steps, statement unchanged; no exact Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-simplicial-bar-projective-resolution.json`: one new statement-only unsplit lemma; no exact Mathlib match. It constructs a projectively cofibrant bar resolution of an arbitrary cofibrant-valued small diagram in a combinatorial simplicial model category. It does not claim the item's augmentation to a presheaf is a weak equivalence.
- `citations.json`: one verbatim statement quotation for each node used in each item proof step.
- `searches.jsonl`: actual search-command log. `write_split.py` is the sandbox-local construction script, not a DAG node or part of the proposed delivery.

## Attachments

None. Searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item's exact blueprint tag, representable-simplex resolutions, homotopy-colimit resolutions, simplicial replacements, Bousfield–Kan, derived colimits and simplicial bar projective resolutions. No project declaration states this theorem or the new general lemma. The master checkout was used only as reference material.

## Wanted sources

WANTED: Daniel Dugger, Universal Homotopy Theories, Proposition 2.9, printed p.152, and Section 9.1, printed pp.170–171, for lem-coef-presheaf-simplex-hocolim-resolution. Read online at the URL already in the item's source; an archival copy is not listed in literature/LIST.md.

WANTED: Daniel Dugger, A Primer on Homotopy Colimits, Section 9.2, Corollary 9.8, Proposition 9.11, Remark 9.12, printed pp.34–38, and Section 19.1 and Theorem 19.4, printed pp.90–91, for lem-coef-simplicial-bar-projective-resolution. Read online at https://pages.uoregon.edu/ddugger/hocolim.pdf; an archival copy is not listed in literature/LIST.md. The Q-prime convention of Remark 9.12 is the forward-chain convention in the new node.

No Stacks tag supplies either of these simplicial model-category theorems. No literature was downloaded or changed. The item's proof_origin is agent: the online proof gives the objectwise diagram and a Grothendieck-construction/cofinality calculation, while the split proves the same evaluation comparison directly by a bisimplicial initial-object contraction.

## Findings and corrections

The imported statement is correct, including its use of every projectively cofibrant replacement and its lack of fibrancy assumptions. It has not been changed. It had no proof, and no lean_audit entry was supplied. The existing blueprint ancestry leads to prop-coef-integral-exceptional-adjoint, middle finite-level mapping-complex adjunction. I read the current main-20261015 proof, the whole unit record sk-prop-sf-biduality-general and the chapter record sec-six-functors. This is an auxiliary model-presentation input below that adjunction, not the unit's key statement, so no unit fields were written.

The one new general bar lemma supplies only the model for a derived colimit; it does not replace the item's content by a new version of that content. The actual evaluation equivalence is proved in Steps 3–5. No separate nodes were created for the elementary smallness, initial-object, nerve, coend or comparison-factorization calculations.

Step 5 declares lem-cbc-simplicial-homotopy-equivalence-weak as an off-unit generic tool in split_report.tool_uses. It supplies exactly the passage from the explicit homotopy furnished by the existing extra-degeneracy leaf to a weak homotopy equivalence, and does not change the unit's route. The same-unit realization-cylinder node alone states a homeomorphism of cylinders rather than that implication, so I did not miscite it for the implication.

## Not duplicates

- lem-coef-simplicial-bar-projective-resolution vs lem-coef-bousfield-kan-comparison-calculus: the existing node defines two simplicial replacements of diagrams of simplicial sets and proves weak-equivalence invariance; it does not construct a projectively cofibrant diagram or identify the replacement with a model derived colimit. The new node supplies that specific missing comparison in general simplicial model categories.
- lem-coef-simplicial-bar-projective-resolution vs lem-coef-model-colimit-localization-comparison: the existing node proves projective-model existence and coherent colimit comparison for an unspecified projectively cofibrant replacement. It does not give the explicit bar replacement or the chain/coend formula; it is cited as the new node's projective-model terminology.
- lem-coef-simplicial-bar-projective-resolution vs lem-coef-simplicial-projective-model-calculus: the existing node gives projective enriched diagram model structures and Quillen equivalences for changing a Dwyer–Kan-equivalent index. It does not construct a bar cofibrant replacement of a value diagram.
- lem-coef-simplicial-bar-projective-resolution vs lem-coef-adjunction-free-simplicial-resolution: the latter is an infinity-categorical free-object resolution under a conservative realization-preserving right adjoint. It gives neither the explicit strict bar diagram nor projective cofibrancy in a model category.
- lem-coef-simplicial-bar-projective-resolution vs lem-coef-presheaf-simplex-hocolim-resolution: the new node is a general tool for computing a derived colimit; it says nothing about an augmentation to F being a weak equivalence. The latter is proved here by the category of representations and its initial objects.

Whole-DAG searches for the source URL, Proposition 9.11, simplicial replacement, Bousfield–Kan, bar projective resolution and derived colimit found no duplicate. Blueprint searches for representable simplex homotopy colimit resolution, simplicial replacement, Bousfield Kan and bar resolution returned no match. The two matches for derived colimit are pro-etale comparison/affine continuity statements, not bar model-category resolutions. The generic last-vertex lemma concerns only the nerve of the simplex category of a single simplicial set and does not state this presheaf or diagram model theorem.

## Review by Q92

I read Universal Homotopy Theories Proposition 2.9 and its whole Section 9.1 proof online. It uses precisely the category of representable standard simplices in the item and computes its homotopy colimit at each object. For the new node I read the Primer's Section 9.2 construction, Corollary 9.8, Proposition 9.11, the forward-chain variant in Remark 9.12, and the extension to simplicial model categories in Section 19.1/19.4. Thus the new node uses the correct chain orientation, with a value at the initial vertex and a final extra arrow to the evaluation object. Its statement introduces every category, diagram, tensor, coend and augmentation; it carries no proof sketch or unintroduced setting.

I checked every cited node's statement, rather than relying on its title or proof:

1. Step 1 uses lem-coef-simplicial-presheaf-projective-model for the objectwise trivial-fibration class and its lifting characterization. The Yoneda lifting adjunction is given by the explicit identity-evaluation formulas, not by citing a fully-faithfulness assertion. lem-coef-kan-quillen-right-proper supplies monomorphism cofibrations, which make every standard simplex cofibrant. I checked the equation for an E_F arrow and the evaluation formula with both the contravariant D operator and the simplex operator; composing them commutes by naturality. Smallness is a small sum of the given small sets, not a large overcategory.

2. Step 2 uses the presheaf-model node's actual combinatorial simplicial assertion, then the new node's actual projective cofibrancy and objectwise augmentation equivalence. Its coend/colimit isomorphism includes maps induced by every cocone, so the resulting augmentation is the evaluation map, not merely an unspecified map between equivalent objects. The existing model-colimit-localization-comparison statement supplies the projective diagram model structure for this small index. The colimit left Quillen assertion is proved by a lifting adjunction in the step. This proves the requested cofibrancy of every H_F before using any comparison of weak equivalences.

3. Step 3 is an explicit calculation, using only Step 2 and functor-category definitions. I checked its coend map degree by degree: a pair (z,theta) represents the same class as (Z(theta)z,id), so the displayed map and inverse are well defined and mutually inverse. The first bar face acts on both b and t; the other bar operators and the q-direction precompositions give the specified bisimplicial operators. This verifies both the diagonal identification and its compatibility with the particular evaluation augmentation.

4. Step 4 is an explicit category and chain calculation, not an invocation of an uncited cofinality theorem. For fixed q and a label xi in F(x)_q, an arrow from (x,q,xi,id,id) to (d,n,sigma,b,t) must be (b,t) and exists exactly by xi=F(b)F(d)(t)sigma. There is therefore a unique initial-object arrow even if D has automorphisms. Prepending it gives all the extra-degeneracy identities written in the step. I checked the degree-zero equation separately. The initial objects need not be natural in q; rowwise contractions suffice, since the augmentation itself is bisimplicial.

5. Step 5 uses lem-coef-extra-degeneracy-contraction exactly for its section and simplicial homotopy. It then uses the generic tool lem-cbc-simplicial-homotopy-equivalence-weak with that section as inverse and the identity composite given a constant homotopy. Both hypotheses are actually supplied and neither space need be Kan or nonempty. Finally lem-coef-bisimplicial-diagonal-equivalence states the rowwise-to-diagonal implication in either direction. I orient it with p as the contracted direction and q as the indexing direction, and the target's diagonal is exactly F(x). No separate coproduct-invariance or nerve-contractibility theorem is being silently used.

6. Step 6 uses the projective-model statement's model factorization systems on diagrams. I did not assume PB_F to B_F is a trivial fibration: I factor the map from the coproduct of the two cofibrant replacements through a new trivial fibration. Both inclusions into the middle object are weak equivalences by their composites to B_F. The actual statement of lem-coef-model-infinity-derived-adjunction says a left Quillen functor preserves weak equivalences between cofibrant objects, which is precisely what is required after Step 2's lifting proof. All three colimits have the specified maps to F and both triangles commute by the colimit universal property. Two-out-of-three then proves the requested augmentation is a weak equivalence, not just that H_F and F have the same weak type.

Small cases checked: D empty (the presheaf category has one object); every value of F empty (E_F and the evaluated representation categories are empty); D terminal (the construction reduces to the canonical simplex resolution of a simplicial set); F a discrete set on the terminal category (each label category is a copy of the simplex category with the object [q] initial in the category of its q-representations); and D a one-object category with nontrivial automorphisms (the b-coordinate forces uniqueness of the initial arrow, so automorphisms create no exception). For the new general bar statement I checked I empty, I discrete, and I terminal: it gives respectively the initial diagram, the original cofibrant values, and the constant simplicial realization of one cofibrant object. These agree with the claimed augmentations.

Against delivery-errors B–E, I checked self-contained statements and definition dependencies, empty proofs for the new unsplit node, TeX escaping, exact search records and genuine hit inspection, blueprint ancestry and duplicate searches, every non-elementary fact's statement citation, the unit route, complete contractions and map compatibility, and the absence of unassumed fibrancy/cofibrancy/smallness hypotheses. I corrected a potential ambiguity in the generic model's simplex-category dependency before writing the final files. There is no statement dispute or source error. No existing metadata, live source, or project file was changed.

## Unfinished work

The one new general bar-resolution node is intentionally unsplit, as required for a one-level split. There are no other mathematical gaps in the item's six proof steps. The second reader must independently inspect the argument and run the delivery; this worker runs only the no-push dry run.

## Second reading by Q92

- Step 1 checked against Universal Homotopy Theories Proposition 2.9/Section 9.1 and the cited projective-presheaf and Kan-model statements; verdict: correct after clarifying evaluation at (d) via (1_d) (the original wording said “evaluation at (1_d)”).
- Step 2 checked against Primer Proposition 9.11/Remark 9.12 and the cited projective diagram and derived-colimit statements; verdict: correct, including the left-Quillen colimit argument and arbitrary projective replacement.
- Step 3 checked against the explicit coend formula and the bisimplicial diagonal definition; verdict: correct, with the coend relations giving the displayed diagonal identification and augmentation compatibility.
- Step 4 checked against the category-of-representations calculation in Universal Homotopy Theories Section 9.1; verdict: correct, including uniqueness of the initial arrow and all extra-degeneracy identities, also for empty label sets.
- Step 5 checked against the extra-degeneracy contraction, simplicial homotopy-equivalence, and bisimplicial diagonal nodes; verdict: correct, with the rowwise weak equivalences oriented in the stated direction.
- Step 6 checked against the projective diagram model structure and left-Quillen derived-adjunction statements; verdict: correct, including the common trivial-fibration factorization and two-out-of-three comparison.
- `lem-coef-simplicial-bar-projective-resolution` checked against Primer Sections 9.2 and 19.1/Theorem 19.4, with its dependency statements and empty-index case; verdict: self-contained, strictly smaller than the item, and not a duplicate or Mathlib declaration.

Changes made: corrected the Step 1 phrase to “evaluation at (d) (at the identity (1_d) under Yoneda)” so the evaluation object is well typed; no statement, citation, dependency, or source fields otherwise required repair. Re-ran the recorded search audit and found no exact Lean/Mathlib declaration or DAG duplicate.
