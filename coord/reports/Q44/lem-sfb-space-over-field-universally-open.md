## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-over-field-universally-open.json`: split into three proof steps; no statement or statement-dependency change. The inherited blueprint provenance, citation records and creation data are retained; current searches and the split report are added.
- `citations.json`: one literal statement quotation for each citation of each step. The full statement is quoted for the two general geometry nodes because several of their clauses are used.
- `searches.jsonl`: five searches run through the required msearch command; every service answered successfully. The queries and results were read and recorded without changing their query text.

## New nodes

None. No new Mathlib leaves. The scheme case already exists as the Mathlib leaf `lem-sc-scheme-over-field-universally-open`.

## Attachments

None. Searching the project `lean/WeilConjectures/` for the item tag, algebraic spaces, and field/universal-openness names found no declaration stating the item. `universallyOpen_of_locallyOfFiniteType_spec_field`, at `AlgebraicGeometry/Hilbert/Curve.lean:1173`, concerns schemes and assumes locally finite type, so it cannot be attached. No Lean was written and no compiler was run.

## Literature and blueprint

Read Stacks `spaces-morphisms.tex`, Tag 06DN, `lemma-space-over-field-universally-open`, including its atlas proof and preceding `lemma-universally-open-local`. Read `morphisms.tex`, Tag 0383, `lemma-scheme-over-field-universally-open`. Read `spaces-properties.tex` statements and proofs at Tags 03H4 (`lemma-points-cartesian`), 03H5 (`lemma-characterize-surjective`), 03BX (`lemma-topology-points`), and the statement of 03IR (`lemma-etale-open`). All are available locally; WANTED: none.

Read the chapter/unit records, the three-level route rule in SETUP, and the latest blueprint unit and direct-images proof (3). This is an auxiliary far below that unit, serving the component-descent input in the inherited prerequisite chain. The latest blueprint has no separate assertion of this auxiliary. `blueprint_refs.py ancestor` returns None for this inherited chain; I preserved that existing `from.node` and exact inherited place rather than invent an ancestor. Searches of the entire imported blueprint for `universally open` and `06DN` returned zero nodes. Whole-DAG searches by 06DN and by universal-openness keywords found the scheme leaf and other stronger-hypothesis openness statements, not a duplicate of this item.

## What was wrong and what remains

The imported item had a correct statement and no proof. There is no statement dispute. Its equivalence explicitly asks for arbitrary algebraic-space base changes, whereas Tag 06DN first checks schemes and invokes locality; the split writes out that last locality argument instead of citing an uncatalogued locality lemma. No mathematical task remains for this one-level split. No new nodes were necessary.

## Not duplicates

No new nodes. The existing scheme theorem is cited directly and is not recreated as an algebraic-space theorem or as a renamed clause of the item.

## Review by Q44

I checked delivery-errors B through E with the source and every cited node open. The item agrees with Tag 06DN: the field is arbitrary, the domain has no finite-type assumption, and the arbitrary base-change formulation is the definition of universal openness. The empty domain is allowed. The proof never uses quasi-compactness, quasi-separatedness, nonemptiness, finite presentation, or an algebraic closure of the field.

In step 1, `def-trf-algebraic-space` explicitly gives a representable surjective etale scheme atlas. `lem-trf-space-fibre-products-etale-covers` states existence of the sheaf fibre product as the categorical fibre product and preservation of jointly surjective etale families by any algebraic-space base change; a singleton atlas is such a family. `lem-a1-space-point-open-calculus` explicitly equates representable scheme-test surjectivity with surjectivity of the point map and states continuity of every morphism. These statements, not their proofs, supply exactly the assertions made about the base-changed atlas. Both U and V are schemes over the same field, and the ordinary scheme product represents the same sheaf product by its universal property.

In step 2, the statement of `lem-sc-scheme-over-field-universally-open` covers arbitrary K-schemes X and S, so it applies to U and V without a finite-type assumption. I read its recorded Mathlib source at `Morphisms/UniversallyOpen.lean:151`: the instance for an integral one-point target is stronger than the finite-type project lemma. The equality between the two images is written using a lift through the surjective atlas point map. It uses no claim that points of fibre products equal fibre products of points, and no unstated descent theorem.

In step 3, `lem-trf-space-fibre-products-etale-covers` supplies the categorical fibre product, so its reassociation is the universal-property identification. Continuity and surjectivity onto the fibre product of point sets are explicit clauses of `lem-a1-space-point-open-calculus`. I wrote both directions of the needed image equality, including lifting a pair consisting of an arbitrary test point and a witness in O. This is stronger information than mere surjectivity of either projection; the cited node really states it. Step 2 makes the resulting image in V open. The definition `def-a1-space-point-topology` tests openness on every representable etale scheme map, exactly the class of maps used here. Thus there is no missing locality assertion. The final universal-openness sentence only unpacks the item's own definition.

The two off-unit geometry nodes are general tools for point topology and etale-cover base change; their use is explained in `split_report.tool_uses`. The scheme node is already a Mathlib leaf and all other cited notions already exist. I did not set the maintainer's top-level `tool_uses` field.

For edge cases I checked X empty, Y empty, and an empty test scheme V: images are empty and the displayed equalities still hold. For arbitrary nonempty, non-finite-type, non-quasi-separated spaces the proof chooses the atlas supplied by the definition, never a finite atlas. A point pair need only have a common field extension, not identical residue fields; Tag 03H4 and the cited point-calculus statement give precisely that lift, including inseparable extensions. No assumption of bijectivity of the cartesian point map occurs. The field can have any characteristic.

The five current Mathlib searches return scheme universal-openness infrastructure and the scheme projection theorem, while the logged grep for algebraic-space names in Mathlib/AlgebraicGeometry has no hits. A second semantic phrasing also returns scheme results. These do not cover algebraic spaces, so the item remains a split statement, not a Mathlib leaf. No new node needs a separate search or a nonduplicate justification. Every step is shorter than 2000 characters; the full assembly is below 3000 characters. All steps cite their non-elementary inputs. The short surjective-image and cartesian-pair arguments are written in the steps themselves rather than hidden in new nodes. There was no earlier split to repair; the correction made in this review was to expand scheme-test locality explicitly and quote all the point-calculus clauses actually used.
