# Stage-1 report: def-wf-determinantal-weight

## Files written

- dag/nodes/sec-purity-real-sheaves/def-wf-determinantal-weight.json: existing definition, now split. It defines the unique determinant-line purity weight divided by the positive rank. Mathlib verdict: no match after six logged searches (grep, two Loogle searches, LeanSearch, two LeanFinder phrasings).
- citations.json: []. This is a definition with no proof steps, so there are no step citations to quote.
- report.md and searches.jsonl: this report and the actual search-command log.

New nodes: 0. Mathlib leaves: 0. No unit file is changed: this item is the individual irreducible determinantal weight, not the key node sk-d-real-detweights that states the entire unit.

## Attachments

None for this item. I searched the project source under WeilConjectures for the exact blueprint id, determinant-weight phrases and names, and read the candidates in full context.

AlgebraicGeometry.WeilGroup.HasDetWeight (WeilConjectures/EtaleCohomology/Purity/RealSheaves/Weights.lean:120-123) defines a predicate on a proposed real number gamma. It does not construct the unique number a/r or specify finite-coefficient independence. Its docstring belongs to the unit sk-d-real-detweights, already recorded on that unit node. Representation.detWeight (WeilConjectures/AlgebraicGeometry/LinearAlgebraicGroup/Weights.lean:142-143) instead divides the value of a supplied real character at a supplied group element by finrank. Identification with the intrinsic determinant-line purity weight is additional mathematics, stated by lem-rp-determinant-weights-agree. Neither is an exact attachment for this item.

AlgebraicGeometry.WeilGroup.IsLisse.hasDetWeight (Purity.lean:225-238) gives a particular determinant-weight witness under its geometric hypotheses. It is not the definition, uniqueness and coefficient-field clause of this item, and its existence result is already represented by lem-wf-determinantal-weight-exists. No attachment to a partial declaration is claimed. Upstream-master sorry declarations are not treated as proofs.

## WANTED

None. The current blueprint source required for this definition is present.

## Imported issues and corrections

Read the current main-20261015 definition at blueprint/sec-purity-real-sheaves/sk-d-real-detweights/def-wf-determinantal-weight.md, order 2978, and followed its blueprint_update. The imported statement was not false, but left the standing finite-field and coefficient hypotheses and the meaning of irreducible implicit. The delivered statement spells out k_0 finite, ell different from its characteristic, the fixed algebraic closure and iota, the curve convention, normality, geometric connectedness, the lisse Weil representation and r = dim V > 0. These are expansions of the source's standing conventions, not extra hypotheses. Normality is written as local rings being integrally closed domains and cites the existing normal-ring definition rather than the omnibus scheme-properties node, which does not itself define normality.

The construction still uses the unique a from lem-wf-determinantal-weight-exists and exactly a/r. Its finite-coefficient well-definedness remains assigned to the existing lem-wf-determinantal-weight-coefficient-field. I did not create another theorem for either clause or put an unproved assertion into a new definition. The source field and imported flags and blueprint_update are retained; source still records the old import location, while split_report identifies the current source actually read.

## Unfinished work

None for this one-level definition split. The existing coefficient-field lemma remains a separate DAG item, not a claim proved by this delivery.

## Not duplicates

No new nodes were created. Whole-DAG keyword searches and tools/blueprint_refs.py searches for 'determinantal weight', 'determinant weight', 'HasDetWeight', and 'dw_' found the existing individual definition, the broader sk-d-real-detweights unit definition, the real-character definition d-weights, and the multiset/block/compatibility nodes. The unit includes this notion alongside other data, d-weights uses a real character and a degree-one element, and lem-rp-determinant-weights-agree identifies the two definitions. None supplies another complete copy requiring a new node or an attachment here. blueprint.same_as is [].

## Review by Q19

I read the chapter and unit records first, then the main-20261015 definition and both supporting lemma statements. I also read the current coefficient-field proof: extension of the same Frobenius matrix leaves its eigenvalues in the fixed algebraic closure unchanged. This delivery follows the unit's rank-one-purity route by taking its unique determinant weight from lem-wf-determinantal-weight-exists; it does not substitute the algebraic-monodromy real-character route. No SGA source is used.

This is a definition, so there is no numbered proof step and no non-elementary step longer than 2000 characters. Its proof and proof_deps stay empty, proof_origin stays null, and citations.json is the empty list. I checked the statement dependencies themselves, rather than treating their titles as sufficient. def-weil-finite-field-fiber supplies the actual finite-field and ell-not-p convention. def-pc-curve defines a separated integral finite-type one-dimensional scheme, and def-weil-geometric-hypotheses defines geometric connectedness with nonemptiness. def-weil-pbc-normal-ring supplies 'integrally closed in the field of fractions' for the local domains. These make the geometric domain of both determinant-weight lemmas exactly the one used here.

For the sheaf and representation interfaces I read def-pod-lisse-l-adic-sheaves, def-wf-weil-category, def-wf-fundamental-representation, and def-real-weil-representation-operations. The first gives finite-stage lisse coefficients, the Weil-category definition includes the Frobenius datum at finite stages, and the fundamental representation includes the degree-one operator, not just the geometric representation. Irreducibility in the operations node means nonzero simple, so r > 0 does not strengthen the hypotheses. The displayed rank is the dimension of that same stalk representation. No equivalence of different completed or rational coefficient categories is asserted.

I checked the exact two theorem interfaces that make the construction legitimate. lem-wf-determinantal-weight-exists says 'there is exactly one real number a' with the stated determinant-line punctual purity, under precisely normal geometrically connected curve, iota, and irreducible lisse Weil sheaf hypotheses. Thus a is determined, rather than arbitrary data chosen from a bare existence theorem. def-mg-determinant-line defines the rank-one top exterior power with action det(rho(g)); def-weil-punctual-weights defines the condition |iota(alpha)| = q_y^(a/2). No extra weight or integrality restriction is imposed on a.

The coefficient-field lemma states preservation of this same purity weight under an inclusion E subset E', not directly equality for two unrelated fields. I therefore checked the common-extension issue explicitly using def-weil-finite-subextension-directed-set, whose statement gives a finite compositum containing both E and F. Apply the existing coefficient-field lemma to E subset EF and F subset EF; both candidate weights are then weights of the same determinant line, so uniqueness from lem-wf-determinantal-weight-exists identifies them. Rank is unchanged: an r-element basis extends to an r-element basis after scalar extension, and the scalar-extended models both have the given Qbar_l representation as their extension. Hence dividing by the same positive r agrees. This is the elementary application of the cited statements explaining the definition's well-definedness; no new comparison lemma is hidden in the node.

I tested rank one (the value is a itself), the trivial rank-one sheaf (determinant scalar 1 gives a = 0 and weight 0), higher positive rank (the normalization is a/r rather than a or r*a), and coefficients E versus both nested and incomparable finite coefficient fields. The zero representation is excluded by irreducibility, so there is no division-by-zero convention silently defining its weight. The curve is nonempty, so there is no empty-scheme vacuity contrary to the existence lemma's uniqueness. The geometric Frobenius and fixed iota conventions stay those of the existing punctual-weight node.

Finally I checked delivery-errors B through E against the files: there are no new nodes needing additional sources, smallness hypotheses, Mathlib leaves or duplicate-tag pairs; all notions newly spelled out have direct definition citations; existing non-elementary well-definedness facts are cited by their actual statements; there is no restatement child, circular appeal or inline proof hidden as a new unsplit statement. I read all search hits. LinearMap determinant facts, Lie-module weights, number-field regulator determinants and Hilbert 90 do not define punctual purity or normalized determinant weights of Weil sheaves. Searches are recorded exactly as run, including both alternate phrasings. All thirteen direct dependency nodes exist and none uses this item in its statement or proof dependencies. The server dry run is the final mechanical check before pushing.
