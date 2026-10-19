# Stage-1 delivery: d-real-setup (Q108)

## Files written

- `dag/nodes/sec-purity-real-sheaves/d-real-setup.json`: existing definition, split by naming its constituent definitions; no new Mathlib leaf for the combined convention.
- `dag/units/sk-d-real-setup.json`: only `realized` and `realized_by`, binding the unit statement to d-real-setup; the unit has no proof steps.
- `citations.json`: empty list, since a definition has no proof steps.
- `searches.jsonl`: six actual searches, with their results read and recorded verbatim as queries in the item.
- `report.md`: this report.

## New nodes

None. Zero new nodes, zero new Mathlib leaves.

## Attachments

None. Searches of WeilConjectures/ for the exact `(blueprint: d-real-setup)` tag, the setup title, geometric Frobenius and the real-sheaves curve interfaces found no declaration covering every clause. `AlgebraicGeometry.IsCurve` at WeilConjectures/AlgebraicGeometry/Curve.lean:75 allows dimension at most one and does not require smoothness, nonemptiness or geometric connectedness. `IsConnectedCurve` at line 89 still does not impose smoothness or geometric connectedness and does not package the coefficient and Frobenius choices. `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` at WeilConjectures/Mathlib/FieldTheory/Finite/Basic.lean:47 is a genuine construction of the Frobenius component alone, already represented by def-weil-frobenius-substitution. `AlgebraicGeometry.WeilGroup` at RealSheaves/Basic.lean:114 packages different, much larger data, and its documentation explicitly says smoothness is additional. These partial matches are not attachments for this item.

## WANTED

None. All sources needed for this definition are present locally.

## Corrections and source comparison

Read both the current main-20261015 definition file and its identical unit _section.md, and the chapter/unit DAG records. Their statement is a convention, with no proof. The imported node had no statement dependencies, omitted the implicit declaration that p is prime, and left the coefficient macro and the local Frobenius shorthand unexpanded. The delivery makes these explicit, using the current blueprint macro `Qlb` = algebraic closure of Q_ell (blueprint.toml:96), and retains every curve condition verbatim in meaning. The coefficient and local Frobenius expansions make the intended notation explicit. The missing prime assumption is separately flagged below. The chosen embedding is a field embedding only, with no continuity assumption and no new existence assertion.

The local version at a closed point means inverse q_x-power Frobenius of the residue field on its algebraic closure. It does not mean that q-power Frobenius acts on the residue field itself as a generator, nor a Frobenius endomorphism of the curve. No étale fundamental group element or choice of path is introduced here; those belong to the later Weil-group definition. No project Lean or Mathlib declaration states the entire combined convention, so the item is split, not marked mathlib.

## Source error

STATEMENT-DISPUTED: the literal imported setup does not explicitly assume that p is prime, although its intended role is the characteristic prime. If arbitrary integers are allowed, p=4, a=1, q=4 and ell=2 satisfy the displayed numerical restrictions and F_q exists, but its characteristic is 2, not p, and ell equals that characteristic despite ell not equal to p. The faithful repair is to state that p is prime, as the existing global finite-field convention def-weil-finite-field-fiber already does. This is the only hypothesis clarification beyond unpacking notation. No unit proof step is replaced (this definition unit has no steps); the chapter route is untouched.

## Not duplicates

No new nodes to compare. Whole-blueprint searches for Frobenius, smooth curve and the exact setup title found the identical unit definition `sk-d-real-setup`; it is recorded as `blueprint.same_as`. The existing broader finite-field datum, smooth-curve definitions and individual geometric-Frobenius nodes were read rather than copied. In particular def-sc-general-curve requires projectivity, and def-sc-curves allows empty and lower-dimensional curves. Neither replaces this chapter's convention. The current item remains the named realization of its own unit.

## Review by Q108

I checked B through E of coord/delivery-errors.md against the actual item, the current blueprint definition and unit, and the statements of every dependency. Since this item is a definition, there are no numbered proof steps or non-elementary inferences to assign to new lemmas. The proof, proof_deps and proof_origin remain empty/null, and citations.json is therefore empty. There are no steps longer than 2000 characters and no proof hidden in a new node.

For the first clause I read def-weil-finite-field-q-elements (prime p, positive a and the chosen q-element field), def-weil-algebraic-closure (closure with its base-field inclusion), and def-weil-l-adic-numbers (the coefficient field Q_ell). The latter also states properties of its integers that this item does not use. I unpacked the embedding directly as an injective unital field homomorphism; neither continuity nor a prescribed action on Q_ell is imposed.

For the curve clause I read def-pc-scheme and def-weil-scheme-over-base for the scheme and structure morphism; def-weil-proper-morphism for its separated clause only (diagonal a closed immersion); def-sbc-smooth-morphisms for smoothness; def-weil-finite-type-morphism for finite type; and def-weil-pure-dimension for every irreducible component having dimension one. Citing the separated definition in a node also defining properness does not assume properness. I read def-pc-base-change for the geometric pullback and def-weil-connected-scheme for connectedness, including its nonemptiness convention. I retained the source's explicit nonempty condition on C_0, even though the connected geometric base change already rules out the empty curve. I did not replace pure dimension one by dimension at most one or add projectivity.

For the closed-point clause I read def-weil-closed-points, def-weil-residue-field, and def-weil-closed-point-degree. The degree node explicitly gives [kappa(x):k_0] and finiteness and positivity at closed points on finite-type schemes over a field. Those hypotheses are present here. For the Frobenius clause I read def-weil-frobenius-substitution: it defines the q-power automorphism of an algebraic closure of any finite field and its inverse. It therefore supplies both the global definition and its specialization to the finite field kappa(x). The local algebraic closure is introduced explicitly. I did not cite the broader def-weil-frobenius-detailed for a field-only convention, nor confuse scheme, arithmetic and geometric Frobenius.

For affine opens I read def-weil-open-immersion, def-weil-affine-spectrum, and again def-weil-finite-type-morphism. These state respectively the identification with the restricted open subscheme, the spectrum construction, and the finitely generated algebra convention. The definition itself asks for a finitely generated k_0-algebra, so it makes no additional theorem claim about arbitrary open subschemes. All the cited notions are existing definition nodes, so no off-unit proof tool or route change is needed.

I read the Mathlib Frobenius construction at FieldTheory/Finite/Basic.lean:363 and its underlying-map formula at lines 366-367, and the individual Smooth and GeometricallyConnected predicates at AlgebraicGeometry/Morphisms/Smooth.lean:62 and Geometrically/Connected.lean:40. The two semantic phrasings gave arithmetic Frobenius, function-field, number-field-embedding or Weierstrass-curve hits, not this combined convention. The Loogle and two grep searches confirm component interfaces already represented in the DAG; none warrants a new node or an item-level Mathlib match. The six log entries are all successful and their exact queries are retained. No searches were invented or marked unavailable incorrectly.

Small cases: A^1 over F_2 with ell=3 is admitted, and so is P^1, confirming that the curve need not be affine. The empty scheme and Spec F_q are excluded (nonemptiness and pure dimension one). A disjoint union of two affine lines is excluded by the connected geometric base change. A^1 over F_(q^2), viewed over F_q, is connected before base change but geometrically disconnected, so is excluded as intended. The degree-one closed point has q_x=q and the usual inverse q-power Frobenius; a degree-two point has q_x=q^2 and uses the inverse q^2-power map. Empty affine opens remain excluded. These checks do not rely on a new theorem or a choice of a hollow object.

## Unfinished work

None in this one-level definition split. Delivery awaits the required remote dry-run/preflight and push, whose outcomes are recorded below.
