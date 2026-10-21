# Worker report: lem-wf-tate-twist-frobenius

## Files written

- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-tate-twist-frobenius.json`: statement; split into eight steps; Mathlib has no exact or one-line-specialization match.
- `citations.json`: 18 verbatim statement excerpts, one for each step/dependency pair.
- `searches.jsonl`: six actual Mathlib searches recorded by msearch.py, with both semantic phrasings retained.
- `report.md`: this direct-delivery report and self-review.

New nodes: 0. New Mathlib leaves: 0. No Lean, unit record, repository file or launcher file was written. `prepare.py` is sandbox-only preparation scratch, not a delivery file.

## Attachments

No attachment of the whole item. I read `lean/WeilConjectures/WeilSheaf/StalkTateTwist.lean`, especially `AlgebraicGeometry.WeilSheaf.stalk_frobenius_tateTwistSheaf` at line 76 and its helper at line 65. Its proof has no local sorry and it covers all integer exponents, but its sheaf has coefficients `PadicAlgCl l`, not the finite intermediate field E and raw completed rational coefficient category of the current `def-wf-tate-twist`. Its construction in `WeilSheaf/TateTwist.lean` is the Qbar constant-Weil-twist construction. It is useful evidence for the arithmetic, not an exact attachment of this finite-E item. `ZetaFunction/LissePurity.lean:64` proves only a numerical weight calculation. The project cyclotomic-character theorems in `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:50,68` concern field automorphisms on the cyclotomic character, not the local sheaf formula. None supplies every clause for the coefficient objects here.

## WANTED

None. The current and old blueprint statements and proofs used here are available locally. This expanded proof is marked agent-written; no primary-source proof is claimed for the blueprint's compressed argument.

## What needed repair

The imported statement used X_0 and E without restating the inherited parameters and did not name the precise local-operator convention. I made that inherited setting explicit through the existing definitions, preserving its hypotheses and conclusion. This is the same finite-E assertion as in both snapshots, not a restriction to the Qbar implementation. The original statement dependency list named tensor and internal Hom but omitted the twist definition itself; it now names the twist and local-operator definitions, which introduce all its objects.

The original proof said that inverse-q action on roots gives Q_x^{-1} at a closed point without showing the degree iteration. It also silently passed an infinite root limit through a stalk, and did not check the negative-power inverse in internal Hom or explain why derived twists have the expected degree-zero line models. The split now constructs a global compatible-root basis before taking any fiber, computes the completed and derived operations on free rank-one lattices, and iterates the Weil map through d = [kappa(x):k_0]. No assertion that an arbitrary stalk commutes with an infinite limit is used. The point return is the equality Phi_X^d bar(x) = bar(x) Spec(gamma)^d, as in the current definition, not that a geometric point is a fixed scheme morphism.

I initially considered citing the curve-only roots-of-unity trivialization definition. Reading its statement exposed its curve and etale-site restrictions, so I did not cite it. Step 2 instead gives the short polynomial-factorization proof on the actual pro-etale site. I also explicitly cite `lem-weil-frobenius-point-transport-natural` for naturality, since the point-transport definition explicitly leaves that assertion to its theorem.

## What could not be finished

Nothing in this stage-1 split remains unfinished. The new-node fields and new-node duplicate-pair table are vacuous because every non-elementary input already has a node.

## Not duplicates

No new-node/existing-node pairs. Whole-blueprint searches used `tools/blueprint_refs.py search 'Tate twist'`, `'cyclotomic'` and `'Frobenius on'`, with a DAG keyword scan for roots, signed lines, fiber operations and Frobenius. The ancestor command returns this imported blueprint item itself. The related constant coefficient-twist definition and weight-shift lemma do not state this finite-E local scalar assertion. The item's `same_as` is consequently empty. No replacement wrapper node was introduced for a clause or for an elementary coordinate calculation.

## Mathlib searches

All six entries were obtained with the required Q85/item msearch command and read. Loogle `cyclotomicCharacter` returns the character and its spec/reduction theorems. The second LeanFinder phrasing also returns `cyclotomicCharacter.spec` and the character construction. I read `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:295-335`: these are automorphisms of one domain and their action on algebraic roots, not adic sheaf fibers or signed twists. The first phrasing and LeanSearch return arithmetic Frobenius at ideals, ordinary finite-field Frobenius and standard one-dimensional Witt isocrystals; their returned types use different objects and do not specialize to this item. Grep finds no Tate-twist or cyclotomic-Frobenius declaration in Mathlib; the second grep locates the character file. No unavailable service was recorded as a negative result, and no field-character lemma was mislabelled as a leaf for the sheaf statement.

## Review by Q85

I read the master statement and proof at `sec-algebraic-groups-lie-algebras/sk-p-cyclotomic/lem-wf-tate-twist-frobenius.md` and the current main-20261015 statement and separate `.proof.md`, as well as the chapter record and the cyclotomic unit record/current text. The assertion is unchanged between snapshots. The unit route is roots of unity, their inverse limit, inversion of the arithmetic Frobenius scalar, and extension of coefficients. These are exactly the operations retained here. This item is not the unit's key proposition about Z_l(1) and Q_l(1), so I did not edit the unit's realization fields. There are no new-node sources to audit.

I checked every statement cited by the eight steps, not just its title or proof. Step 1 uses only the field-level primitive-root assertion of `lem-sc-primitive-root`, whose statement has no curve hypothesis, and the compatible-root inverse-limit construction in `def-wf-tate-twist`. I read both snapshots of the primitive-root node and its proof, and the project declaration `IsSepClosed.exists_isPrimitiveRoot`. The parameter n = ell is positive and prime to p. Subsequent roots exist because k is algebraically closed; the displayed order argument shows that arbitrary ell-th-root choices remain primitive. No unproved compatibility of independently chosen generators is assumed.

Step 2 uses the actual root-sheaf and sectionwise limit definitions in `def-wf-tate-twist`. The factorization proof handles arbitrary functions, including disconnected or nonreduced site objects: differences of constants are units, so the principal-open cover forces each root section locally to equal exactly one constant root. The ell-th-power transition identity is written out. The limit is taken as an isomorphism of sheaves; no stalk/limit comparison is needed. This is an elementary argument from the definitions and the chosen primitive roots, not a new lemma being smuggled into a citation.

Step 3 uses the completed B-module identification stated in the twist definition and the K-flat tensor/K-injective Hom models actually stated by the two operation definitions. After the basis isomorphism these inputs are the coefficient unit B[0]. The computations B tensor_B B = B and Hom_B(B,I) = I explain the derived identifications. Completion causes no change for the coefficient unit, which is an object of the specified complete category. This keeps finite E, including ramified E, and does not reinterpret E as a discrete constant sheaf. Positive tensor bases and negative evaluation-dual bases introduce no extra hypothesis.

Step 4 uses the explicit affine formula for Phi in `def-weil-frobenius-detailed`, the roots pullback formula in `def-pur-roots-of-unity-inverse-image`, the strict arrow asserted by `lem-wf-tate-twist-compatibility`, and the lattice/rationalization convention in the twist definition. These statements really specify the maps used. The inverse-q exponents exist because ell does not divide q = p^a; uniqueness modulo ell^r proves transition compatibility. The scheme map is geometric Galois Frobenius, not absolute or relative Frobenius. Its function map sends each chosen constant root to gamma(root), which is its inverse-q power.

Step 5 uses the tensor Weil-map formula of `def-wf-tensor-product` and the left-associated powers and unit of the twist definition. The pure-tensor comparison fixes the chosen tensor of generators, so the positive-power induction is literal multiplication of the scalars, with m = 0 treated separately. Step 6 uses the formula in `def-wf-internal-hom` with the INVERSE first Weil map contravariantly. On a functional this is precomposition by q^h, not q^{-h}. The evaluation calculation checks the sign for negative twists without postulating an unproved arbitrary Hom/fiber comparison.

Step 7 uses `lem-kun-closed-point-field` only for finite residue degree, applicable to the finite-type k_0-scheme X_0. The local Frobenius definition supplies precisely the d-fold Weil map and the semilinear geometric-point return. The point-transport and point-fiber definitions give the actual insertion/section/scalar-extension maps, and `lem-weil-frobenius-point-transport-natural` supplies the naturality used for the chosen basis isomorphisms. I checked its integral and rational coefficient cases. The lattice basis lies in both integral presentations since it is the coefficient unit; evaluating and rationalizing therefore uses the specified fiber formula on these same objects. The unit comparisons send 1 to 1, and coefficient transport fixes the scalar, so no extra conjugation or inverse enters the degree iteration. Step 8 counts a finite vector-space basis to obtain Q_x = q^d and removes the auxiliary choice by conjugation invariance of a scalar operator.

The off-unit proof tools declared in `split_report.tool_uses` are the primitive-root existence statement, the finite closed-point residue-field clause and point-transport naturality; the compatibility lemma is also explicitly listed for clarity and belongs to the item's unit. They provide general prerequisites, not an alternative route to any cyclotomic step. Definitions are used for their explicit constructions, never as stand-ins for theorems about those constructions. The naturality theorem is specifically cited instead of its definition. `citations.json` contains an exact substring of the statement for every cited step/node pair. Dependency closure inspection found no return path to this item through these citations.

Against delivery-errors B--E, I checked: no new unsplit proofs, duplicate nodes or hollow definitions; complete introduced parameters and genuine notion dependencies; actual search logs and candidate object types; no curve-only or etale-only statement applied to the pro-etale scheme X; no lemma used only through its proof; no source tag used in place of a node; no circular use of this local formula through the weight-shift theorem; no new wrapper restating the conclusion. Every proof step is shorter than 2000 characters. The elementary steps spell out polynomial localization, tensor/Hom-on-the-unit calculations and scalar arithmetic; the genuine primitive-root and naturality inputs are cited statements. No SGA source is used.

I checked m = 0 gives the unit identity, m = 1 gives Q_x^{-1}, m = -1 gives Q_x, and a degree-two closed point gives q^{-2m}, not q^{-m}. The case ell = 2 still admits compatible primitive 2-power roots and q is odd, so the inverse residues exist. E = Q_ell and ramified finite E use the same coefficient-unit basis; no comparison of ell-adic and varpi-adic stalk limits is assumed. An empty X_0 has no closed points. No imported mathematical assertion was found false; the repairs fill missing arguments and make inherited parameters explicit.

The server-side preliminary `review_split` check passed with zero new nodes. Final delivery validation is run with the required deliver.py dry run after this report is written.
