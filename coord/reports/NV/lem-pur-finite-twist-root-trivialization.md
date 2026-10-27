## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-finite-twist-root-trivialization.json: item, statement unchanged, eight proof steps, status split.
- dag/nodes/sec-smooth-purity/lem-pur-primitive-root-etale-basis.json: one new statement-only node, no Mathlib match, upstream attachment candidate.
- citations.json: a verbatim statement quote for every step/node citation.

Attachments: AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf belongs to lem-pur-primitive-root-etale-basis, lean/WeilConjectures/AlgebraicGeometry/Sites/RootsOfUnity.lean:305. Its IsIso proof is AlgebraicGeometry.Scheme.isIso_constantZModToRootsOfUnitySheaf at line 261. The module contains no sorry. This is an attachment candidate for the maintainer's transitive closure check, not a claim that I ran an axiom audit. The item's much larger assertion has no exact project attachment.

WANTED: none.

The imported item was statement-only. Its statement and all original metadata were retained. The curve-specific def-sc-mu-trivialization cannot justify a root basis on arbitrary schemes; the new node records exactly the general theorem the upstream module actually constructs. In particular the proof does not take an assertion about arbitrary schemes from the proof of a curve node. The new node is strictly smaller: it concerns only an ordinary etale cyclic sheaf and has no inverse limit, coefficient ring extension, signed twist, or site-comparison conclusion.

Nothing remains unfinished in this split. One new node remains statement-only with an attachment candidate, as required for one-level delivery; no Mathlib leaves were created. No Lean was written and no compiler, Lake or build was run.

## Sources and searches

I read Stacks etale-cohomology.tex, Tag 03PK, section-kummer: the roots-of-unity functor and its sheaf property; the current blueprint main-20261015/sk-prop-a1-kummer/sk-prop-a1-kummer.proof.md, specifically Coefficients and the final twist sentence of Reduction to a geometric fibre; the current frame-independence proof's elementary-shears paragraph; and def-coefficient-twists-detailed in the current blueprint and the live DAG. The item is an agent refinement of these finite coefficient inputs, not an assertion that Stacks 03PK alone proves the completed or signed statements. Its proof_origin is consequently agent.

For the new node I also read the complete upstream primitive-root isomorphism proof and its constructors at RootsOfUnity.lean:255--314, including the local injectivity and local surjectivity inputs. This construction has arbitrary X over k, no curve or finite-type instance. It takes a specified primitive root, not merely an unspecified local trivialization. The statement is written independently of Lean syntax; m=1 is allowed. Stacks 03PK supplies the root-functor source, while the displayed upstream proof supplies the explicit general-scheme refinement. If the attachment needs a future independent natural-language proof, the interpolation argument is: factor X^m-1 into the distinct factors X-zeta^j; for a root section u the Lagrange polynomials in u are orthogonal idempotents summing to one, so on their open-and-closed pieces u is exactly one zeta^j. Uniqueness follows from the invertible differences zeta^i-zeta^j. This hint is confined to the report, not the unsplit node's statement.

Before introducing the new id I searched all DAG source/tag/statement records and the whole imported blueprint using blueprint_refs.py searches for primitive root, root trivialization, constant roots, root sheaf, and trivialization. I searched the project Lean by the item's tag and by Tate twist, primitive root and roots-of-unity isomorphism names. The only exact general-scheme project constructor found is the attachment candidate above; the DAG notion with the same declaration name is curve-restricted in its actual statement. I read the other candidate node statements (including finite-etale-twist-line, finite-etale-tate-local-line, finite-etale-tate-tensor-family, and affine-roots-representability) before rejecting them as exact substitutes.

All new Mathlib queries were run with msearch.py and recorded verbatim from searches.jsonl. The item searches returned general constant-sheaf criteria, cyclotomic characters, and unrelated text hits; none states the finite geometric comparison assertion. For the new node I ran LeanFinder in two phrasings, LeanSearch with another phrasing, Loogle for rootsOfUnity with constantSheaf, and grep for rootsOfUnity/PrimitiveRoot in Mathlib/AlgebraicGeometry. Loogle and the targeted grep had no hits; the semantic results concern algebraic roots and cyclotomic actions, not the etale sheaf isomorphism. No unavailable query was recorded as a negative result. Existing item searches were preserved.

## Review by NV

I compared the unchanged item's hypotheses against the finite coefficient conventions, the detailed pro-etale tensor construction, the ordinary etale twist construction, and the Stacks root functor. I checked every proof citation against the cited statement itself; citations.json contains those exact statements so that the particular formulas and clauses are visible. The proof distinguishes the discrete constant Z_l used for the initial tensor from the completed limit of constant residue sheaves. It never substitutes the discrete Z_l constant sheaf for that completed limit.

Step 1 uses lem-weil-l-adic-extension-integers-dvr for the actual valuation ring, maximal ideal, and finite residue field, and lem-weil-valued-dvr-finite-quotients(2) for finiteness of the chosen uniformizer quotient. I checked their extending-absolute-value and uniformizer hypotheses. The annihilator is explicitly derived from |ell|<1, rather than assuming the false equality ell=varpi. This works for arbitrary ramification. These two off-unit statements are generic coefficient tools, not replacements for the affine-line cohomology route.

Step 2 takes only the final sentence of lem-pur-affine-line-finite-group-devissage, which explicitly states that the order of a finite abelian group killed by an ell-power is an ell-power. I checked that the stated hypotheses on B, k, ell and a=n hold. No cohomology or freeness of A over Z/ell^n is inferred. Its dependency lists are empty, so this use introduces no cycle back to the item or ordinary invariance.

Step 3 uses the new node for the specified primitive-root etale basis on every T. It then uses the root-only c_m map of lem-amb-finite-root-site-comparison, whose statement says that a root is sent to that same unit. Thus the pulled-back basis really is a -> zeta^a. The comparison node assumes a finite coefficient ring killed by m, supplied by step 1, and m invertible; it explicitly imposes no affine, Noetherian or finite-type restriction. This is a generic site-comparison tool; the unit does not supply its sheaf-level formula.

Step 4 uses the statement of def-pur-sheaf-inverse-limit, which explicitly asserts sectionwise computation. I checked the division formula b_r=a_(r+n)/ell^n using multiplication into ell^n(Z/ell^(r+n)), including its reduction compatibility. The section a_n=0 forces every a_(r+n) into that subgroup. Surjectivity is local, because sections of a constant finite sheaf need only be locally constant; no erroneous assertion of global lifting is made. This is one elementary coordinate calculation from the preceding bases and the cited sectionwise definition, not an application of unmentioned exactness of inverse limits. The quotient is induced by the canonical root projection, hence independent of the auxiliary compatible roots used to check its kernel. Compatible lifts exist since k is algebraically closed; an ell-th root of a primitive ell^r-th root is primitive of order ell^(r+1).

Step 5 expands the two ordinary tensors in def-coefficient-twists-detailed and uses lem-pc-sites-sheaf-tensor-bilinear-universal exactly for the balanced maps. I checked both reassociation formulas and that changing a lift of a finite root by my changes x tensor a by zero. The sheaf gluing follows because this difference vanishes on every overlap. This proves the tensor quotient formula by explicit inverses and does not invoke tensor exactness. The universal-property node is an off-unit generic tool because the unit has no sheaf-tensor construction theorem.

Step 6 takes the positive-power and internal-dual definitions from def-coefficient-twists-detailed, def-pur-sheaf-hom, and the explicit signed realization in lem-asd-etale-finite-twist-pullback. I checked that the inverse on a dual is evaluation at the positive basis, on every slice site. This proves the dual comparison in this free-line situation without assuming that inverse image commutes with arbitrary internal Hom.

Step 7 uses the actual root/pure-tensor pullback equations of lem-amb-finite-root-site-comparison. It uses lem-amb-finite-tate-site-descent only for the nonnegative detailed-twist comparison, precisely the range its statement gives. Negative degrees are checked by the evaluation formula from step 6; they are not silently taken from that nonnegative theorem. Both comparison nodes are generic tools for the two sites; the unit's affine-line argument cannot replace their root-projection identification. Evaluation on a basis proves the identities and composition assertions, so no unspecified transport is used.

Step 8 uses the final exponent-independence clause of lem-asd-etale-finite-twist-pullback and the power compatibility of lem-amb-finite-root-site-comparison. I checked the exponent is common to both rings, and that a map of finite coefficient rings fixes integers, hence the common Z/ell^a scalars. The actual formula on a negative dual and its inverse are displayed. In particular a quotient of coefficients preserves a basis without any flatness hypothesis. These are equations on the basis itself, not just an assertion that the endpoints are isomorphic.

For B1--B7 I checked that the sole new node is self-contained and statement-only, with field, primitive order, integer positivity, arbitrary scheme, root sheaf, scalar action and topology all specified. Its primitive-root condition is inline, its other notions have statement dependencies, and TeX is singly escaped. It carries the correct nearest blueprint ancestor and the full via chain; same_as is empty because the curve definition and existence of an unspecified local basis do not state the same assertion. No human target or chapter/unit statement was changed. The source identifies both Stacks tag/label and the upstream refinement. I corrected the IsIso source line from the docstring line 260 to theorem line 261 when reading numbered source.

For E1--E6 I tested empty T, a disconnected T, a nonreduced T, arbitrary ramification, n=1, r=0, positive and negative r, differing annihilating exponents, and a nonflat quotient A -> A/(varpi). The new root-basis node also permits m=1 and non-algebraically-closed k when the specified primitive root exists. For a nonreduced scheme the differences of distinct field roots remain units, so the local root decomposition remains valid. All quotient formulas use finite sheaf labels locally, not connectedness or reducedness. There is no statement dispute or source correction. Every non-elementary step is shorter than 2000 characters; the longest step, the elementary residue-coordinate quotient computation, is 1145 characters. I found no hidden comparison lemma left in a long step.

## Not duplicates

lem-pur-primitive-root-etale-basis vs def-sc-mu-trivialization: the existing definition is restricted to curves over an algebraically closed field; the new theorem applies to every scheme over any field containing the specified primitive root. Its statement also explicitly requires primitive order, absent from the final sentence of that imported definition.
lem-pur-primitive-root-etale-basis vs lem-sc-primitive-root: the existing result supplies roots in an algebraically closed field and their field-extension behavior; it does not state the root-sheaf isomorphism on an arbitrary scheme over a possibly nonclosed field.

lem-pur-primitive-root-etale-basis vs def-pur-kummer-module-coefficients: defines tensor coefficient sheaves and insertion maps for modules; does not trivialize a specified root sheaf globally.

lem-pur-primitive-root-etale-basis vs lem-asd-finite-etale-tate-line-comparison: compares pullbacks of coefficient lines; does not supply a specified primitive-root basis.

lem-pur-primitive-root-etale-basis vs lem-asd-normalized-signed-tensor-family: normalizes powers of an abstract invertible object; has no scheme or root-basis theorem.

lem-pur-primitive-root-etale-basis vs def-pur-kummer-line-geometry: defines the affine line and punctured-line geometry and boundaries; not the root basis for arbitrary schemes.

lem-pur-primitive-root-etale-basis vs def-asd-finite-etale-tate-sheaf: defines signed twists and local tensor generators; does not prove the cyclic root basis is invertible.

lem-pur-primitive-root-etale-basis vs lem-asd-int-tensor-family-comparison: extends a given degree-one comparison in monoidal categories; does not construct the primitive-root degree-one map.

lem-pur-primitive-root-etale-basis vs def-pur-finite-tate-site-comparison: defines finite comparison data and generators; does not assert this primitive-root basis theorem.

lem-pur-primitive-root-etale-basis vs lem-asd-etale-finite-twist-pullback: gives local freeness and pullback/exponent comparisons for finite twists; not global invertibility of the map defined by a specified primitive root.

lem-pur-primitive-root-etale-basis vs lem-pur-twist-root-local-models: gives existence of local unit trivializations and completed reductions; not the specified root basis on any scheme over its field.

lem-pur-primitive-root-etale-basis vs lem-pur-finite-twist-root-trivialization: the item includes valuation-ring arithmetic, an inverse-limit quotient, scalar extensions, signed twists and two-site/coefficient compatibility; the new node is just the independent etale cyclic root-basis tool.

lem-pur-primitive-root-etale-basis vs lem-pur-kummer-root-line-computation: computes cohomology and Kummer generators only on the affine line and multiplicative group; does not cover arbitrary schemes.

lem-pur-primitive-root-etale-basis vs lem-amb-finite-tate-site-descent: compares finite etale and pro-etale Tate lines and their nonnegative powers; not the root-basis theorem with a specified root.

lem-pur-primitive-root-etale-basis vs lem-pur-integration-exponent-transpose-transport: is a derived integration/exponent comparison theorem on finite-type schemes; not this root-sheaf isomorphism.

lem-pur-primitive-root-etale-basis vs def-pur-roots-of-unity-sheaf: defines the pro-etale kernel sheaf; does not state the etale primitive-root basis.

lem-pur-primitive-root-etale-basis vs lem-pur-twist-integral-local-models: concerns completed integral and finite tensor local models; not the globally specified etale root basis.

lem-pur-primitive-root-etale-basis vs def-asd-finite-etale-tate-twist: defines scalar extensions and powers; does not prove the specified cyclic root-basis map invertible.

lem-pur-primitive-root-etale-basis vs def-pur-twist-sheaves: constructs pro-etale inverse-limit and scalar twist modules; no etale primitive-root basis assertion.

lem-pur-primitive-root-etale-basis vs lem-asd-finite-etale-tate-local-line: asserts existence of a cover trivializing a coefficient line; does not identify the particular map from a prescribed primitive field root.

lem-pur-primitive-root-etale-basis vs lem-pur-twist-root-transitions: asserts epimorphy of successive root transitions; not triviality from a specified primitive root.

lem-pur-primitive-root-etale-basis vs def-asd-etale-roots-of-unity: defines the etale root functor; no primitive-root isomorphism assertion.

lem-pur-primitive-root-etale-basis vs lem-asd-etale-finite-twist-pullback-base: packages local trivializations and tensor coherence, not the specified field-root basis for all schemes.

lem-pur-primitive-root-etale-basis vs lem-asd-finite-etale-twist-line: asserts existence of local trivializations of nonnegative coefficient twists, with no chosen-root global basis.

lem-pur-primitive-root-etale-basis vs lem-pur-twist-sheaf-locally-free: supplies local root and completed Tate trivializations and reductions, not the prescribed field-root etale isomorphism.

lem-pur-primitive-root-etale-basis vs lem-asd-finite-etale-tate-tensor-family: constructs signed tensor families trivialized on a cover; not the specific global field-root map.

lem-pur-primitive-root-etale-basis vs lem-sp-etale-pullback-twist-tor-window: compares pulled-back twisted derived objects and Tor windows on finite-type schemes, not this root basis.

lem-pur-primitive-root-etale-basis vs def-amb-finite-tate-site-comparison-data: defines nonnegative comparison generators and models; no root-basis invertibility theorem.

lem-pur-primitive-root-etale-basis vs lem-asd-affine-roots-representability: represents roots by Spec(R[t]/(t^n-1)) for arbitrary R; does not split that scheme by a specified field primitive root.

lem-pur-primitive-root-etale-basis vs lem-asd-etale-finite-twist-pullback-rest: packages remaining derived and exponent clauses assuming base data; no specified primitive-root basis theorem.
