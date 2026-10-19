# Q46: lem-per-vector-extension-splitting-cohomology

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-vector-extension-splitting-cohomology.json: statement, split into nine steps; no Mathlib theorem covers the item.
- dag/nodes/sec-deligne-laumon-a1/lem-per-affine-space-global-functions.json: statement, Mathlib leaf; AlgebraicGeometry.AffineSpace.homOverEquiv, Mathlib/AlgebraicGeometry/AffineSpace.lean:153, with naturality comp_homOfVector:140.
- dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-affine-line-unit.json: statement only, unsplit; no Mathlib match after the logged searches.
- citations.json: one verbatim quotation for every step/node citation.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source by the item tag and splitting-scheme, extension, affine-line and cohomology terminology, and searched dag/lean_names_upstream.json. No declaration of the project states the item or the new affine-line theorem. The coordinate equivalence is in Mathlib, so it is a leaf rather than an attachment. Master sorry declarations are not used as proofs.

## WANTED

None. The source used for the item and the affine-line input is available: Illusie–Laszlo–Orgogozo, Expose XVI, Proposition 1.5, printed page 227. Its local affine-space route is followed. The affine-line input is left as a separate mathematical statement, not claimed to have been proved here.

## Audit and changes

The item initially had no proof. Its statement agrees with Proposition 1.5 and is unchanged. The universal splitting and translation clauses require an actual representing construction, which steps 1–4 now give. The Noetherian and twisted consequences are expanded separately.

The main hypothesis trap is the existing lem-pur-affine-line-ordinary-invariance: it permits arbitrary k-schemes but its k is a fixed field with the purity conventions. It cannot be applied to an arbitrary Noetherian X in this item. I created only the one-dimensional arbitrary-Noetherian-base unit input and used induction for higher affine dimension; I did not silently add a field or regularity assumption to X. This input has its own hypotheses and no vector-bundle extension in its statement. It is not a relabelled clause of the item.

The other new node is the general affine-space coordinate universal property already in Mathlib. It is not the particular representing scheme of splittings. Existing local-splitting and scheme-gluing nodes are reused. No new node is created for uniqueness of differences, finite-cover Noetherianity, composition of units, or the twist consequence: their arguments are written in the proof steps from the cited statements.

All Mathlib searches were made through msearch.py and read. The homotopy searches returned etale-morphism APIs, Gamma-Spec adjunction isomorphisms, and IsHomotopyInvariant for topological homology; none gives the etale cohomological theorem. I read the homOverEquiv and comp_homOfVector source, and the topological IsHomotopyInvariant declaration, to distinguish those hits. One Loogle query used the unknown identifier IsIso; this is recorded as an invalid query, and a corrected CategoryTheory.IsIso query was run and inspected. Its sole affine-space isomorphism hit concerns zero-dimensional affine space, not derived direct image.

## Not duplicates

lem-per-noetherian-affine-line-unit vs lem-pur-affine-line-ordinary-invariance: the new input is for Noetherian schemes over Z[1/ell] with no field structure; the existing statement requires the finite purity datum and a k-scheme. The latter additionally treats twists and the pro-etale site, which the new input does not.

lem-per-noetherian-affine-line-unit vs lem-pur-a1-direct-image: the existing blueprint statement requires a separated finite-type k-scheme in fixed purity conventions. It does not cover an arbitrary Noetherian scheme.

lem-per-noetherian-affine-line-unit vs prop-pur-a1-invariance: the latter is also restricted to separated finite-type k-schemes, and states the cohomological invariance in that setting.

lem-per-affine-space-global-functions vs def-sbc-affine-space: the existing node defines the polynomial scheme and its affine charts; it does not state the bijection for all test schemes or its naturality. The new node records exactly the Mathlib bijection and composition formula.

I searched the whole DAG by homotopy, affine line, splitting, coordinates, homOverEquiv, the proposed ids, and scheme-gluing tags, and used blueprint_refs.py searches for homotopy invariance, homotopy, affine line, affine-space global sections, splittings and splitting. No blueprint node states either new result with these hypotheses. The existing glue-schemes node (01JB/01JC), scheme-morphism-gluing node, local-splitting node, affine trace tower and localization tools are cited rather than recreated. There are no new Stacks-tagged nodes and hence no new same-tag pairs.

## Review by Q46

I read Proposition 1.5 and its surrounding geometric splitting discussion on printed pp. 226–227 in the available ILO PDF. I also read the current chapter/unit records, the blueprint ancestor, the existing affine-line invariance statement with its field assumptions, and the statements of every node cited below. For the coordinate leaf I read Mathlib/AlgebraicGeometry/AffineSpace.lean lines 140–161. For the other new node I read the exact homotopy-invariance sentence of Proposition 1.5; I isolate only its affine-line input, retaining the stated invertible-coefficient condition and arbitrary scheme base. That input is intentionally unsplit. The Stacks material I consulted for the expansion was schemes.tex, lemma-glue and lemma-glue-schemes (01JB, 01JC); sites-cohomology.tex, lemma-cohomology-of-open (03F3); the exact localized extension-by-zero adjunction (03DJ); and morphisms.tex, lemma-finite-type-noetherian (01T6). I did not use a forbidden purity or trace route.

Step 1 uses the actual statement of lem-sc-local-splitting-finite-free, after restricting to constant-rank neighborhoods, and def-amb-finite-locally-free-module for the frames. The pullback tensor formula in def-pc-module-pullback sends split identities to split identities. Thus arbitrary test morphisms are allowed: there is no unjustified preservation of a nonsplit exact sequence by a nonflat pullback.

Step 2 takes precisely the natural coordinate bijection from the new Mathlib leaf. In split coordinates q is the projection, so every section has lower block identity and arbitrary upper block. This works on arbitrary test schemes through global functions; an affine-only representing argument would not suffice.

Step 3 uses that same coordinate bijection to turn changes of frames into morphisms. It checks the inverse and triple cocycle by their effect on sections. The existing glue-schemes statement supplies the glued scheme and its open charts. The existing scheme-morphism-gluing statement supplies the projection. I checked that neither citation requires the overlaps to be affine, and that all transitions are over the overlap in X.

Step 4 uses the morphism-gluing statement exactly for maps from the open covering of a test scheme. Gluing module maps is written directly on sections using the sheaf axiom. The universal section and unique difference follow from the displayed split coordinate formulas, including injectivity of j after arbitrary pullback as established in step 1. This is an elementary step relative to the previously constructed charts, rather than a new torsor lemma.

Step 5 uses the affine trace tower statement for Noetherianity of each affine-space chart and its intermediate coordinate stages; pqf-def-locnoeth supplies the local meaning of Noetherianity. The finite subcover from step 1 makes the finite affine Noetherian cover of S explicit. In particular the argument does not confuse locally Noetherian with Noetherian.

Step 6 uses enough-injectives in the ordinary etale fixed-ring module category. The etale-site localization node identifies the slice topology with the small site of V; transporting the coefficient actions gives the corresponding module identification. The exact extension-by-zero/restriction adjunction node says exactly what is needed for the written injective-lifting argument. The direct-image definition evaluates both sides on W by the same fibre product and the same complex. This proves the needed derived localization and compatibility with the actual unit, without appealing to an unnamed base-change theorem.

Step 7 uses the new one-dimensional affine-line unit only at Noetherian coordinate stages where ell remains invertible. The affine trace tower states both properties. Clause (5) of lem-weil-derived-direct-image-composition is for ordinary small-etale categories and any commutative ring; I explicitly avoided its different pro-etale/integral clauses. The transpose computation checks that the composite of units is the named canonical unit. The d=0 base case is the identity.

Step 8 uses geometric-stalk conservativity only on abelian cohomology sheaves, then the cohomology criterion for the derived isomorphism; module inverses are checked to remain linear. The finite-twist node states local rank-one freeness for positive, zero and negative twists and canonical inverse-image compatibility. Step 6 permits restriction to its etale trivializing objects, so no global primitive root and no finiteness condition on those objects is smuggled into the argument. The constant unit on such an object is restriction of the already-proved constant unit, rather than a new invocation of the Noetherian affine-line input.

Step 9 uses the exact inverse-image/direct-image adjunction to prove preservation of injectives by the right adjoint, then the literal direct-image section formula. The etale-cohomology definition computes the resulting groups. The twist-pullback node supplies the canonical coefficient identification on the target. Thus the cohomology isomorphism is the specified pullback for every q and signed t, not just an abstract isomorphism between two groups.

I tested empty X, zero ranks a or b, a=b=1 over a field, a split extension over an arbitrary ring with ell inverted, nonreduced base rings, mixed characteristic, n=1 and t=0,-1. When a or b is zero there is a unique section and S=X; the affine tower starts at dimension zero, so the unit is the identity. Nonreduced or mixed-characteristic bases require no extra step beyond the separately stated homotopy input. All new unsplit nodes have empty proof and proof_deps. No proof step is longer than 2000 characters. The item proof is not moved into either new node; all splitting-specific constructions are steps 1–4. I checked C1 and C4 by matching each use to its cited statement, and wrote those exact statements verbatim into citations.json. Generic off-unit tools are declared in split_report.tool_uses. The original blueprint provenance, citations and search records are retained.

## Unfinished work

No part of this one-level split is omitted. The arbitrary-base affine-line theorem remains the single new unsplit input, as required for newly created non-Mathlib nodes. No Lean was written or compiled, no live repository or launcher file was changed, and no agents were started.
