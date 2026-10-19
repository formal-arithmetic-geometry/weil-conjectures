# Stage-1 split by Q141

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-ringed-site-finite-free-dual-pullback.json`: statement, split; no exact Mathlib match. Six proof steps, no new nodes and no Mathlib leaves.
- `citations.json`: the current statement of every node cited in every step, copied verbatim.
- `searches.jsonl`: five actual command-generated Q141 searches. `prepare.py` is sandbox-only preparation code.

## Attachments

None. The exact blueprint tag has no hit in the read-only slopmaster2 or upstream master project. Concept searches in slopmaster2 found `SheafOfModules.homObjFreeUnitIso` and `IsFiniteLocallyFree.homObj_unit` in InternalHomFree.lean (the finite free dual and local freeness of the dual), and `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_dual_iso` in EffectiveCartier.lean:224. The latter concerns invertible structure-sheaf modules on schemes and asserts a nonempty isomorphism, not this canonical natural comparison for arbitrary ringed sites and finite local ranks. None states all clauses of this item. No master sorry declaration is treated as a proof.

## WANTED

None. All sources used are present locally.

## Faults and changes

The imported item had a statement and honest prior Q103 searches but no proof. Its statement is preserved exactly. There is no blueprint_update on it. I filled its proof and proof dependencies, retained its ancestry and all existing fields, and added the five actual Q141 searches. The blueprint parent is `det-prop-sfb-cartesian-coefficients-twists`; its current main-20261015 proof's Powers and duals paragraph is precisely the local-free dual comparison being expanded. I read the sec-smooth-purity chapter and sk-prop-an unit records: this support result does not realize the unit statement, so no unit realized fields are changed.

The source 0GN2 has a flatness hypothesis for a general finitely presented first argument. It is deliberately not used here. Finite local freeness gives an explicit inverse even for nonflat scalar extension. The sites are small in the sheaf universe, have the stated finite limits, and the given functor preserves finite limits and coverings. Thus it defines the geometric inverse image and all localization and cover pullbacks used below.

## Searches and existing nodes

I searched all DAG statements and source tags, including 0GMX, 0FNY, finite locally free dual, pullback dual, ringed localization, finite free Hom and cover gluing. Blueprint searches with `tools/blueprint_refs.py` used `dual pullback`, `internal Hom` and `finite locally free`; the ancestor command gives `det-prop-sfb-cartesian-coefficients-twists`. No blueprint node states this arbitrary-ringed-site conclusion. The scheme-only dual nodes and isomorphism-only inverse-image theorem have weaker ambient scope, so they cannot be attached or used as this theorem. All support nodes were already present; no node was created.

The Q141 command log contains two LeanFinder phrasings, LeanSearch, Loogle `"SheafOfModules.pullback"`, and source grep `dual|internalHom|homObj` in Algebra/Category/ModuleCat/Sheaf. All services responded. The hits concern free pullback, unit pullback, adjunction and free-module naturality. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:43-145, especially the unit map at 88, the free comparison at 120 and its basis inclusion formula at 128. They do not give the internal dual comparison, its local reduction or evaluation naturality. Grep found no dual or internal-Hom declaration in that Mathlib directory. I also read the project's InternalHomFree.lean:43-101 and EffectiveCartier.lean:212-229. The former can supply partial finished interfaces but neither whole theorem. Earlier Q103 searches are retained as historical searches rather than relabeled as Q141 calls.

## Not duplicates

No new node is introduced. The existing item differs from `lem-ag-pullback-dual-finite-locally-free` and `lem-sc-picard-pullback-perfect-evaluation`: those concern scheme structure-sheaf modules, rather than arbitrary sheaf rings on sites. It differs from `lem-pur-isomorphism-inverse-image-tensor-hom`, which assumes a scheme isomorphism, and `lem-weil-pbc-etale-pullback-internal-hom`, which assumes an etale scheme map with constant coefficients. No duplicate support fact was extracted: the finite-free coordinate calculations are elementary steps, and localization and gluing cite the existing general lemmas.

## Review by Q141

I read Stacks sites-modules.tex at 0GMX, label remark-pullback-internal-hom, and 0FNY, label example-dual, comparing them with the unchanged item statement and the current main-20261015 Powers and duals paragraph. Remark 0GMX constructs the canonical comparison. The finite-free part of 0FNY is proved by the coordinate formulas here; I do not invoke the omitted summand argument. I also opened 04J0 (lemma-localize-morphism-ringed-sites), 03EL (lemma-tensor-product-pullback), 03EO (lemma-internal-hom-adjoint-tensor), the internal-Hom restriction paragraph, and 03EM's map-gluing statement. Every supporting DAG statement was read in full before being cited. The proof is marked agent-written because it supplies the complete coordinate argument rather than quoting a finished source theorem. There is no SGA source.

Step 1 uses the relative tensor-pullback node for exactly its natural S-linear tensor isomorphism; the closed-tensor node for exactly its symmetry and Hom adjunction; and the Hom and tensor definitions for evaluation and the balancing relation. The unit identification has its explicit inverse and does not presume flatness. Thus the construction is of the canonical map named in the item, not merely some isomorphism.

Step 2 uses the actual module-pullback formula in `lem-weil-pbc-localize-ringed-site-morphism`, not just a site-definition node. Its source and target notation is swapped relative to ours, and its map of rings is exactly the restriction of c. The global geometric inverse image exists by the item hypotheses, and localized sites have finite limits. The site definition supplies the covering axiom; u sends the given cover to a cover and preserves the terminal object. Hom restriction is an elementary relocalization identity: its value at T over V is Hom of the same two sheaves on C/T. Evaluation and the canonical bilinear tensor map have the same restrictions, so the local map computed later is the restriction of delta.

Step 3 cites only the Hom and module definitions. I checked that it actually writes the inverse to the finite-free dual coordinate map: a tuple gives the functional sum a_j x_j on every object, and evaluation at e_j recovers the tuple. Restriction is componentwise. The finite product equals the finite direct sum by the written projection/injection identities. This is an elementary calculation, not a hidden finite-duality lemma, and includes rank zero.

Step 4 uses the geometric-inverse-image node only for finite-product preservation; it is applied to each localized functor satisfying the same finite-limit and covering hypotheses. Scalar extension of the coordinate diagram is computed by two explicit balancing formulas, valid for sheaf tensor after sheafification. The tensor-comparison node identifies the actual evaluation pairing. The Kronecker evaluation equations then force the map to be the identity in the two free coordinate systems, and the inverse formula is written. No exactness of scalar extension, general Hom base change, or unproved local-freeness preservation theorem enters this elementary finite coordinate calculation.

Step 5 uses exactly the existence and uniqueness clauses of `lem-pur-sheaf-hom-cover-gluing`. Here U is the terminal object of D; all its cover pullbacks exist by finite limits. Local inverses agree because both invert the same restricted delta, with the cancellation formula written. Uniqueness of the glued map also proves both inverse identities; it is not an uncited assertion that isomorphy is local. Localization over the terminal object only relabels the sheaf's objects. This covers even an empty covering: the gluing statement then forces the unique maps and inverse identities in the degenerate sheaf category.

Step 6 uses the explicit contravariant action of sheaf Hom, the natural tensor comparison and the natural tensor-Hom adjunction, all present in the three cited statements. Both transposed pairings evaluate phi,a,x by phi(a(x)); injectivity of the adjunction gives the naturality square. It permits different local ranks and requires no chosen simultaneous frame. This verifies the naturality clause independently of any assertion about changing bases.

I tested the unchanged statement and the formulas at rank 0, rank 1, rank 2, varying ranks over a cover, the zero ring, identity inverse image, a module without a global frame, and nonflat Z to Z/2 scalar extension on the one-object site. Rank zero gives zero dual and zero module; the unique zero map is the identity of the zero object. Nonflat scalar extension still gives the identity matrix, as required. No finite presentation of the coefficient map, flatness or enough-points assumption is used. The closure of each of the newly used localization, gluing and closed-tensor nodes does not reach this item, so these citations do not introduce a cycle. Generic off-unit tool uses are explicitly declared in split_report; the purity route is unchanged. All six steps have fewer than 2000 characters (672, 1139, 808, 1183, 727, 812). I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these files: no new-node defects, no clause relabeling, no uncited non-elementary lemma, and no statement dispute remain.

## Unfinished work

None in the one-level split. Server dry run and delivery follow this report; the independent maintainer review remains the project's next stage of validation.
