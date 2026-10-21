# Worker report: lem-pur-inverse-image-scalar-unit-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-inverse-image-scalar-unit-normalization.json`: existing statement, now split into five steps; no exact Mathlib match for the full statement.
- `citations.json`: eleven step/node entries quoting verbatim the statements used.
- `report.md`: this report and signed self-review.

No new DAG nodes; no Mathlib leaves. No unit or chapter record changed: the item is a subordinate construction, not the unit's key statement.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id, CanonicalRingedTensorComparison, AlgebraicInverseImage, and the scalar-unit terminology found no declaration stating all clauses. The comparison-data structure lives in `lean/Sheaf/Paper/RingedTopoiTensorComparisonData.lean`; it is a definition of the given normalization, not a proof of this item. Its `q_one` and `pure` fields were read to check precisely what is assumed.

## WANTED

None. All sources needed for this split are in the read-only repository.

## What was wrong or incomplete

The imported item had a statement and searches but no proof. Its statement is retained verbatim. The algebraic presentation must realize the specified inverse image on objects and morphisms, so merely citing existence of some module lift would not suffice. Step 1 instead uses the actual transported operations in the specified construction and checks the graph condition by the product comparison. Similarly, a unitor for some abstract monoidal tensor is insufficient without comparison to the specified sheafification tensor: steps 2–4 give multiplication and insertion explicitly and check equality through the sheaf tensor universal property.

The final clause is conditional on an arbitrary *given* normalized comparison. Existence of that comparison is not claimed or used here; in particular the split does not invoke the parent tensor-comparison construction and is not circular. The product test sheaf in step 5 avoids silently identifying a representable with its inverse image. No statement dispute, source correction, or Lean discrepancy was found.

## Sources and searches

Read Stacks `sites-modules.tex`, Tag 03D2 (`lemma-pullback-module`), including its product-transport proof, Section 03EK (`section-tensor-product`), including the sectionwise/sheafified tensor definition and the displayed Hom–Bilin universal property, and Tag 03EL (`lemma-tensor-product-pullback`). Read `sites.tex`, Tag 00YV (`proposition-functoriality-algebraic-structures-topoi`), including the preceding finite-product transport description. Tag/label correspondence was checked in `literature/stacks-project/tags/tags`. No SGA source is used.

Read the chapter and conventions unit records and the current blueprint `main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md`, specifically its final tensor/base-change naturality sentence. The item already names this ancestor and exact place, retained in `blueprint.from`; whole-blueprint searches for `scalar-unit`, `algebraic inverse-image`, `tensor unit`, and `inverse image` found no blueprint statement of the present full assertion. The existing tensor-unit hits concern derived or cochain objects rather than this specified ordinary inverse image and its original unit. No new node was proposed.

The six new Mathlib searches are logged exactly in `searches.jsonl` and appended to the item's existing search history: LeanFinder for the full assertion; Loogle for `ModuleCat.extendScalarsId`; grep for `extendScalarsId|CanonicalRingedTensorComparison|AlgebraicInverseImage` under `Algebra/Category/ModuleCat`; LeanSearch for the sheaf tensor unitor; a second LeanFinder phrasing for finite-product module transport; and grep for `pullback.*tensor|tensor.*pullback|leftUnitor` under `Algebra/Category/ModuleCat/Sheaf`. All six services answered. Read `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:954–974`: `extendScalarsId`, its inverse section formula and forward formula concern ordinary modules over one ring. Read `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:48–84`: `pullback` is the chosen left adjoint to scalar-restricted pushforward. These do not give the full specified-functor/original-unit assertion by one-line specialization. The ordinary scalar calculation is elementary and kept as steps, rather than made into an unnecessary new Mathlib leaf.

## Tool uses

`lem-weil-pbc-left-exact-site-inverse-image-tensor` provides finite-limit preservation for the specific site inverse image, using the base-change and smallness hypotheses already established in `def-weil-proetale-inverse-image`. Only this generic site-theoretic part of its statement is used, not its tensor conclusion. `lem-pc-sites-sheaf-tensor-bilinear-universal` supplies the construction and injectivity of Hom–Bilin for ordinary sheaf tensors. Both are declared in `split_report.tool_uses`; they do not replace any step of the purity unit route.

## Not duplicates

No new nodes. Existing generic facts were reused. In particular no clone of the algebraic inverse-image construction, scalar unitor, or a clause of the item was created.

## Review by NU

I read the source passages named above against the unchanged item. Tag 03D2 transports an arbitrary ring-sheaf module through the finite-product comparison, so the hypothesis is an arbitrary commutative ring sheaf, not a constant coefficient ring or a flatness assumption. Section 03EK constructs exactly the tensor used here by sheafification; 03EL supplies the ringed tensor context, while the normalization/cancellation argument is explicitly agent-written. There are no new statements requiring a separate source review.

In step 1 I opened `def-weil-proetale-inverse-image`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`, and `def-weil-pbc-algebraic-inverse-image`. The first supplies the chosen base-change functor, compatible small sites and universes, original adjunction unit, and transported operations. The second explicitly asserts finite-limit preservation under precisely those finite-limit and covering hypotheses. The third defines the graph equations and natural underlying-sheaf identifications. The proof checks those equations by applying L to an operation equation and checking the product comparison by its two projections. It sets the presentation's module functor to I itself, not a newly chosen isomorphic functor. The same operation transport applies to arbitrary R as in 03D2; it is not scalar extension to a constant sheaf.

In step 2 I opened `lem-pc-sites-sheaf-tensor-bilinear-universal` and `def-pur-sheaf-tensor-product`. The lemma states the full Hom–Bilin bijection, not merely tensor existence or a closed-category name, and therefore constructs a from the written bilinear multiplication formula. The definition gives the presheaf-to-sheaf tensor map used for q. I checked commutativity is available for bilinearity, and wrote the balanced relation proving q is linear. In step 3 the same lemma's injectivity proves the two sheaf morphisms equal from their values after the pairing. Thus there is no unsupported assumption that all global sections are finite sums of pure tensors.

Step 4 uses exactly that injectivity again for the naturality and functor laws, with the actual arrow formula T(f)=1 tensor I(f). The calculation v(bm)=b v(m) uses only module-linearity, so all hypotheses of the tensor lemma are unchanged. In step 5 I read `def-weil-pbc-canonical-ringed-tensor-comparison`, including its generalized pure-tensor equation, and checked the data structure's actual fields. Its q_one condition forces its insertion to be the inverse from step 3. Its pure condition applies with Z the product of the underlying sheaves, x and y the projections and z the tensor pairing. The chosen adjunction unit is natural on *set* sheaves, hence applies to that product Z and to x,y,z; it gives exactly the original unit sections appearing in the item. Applying a tensor a then cancels both q factors. No uniqueness theorem for a possibly different tensor comparison, no stalk detection theorem, and no composite-site identification is needed.

For the small-case review I checked the zero module and zero coefficient ring: the multiplication/insertion equations still hold (every unital module over the zero ring is zero). Empty schemes/sites yield the same tautological sheaf identities and require no chosen point. Disconnected schemes and arbitrary sections cause no problem because every formula commutes with restriction and equality uses the sheaf tensor universal property. Nonconstant coefficients require no basis, trivialization, finiteness, flatness, constructibility or boundedness. If no normalized comparison is supplied, the final universal assertion is conditional as stated. Every proof step is shorter than 2000 characters; none hides a separate non-elementary comparison theorem. The corrections made while writing were to use the product test sheaf instead of a representability assertion, and to quote the original unit sentence specifically for step 5 in `citations.json`.

## Unfinished

Nothing in the authorized one-level split is unfinished. The item uses existing nodes; their own proofs are outside this delivery. Server checks and push are performed by the required delivery command.
