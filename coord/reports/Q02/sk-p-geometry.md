# Worker report: Q02 / sk-p-geometry

## Files written

- `dag/nodes/sec-algebraic-groups-lie-algebras/sk-p-geometry.json`: statement, split in ten proof steps; no Mathlib match for the whole item.
- `dag/units/sk-p-geometry.json`: only `realized` and `realized_by`, binding the unit statement and its single original assembly step to this item.
- `citations.json`: a verbatim statement quote for every step/node citation. The quotations are the complete cited statements, so the review below specifies the particular clauses actually used.
- `report.md`, `searches.jsonl` and the sandbox-only reproducible writer `write_split.py`.

There are **0 new nodes and 0 new Mathlib leaves**. The existing nodes needed for the argument were found before creating any replacement. There was no pre-existing item, report or search log in this sandbox; only the dispatcher's brief markers were present.

## Attachments

No new attachment is claimed. In particular I do not repeat the previously rejected attachment for the whole item. The live library has extensive implementations of the component, image and dimension interfaces, but the mathematical split here does not infer completeness from a theorem whose immediate body contains no `sorry`. Existing general Cartier and identity/local-dimension nodes are cited under their own statements.

## WANTED

None. All sources used for this split are available in the named literature directory.

## Statement corrected

**STATEMENT-DISPUTED: the imported statement is not self-contained without the standing field and finiteness conventions.** Over an algebraically closed field of characteristic p, the proper closed subgroup scheme alpha_p of G_a has Lie(alpha_p) = Lie(G_a), both one-dimensional, but alpha_p is not G_a. Over the reals, even the rational-point image of squaring on G_m is the positive real numbers and is not a Zariski closed subgroup of the real points. Finite type is also needed for component finiteness (the constant group scheme Z is a counterexample without it).

I read the newest blueprint through `literature/blueprint/latest/`, which points to `main-20261024`, specifically the sk-p-geometry statement and its three-paragraph proof, and the sk-i-cartier statement immediately providing its context. The latter says explicitly: L algebraically closed of characteristic zero; algebraic group means a finite-type group scheme, not necessarily affine. I restored exactly that context in the item. All originally imported clauses remain verbatim. The original unit's matrix-group clauses remain special cases.

I also made the meaning of equal Lie algebras explicit: it is the differential of the given inclusion which identifies them, and the first image assertion concerns the underlying scheme image with its reduced subgroup structure. This matches the blueprint's own passage between scheme images and L-points. Connectedness is harmless under the two existing conventions: every group scheme here is nonempty because it has an identity section.

## What was wrong or incomplete

The imported proof had empty `uses` lists and unjudged elementary flags throughout. It used Cartier, component finiteness, regular local domains, constructibility, an open piece in a constructible image, and dimension drop without their actual DAG statements. It also switched directly from a constructible scheme image to an image of L-points. A nonempty fibre over an L-rational point needs a rational point of its own; step 6 now supplies that argument. Step 8 then explicitly recovers closedness of the underlying scheme image.

The older `lem-ag-cartier-reduced`, `lem-ag-homomorphism-image-closed`, `lem-ag-equal-dimension-subgroup` and `lem-wf-same-lie-closed-subgroup` have Qbar_l/matrix hypotheses. They do not by their statements prove the arbitrary-L, possibly non-affine version of this item. In particular I did not cite the matrix Cartier node to make a false hypothesis match. The general Cartier, identity-component and groupoid closure nodes already exist elsewhere in the DAG and supply precisely the broader statements needed here.

The source's phrase that continuity makes the closure a group suppresses both the product-image issue and the reduced scheme structure. Step 4 uses the existing perfect-field groupoid image-closure theorem, specializing a group scheme to an absolute groupoid with the single object scheme Spec L. This is the same closure step, not a replacement route for the Chevalley argument. No assertion that the underlying scheme product has the product topology is used.

## Not duplicates

No new node was created. Searches of the whole DAG by the tags 047N and 047M, by Cartier, identity component, closed image, local minimal prime, constructibility and dimension, and blueprint_refs searches by the corresponding concepts found existing generic tools. In particular:

- `lem-sfb-cartier-characteristic-zero-smooth` supplies arbitrary characteristic-zero fields, unlike the older matrix-only Cartier node.
- `lem-sfb-locally-algebraic-group-identity-component` supplies a geometrically irreducible identity subgroup for locally finite-type group schemes.
- `lem-sfb-perfect-field-groupoid-image-closure` supplies the reduced closed groupoid structure needed on the image closure.
- `lem-ag-smooth-lie-local-dimension` and `lem-ag-group-identity-local-dimension` together supply the two distinct dimension equalities; no new wrapper repeats them.

The blueprint search for the item's title and for equal Lie / closed subgroup statements found matrix special cases but no other node stating the full general bundle, so `blueprint.same_as` is empty. This is an imported blueprint item: `blueprint.from` remains null as required.

## Review by Q02

I checked delivery-errors B through E against the actual files and their cited statements, and corrected the missing hypotheses and the rational-point/scheme-image distinction above. The literature I read for the item was the current sk-p-geometry statement and proof and the current sk-i-cartier context, supplemented directly by Stacks `groupoids.tex` at Cartier (047N), the geometrically irreducible component argument (047M), and the identity subgroup proposition (0B7R); `more-groupoids.tex` at the perfect-field image-closure theorem (04Q8) and its preceding product-image argument; `morphisms.tex` at Chevalley (054J/054K); `topology.tex` at the dense constructible open argument; and the reduced-closed-subscheme and Noetherian-topology sources. There are no new nodes whose sources still need checking.

**Steps 1–2.** I read the statements of all ten cited nodes. The finite-type-over-Noetherian node supplies precisely Noetherianity, and the finite-component and component-cover nodes supply the finite family covering G. The domain argument uses the general Cartier node, smooth-implies-regular, and regular-local-domain. I did not apply the affine-only smooth-component node to a non-affine group: instead the proof takes an affine neighbourhood of a proposed intersection. The open-component injection node makes its two components distinct on that neighbourhood, the spectrum/minimal-prime node identifies their primes, and the localization correspondence together with the stalk-localization node carries distinct minimal primes to the local domain. Thus the argument is valid without affineness of G. The remaining finiteness and clopen-component deductions are written out.

**Step 3.** I checked that the identity-component node really supplies both the subgroup structure and geometric irreducibility, not just an underlying component definition. Its locally finite-type and algebraically closed hypotheses hold. A nonempty affine open is quasi-compact and T0, so the closed-point existence node applies there; the affine Nullstellensatz then gives an L-point. The translation node supplies an actual scheme isomorphism. For normality, the product node requires geometric irreducibility of both factors: each translate of C has it, and C has it by the identity-component node. Conjugation on every piece has connected image containing 1, and the open-factorization node turns the resulting support containment into a morphism to C. This proves normality over arbitrary test algebras, not merely on L-points.

**Step 4.** I read both the definition of an absolute groupoid and the exact general image-closure statement. Taking the object scheme to be Spec L identifies it with the group case. L is perfect because it has characteristic zero. The theorem supplies the reduced closed subgroup on the closure of the scheme image, exactly what this step uses. Cartier supplies reducedness of the source for the reduced-source factorization theorem. Monomorphy of the closed inclusion ensures the factor is a homomorphism. No claim is extracted from the proof rather than the statement of that closure theorem.

**Step 5.** The finite-type and Noetherian arguments are explicit on affine charts: L-generators of B are still generators over A. The open-Noetherian node gives quasi-compact inverse images, and the locally-Noetherian finite-type/presentation node supplies local finite presentation. The group-separatedness node applies to J now that step 4 has given it group operations. Thus every hypothesis of the cited scheme-level Chevalley node (quasi-compactness, local finite presentation, and qcqs target) is established. I did not apply affine Chevalley to a non-affine map. I only apply clause (2) of the affine constructible-open node after restricting its already constructible image to an affine open, with the restriction node cited.

**Step 6.** The finite-type base-change node applies to the nonempty fibre over u because step 5 established finite type of q. The closed-point existence and affine Nullstellensatz nodes are used on a nonempty affine chart of that fibre, not on a non-affine scheme assumed affine. Translation supplies the inverse and the equality of the translated L-point sets. This checks the gap between the scheme image and P = q(G(L)).

**Steps 7–8.** The rational-density node assumes a smooth scheme over a separably closed field: Cartier makes G smooth, and algebraically closed L is separably closed. Continuity therefore makes q(G(L)) dense in J. The displayed unions of translates show P and its cosets open in J(L), and hence P closed there; this is a direct subgroup calculation. Step 8 separately uses a finite union of locally closed pieces for the constructible complement. A nonempty piece has an affine chart and hence an L-point by the same two cited closed-point/Nullstellensatz statements. Such a point cannot exist since P = J(L). This proves equality with the scheme image and not only equality on rational points.

**Steps 9–10.** I read the smooth Lie/local-dimension and identity/global-dimension statements separately. The former assumes a smooth group; the latter only finite type. Cartier applies to K as a closed subgroup scheme as well as to G. Their combination gives exactly the equality of dimensions from the differential of inclusion. Finite dimension is supplied by the finite-type-dimension node. Connected G has already been proved irreducible. If K had proper closed support, that support would be nowhere dense, so the cited finite-dimensional Noetherian dimension-drop statement applies. Finally, the reduced-induced-closed-subscheme node's uniqueness clause, not an unstated rule that supports determine all closed subschemes, identifies the two reduced closed subschemes. For the complement the same argument starts from its assumed dimension equality.

I tested G = Spec L, finite disconnected constant groups, a connected additive group, zero-dimensional connected groups, and GL on a zero-dimensional vector space. The identity prevents empty-group edge cases. Without connectedness a proper subgroup of a finite constant group has the same zero Lie algebra, so that hypothesis is retained. Without reducedness equal support does not imply equality (Spec L[epsilon]/epsilon^2 versus its reduction); step 10 explicitly invokes Cartier to prevent that error. The characteristic-p alpha_p example above checks the corrected characteristic assumption. None of the ten non-elementary steps exceeds 2000 characters, and none hides an uncited comparison or new standalone lemma.

I read all actual results of the logged searches. The two item phrasings return topological connected components, path components and manifold Lie groups, not this scheme theorem. Loogle on scheme/Lie and the source grep return no matching declaration. LeanSearch's closed-map results need unrelated hypotheses such as universal closedness, so none is a one-line specialization proving this item. The exploratory Cartier searches found Mathlib's `smooth_of_grpObj`, whose source additionally requires geometric reducedness; the existing project Cartier node provides precisely the stronger theorem needed here. No service failure was recorded as mathematical absence.

The off-unit dependencies are declared in `split_report.tool_uses`. They are generic scheme, topology and commutative-algebra tools, used within the unit's specified Cartier/components, Chevalley/translates and dimension-drop route. No SGA source is used. No Lean file was written and no compiler, Lake or build command was run.

## Unfinished work

None in the one-level stage-1 split. Existing unsplit supporting nodes remain their own future items. Server dry-run and push results will be appended below after the commands exit.

## Validation

The server-only `srvcheck.py ... review_split` exited successfully: PASS, 0 new nodes, unit realized, generic tool uses declared. The full `deliver.py Q02 sk-p-geometry --no-push` then exited with `OK (not pushed)` at e72cf56deed; server preflight passed and the durable dry-run receipt was saved. The push invocation is the final delivery step.
