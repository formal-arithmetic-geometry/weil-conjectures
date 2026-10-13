## What changed

Proved `AlgebraicGeometry.alternatingCechSheafComplex_affineSections` in its original module,
with its signature and public imports unchanged. Added a proof-only import of
`Mathlib.Algebra.Category.ModuleCat.Products` and proved private helpers for intersection
sheafness, sheafification units, product evaluation, signed differential compatibility,
pushforward sections, and commutation with extension by zero. Updated the item's DAG proof
to record this actual argument. No definitions or public statements changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.alternatingCechSheafComplex_affineSections`
(node `lem-pc-s3-alternating-cech-sheaf-affine-sections`).
There are no remaining or added sorries, and no split-off statements. The axiom probe reports
only `propext`, `Classical.choice`, and `Quot.sound`. The original module and all helpers
compile cleanly through lcompile.py. The proof works without covering, affine or
quasi-coherence assumptions, including the empty family, empty tuple products and negative
degrees. Every chosen isomorphism is constructed from proved Mathlib results.

## No longer needed

None. Both original public imports and both original DAG proof dependencies are used.
No node or module in the unit route is bypassed. Temporary split-module scaffolding was
removed after proving the sheafification-unit lemma privately; no new module is delivered.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The DAG's observation that the intersection presheaf is
already a sheaf is proved by factoring through the open subspace, rather than by asserting
an over-site identification. No preservation-of-products assertion for sheafification is
needed: the product presheaf is itself a sheaf, so its unit is invertible directly.
The cited tags provide the surrounding Čech and base-change arguments, not an existing
Lean theorem with this exact signature; the termwise construction is checked directly.
LeanFinder and Loogle found only general sheaf and adjunction tools. Local searches of
Mathlib and both library roots found no existing exact complex comparison.

## Second reading by F4

1. **Unchanged interface — pass.** Compared the delivered module against the repository
   with `diff`, and checked the original theorem signature byte for byte through its
   `:= by` delimiter. Its arbitrary scheme morphism, finite family, module, scalar map,
   two integer complexes, and `Nonempty` isomorphism conclusion are unchanged. There is
   no new public declaration, definition change, or changed public import. All ten
   added helpers are private; the product import is proof-only.
2. **Proof and trust — pass.** Independently compiled the complete module with
   `lcompile.py` (8.1 seconds, no diagnostics), and compiled a scratch copy with
   `#print axioms AlgebraicGeometry.alternatingCechSheafComplex_affineSections`.
   The result is exactly `propext`, `Classical.choice`, and `Quot.sound`. Inspected
   every helper and the final composition: no forbidden declaration or attribute,
   no sorry, and no choice from an unproved existence theorem. The module sheaf H
   is built from the explicit presheaf and its proved sheaf condition.
3. **Split statements — pass, none.** No new hole or split statement is delivered.
   For the proved helper statements, checked W empty, r = 0, tuple length exceeding r,
   and degrees -1 and 0: intersection sheafness and product sheafness cover empty
   opens and empty products; the extension comparison uses zero objects outside
   the image and `extendXIso` inside it. In the mixed-degree differential case,
   zero source or target gives uniqueness. No affineness or covering is used.
4. **Shortest route and pruning — pass.** Read the construction module and its
   product and signed-face definitions, then checked each projected differential.
   Evaluation preserves products, the cap comparison is restriction along top
   intersection, and functoriality identifies each face map before signed sums.
   The unit is invertible because each presheaf term is already a sheaf; no separate
   preservation-of-products claim for sheafification is needed. Independent Loogle
   search `"extend", "mapHomologicalComplex"` returned no match; LeanFinder on
   commuting zero-preserving functors with natural-to-integer extension returned
   single-term and support lemmas, not this comparison. Searched the repository's
   two Lean roots and Mathlib's homological embedding files; no direct replacement
   was found. Both original public imports serve the theorem's signature, the new
   proof-only import supplies `ModuleCat.piIsoPi`, and both old proof dependencies
   are used. Thus `No longer needed: None` is complete. Read the unit's `realized`
   record: this item replaces no realized unit statement or step, and retains the
   construction and total-complex route.
5. **DAG agreement — pass.** Read the node's three proof steps against the helpers
   and final proof. The steps record intersection sheafness and the unit, evaluated
   products and differentials, then pushforward/scalars and extension. Their `uses`
   union is exactly `proof_deps`; `proof_origin` describes this argument. There
   are no new nodes needing metadata or source review.

Changed only the report and restored the existing node's `mathlib_searches` to the
repository version, keeping changes to that node within stage-3-owned fields.
No Lean repair was necessary. The original one hole is closed, zero holes are
added, and zero statements are split off; this is a proof, not a decomposition.
