## What changed

Replaced the sole sorry in `Sheaf.CategoryTheory.ColimitSiteFiniteProductSections` with a
complete Lean reduction to one scalar comparison theorem in the new proof-only import
`Sheaf.CategoryTheory.ColimitSiteScalarSectionComparison`. The existing theorem's signature,
visibility and docstring are unchanged. `Mathlib.CategoryTheory.Filtered.Final` supplies
filteredness of `Under i`.

The main module proves the finite-product assembly, rather than leaving that assembly to a
new sorry. Its private helpers handle Arrow endpoint transports, zero-filled coordinate
inclusions, projection factorization, scalar functor/cocone laws, and the filtered-colimit
universal property. Every coordinate has its own supplied stage object; no product of those
site objects is assumed. The new scalar theorem concerns one object and asserts stage
representatives and eventual zero, with explicit transition and cocone laws.

Updated the original node's proof and proof dependencies to match this reduction. Both modules
compile without warnings using lcompile.py. No existing interface changes, adapted modules,
or change records are needed.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.colimitSite_finiteProduct_sections_isColimit`
(node `lem-weil-pbc-colimit-site-finite-product-sections`). There are no sorries in the main
module. This is a decomposition, not a sorry-free proof of the varying-site comparison.

Added exactly one hole, the whole public theorem proof `:= by sorry`:
`CategoryTheory.colimitSite_scalar_sections_representatives_and_zero`
in `Sheaf.CategoryTheory.ColimitSiteScalarSectionComparison`
(node `lem-weil-pbc-colimit-site-scalar-section-comparison`). Its docstring and node give the
source and full mathematical argument. No other new or retained holes occur in this delivery.
Thus the delivery closes one upper hole and adds one strictly smaller scalar hole: net zero
holes, with the finite-product step now proved.

All private helpers are proved. Surjectivity chooses one representative per coordinate and a
common upper stage using `IsFiltered.sup_objs_exists`; injectivity subtracts two representatives,
kills each coordinate, and uses `IsFiltered.wideSpan` for one common killing arrow. The proof
then applies `Types.FilteredColimit.isColimitOf'` and reflects that colimit through the abelian
forgetful functor. These choices are witnesses used in a theorem proof, not data definitions
chosen from unproved mere existence.

Edge cases checked: the empty coordinate type is covered by finite-set upper bounds and
vacuous product extensionality, and wideSpan permits an empty family. For a singleton the
assembly is the scalar assertion. Zero section groups satisfy both scalar clauses using zero
and identity arrows. Empty covers are retained in all statements and in the scalar proof plan.

## No longer needed

No existing import, node or module is pruned from the overall mathematical argument.
The original main node no longer directly invokes
`lem-weil-pbc-colimit-of-sites`, `lem-weil-pbc-colimit-of-sites-sections` or
`lem-weil-pbc-filtered-colimits-commute-finite-limits`: these remain dependencies of the
new scalar comparison. The main module proves the finite-product special case elementwise.
`Sheaf.CategoryTheory.ColimitSites` remains a public statement import.

Removed the trial explicit imports `Mathlib.CategoryTheory.Limits.Types.Filtered` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`; their needed declarations are already
available through the unchanged public import. Removed the earlier sandbox-only Aux module
and its node, which merely packaged IsColimit as Nonempty and did not reduce the original hole.
Those files were never library dependencies and are not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped without implementing the finite-product step. That step can be
stated and proved in Lean using coordinate inclusions, joint injectivity, and common filtered
refinements; this delivery supplies that proof.

`lem-weil-pbc-colimit-of-sites-sections` describes a varying-site section comparison in words,
but its recorded Lean `colimitSite_sections_isIso` only evaluates a supplied diagram of sheaves
on the fixed limit site. It does not compare that diagram to the original varying-stage G
sections. `colimit_site_abelian_section_universality` instead computes the inverse image of
one fixed stage sheaf, and requires sheaf-level comparison maps and unit equations. The
varying-site zero-detection and degree-zero descent interfaces additionally require coherent
pullback isomorphisms (and, for degree-zero descent, Ext and cohomology-map data). None is a
direct instance for the supplied pointwise theta/beta interface. The new scalar theorem states
exactly the missing inner/outer diagonal-comparison step, without copying the finite-product
conclusion or importing the upper theorem.

Read the official source pages for [09YM](https://stacks.math.columbia.edu/tag/09YM),
[09YN](https://stacks.math.columbia.edu/tag/09YN), and
[09YP](https://stacks.math.columbia.edu/tag/09YP). Their scalar inverse-image formula,
iterated-colimit comparison, and finite-product Cech application agree with the reduction.
The unit's realized statements and proof steps are untouched; this is below the unit level.

Mathlib searches used LeanFinder (finite products and scalar representatives), Loogle
(`Types.FilteredColimit.isColimitOf`), and source rg in the filtered-colimit and site files.
LeanSearch for the scalar comparison returned Internal Server Error, recorded as unavailable,
not as evidence of absence. Blueprint searches for scalar sections and 09YN returned no match.

## New nodes

`lem-weil-pbc-colimit-site-scalar-section-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-site-scalar-section-comparison.json`,
states the representatives and eventual-zero consequences of the scalar 09YM/09YN comparison.
Its one new module is `Sheaf.CategoryTheory.ColimitSiteScalarSectionComparison`. It has no
finite coordinate type, product diagram, product isomorphisms, or arbitrary product cocone
universal-property conclusion. The existing argument still must prove that each coordinate
splits naturally and assemble finitely many independent stage and zero witnesses; those steps
are fully proved in the main module. No change record is needed.

## Second reading by R2

1. **Interfaces unchanged — pass.** Read the diff of both delivered modules against
   the repository. The only existing public declaration is
   `CategoryTheory.colimitSite_finiteProduct_sections_isColimit`; its entire signature
   is byte-identical, as is its existing docstring. The public `ColimitSites` import
   remains. Both added main-module imports are proof-only. The scalar module is new;
   no existing definition, target, visibility or hypothesis changed. The existing node
   changes only `proof`, `proof_deps` and `proof_origin`; no change record is required.
2. **Proof and trust basis — pass as decomposition.** Independently compiled both modules
   in import order with lcompile.py, without errors or warnings. Read all six private
   helpers and the main proof: Arrow endpoint equality is handled by
   `Arrow.mk_eq_mk_iff`, scalar projections have explicit zero-filled right inverses,
   and projection factorization justifies scalar naturality before applying the scalar
   theorem. The finite-product proof uses finite upper bounds for surjectivity and
   `wideSpan` for one common killing arrow; subtraction reduces injectivity to zero.
   Inspected Mathlib's `Types.FilteredColimit.isColimitOf'` and `wideSpan` signatures.
   A scratch copy with `#print axioms` checked every private helper and the public
   result. Helpers use only propext, Classical.choice and Quot.sound; the public result
   and scalar theorem additionally use sorryAx. Exactly one named theorem remains
   `:= by sorry`, as listed above. No forbidden declaration or hollow definition occurs.
   All constructed data are explicit maps; choices of stage witnesses occur in proofs.
3. **New scalar statement — pass.** Compared its Lean signature verbatim with its node,
   including rho identity/composition, mu cocone law, beta compatibility, and both Arrow
   transport equations. Read official Stacks 0A34, 0A35/09YM, 09YN, 0738 and 03CO:
   finite stage covers and covering pullbacks give the inner comparison, and finite
   limit sheaf conditions give the outer section comparison. Adjunction identifies the
   transitions with theta. The conclusions are precisely scalar representatives and
   eventual zero; no finite coordinate type or arbitrary product cocone remains.
   It is a strictly smaller step, with a genuine finite-product assembly proved above,
   rather than the item renamed. Checked a singleton index category (identity inverse
   image), zero groups, an empty coordinate type, and a singleton coordinate type.
   An empty source stage has no X and is vacuous. An empty cover forces zero at its
   covered object; if that cover first appears later, the refinement argument, rather
   than an identity-arrow claim, detects zero. Repeated LeanFinder with “inverse image
   sheaf sections filtered system of sites eventual equality stage representatives”:
   only fixed-site gluing results, no varying-site comparison. A Loogle attempt for
   the colimit criterion did not resolve its qualified name; checked its Mathlib source
   directly. Also searched the repository for colimit section and zero-detection
   interfaces and read ColimitSiteSections, ColimitSiteAbelianSectionUniversality,
   VaryingSiteSectionsZeroDetection and ColimitSiteUnitZeroDetection. The first handles
   fixed-site sections, the second one fixed stage sheaf, the third requires extra
   coherent pullback data, and the fourth only unit zero detection. None directly
   supplies both scalar clauses for this varying G/theta/beta interface.
4. **Route and pruning — pass.** The main proof proves the finite-product step directly
   by representatives, rather than adding a second assembly hole. Its only project
   proof dependency is the scalar comparison. All three original proof dependencies
   are now named in “No longer needed”; they remain below the scalar node, and
   ColimitSites remains necessary for public statement vocabulary. No module is
   pruned from the overall argument. Filtered.Final provides Under i filteredness;
   other Mathlib declarations are available from the existing import. Read
   dag/units/sk-thm-p1.json, including every realized statement/step entry: this
   delivery changes no unit and bypasses no realized step.
5. **DAG matches Lean — pass.** Both node `lean.statement` strings equal their module
   signatures. The main node records projection splitting, scalar comparison, common
   stages/arrows and the type-colimit reflection, exactly as implemented. Its
   proof_deps is the scalar node. The new scalar node has source, complete proof plan,
   proof dependencies, search records, split status, worker/item/group/date,
   blueprint ancestry and matching chapter/unit/Lean metadata. Its docstring carries
   the same named source and blueprint id.

Second reading changed only documentation and metadata: added the explicit 0738
finite-cover reference to the new scalar module and node, clarified that empty-cover
zero detection can require refinement, and listed the original colimit-of-sites node
alongside the other two old proof dependencies. No proof or signature needed repair.
One upper hole closed, one scalar hole added: net zero, a decomposition; no claim of a
sorry-free varying-site theorem or pruned module is made.
