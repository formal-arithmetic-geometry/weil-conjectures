## What changed

The item's signature and all its existing public imports are unchanged. Its proof now
uses an explicitly constructed increasing-tuple module-sheaf complex and augmentation.
Three proof-only imports supply the proved term comparison and the two remaining
intermediate theorems.

New module `Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction` constructs
intersection module presheaves using restriction of rings and Mathlib presheaf
pushforward. It constructs their finite products and signed face differential, proves
d-squared-zero by a bijection pairing the two deletion orders, and proves the
zero-degree augmentation identity. Degreewise module sheafification gives the actual
complex; its augmentation uses the sheafification unit and the proved restriction
identity. Every definition has actual data and a proved side condition.

New module `Sheaf.AlgebraicGeometry.AlternatingCechSheafTerms` proves the degreewise
open-direct-image description. Its private helpers compare intersections to categorical
products of opens, apply the sheafification counit, and use uniqueness of right adjoints
under the over-site equivalence. Additivity gives preservation of finite products.

The item's proof proves the intersections affine from separatedness over Spec A,
enumerates the finite increasing-tuple type by its cardinality, and uses `Pi.reindex`
to produce the required family indexed by `Fin n`. It combines this with the two
remaining intermediate results below. The unit's route is preserved; no target or
existing definition changes. All five modules compile without warnings. The delivery
dry run passes compilation, axiom probes and static preflight; the second reader
will supply the second-reading section before delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_affineAlternatingCech_augmented_construction`
(node `lem-pc-s3-affine-alternating-cech-augmented-construction`). This is a decomposition:
one old hole closed and two strictly smaller holes added, not a sorry-free proof of
the complete mathematical theorem. No sorry remains in the item or the explicit
construction and term-comparison modules.

Proved in the construction module:
`AlgebraicGeometry.alternatingCechSheafPresheafD_square` and
`AlgebraicGeometry.alternatingCechSheafPresheafZero_comp`, with all private restriction
and product-projection helpers proved as well. The construction node is
`def-pc-s3-alternating-cech-sheaf-construction`.

Proved `AlgebraicGeometry.alternatingCechSheafComplex_terms`
(node `lem-pc-s3-alternating-cech-sheaf-terms`). This uses no covering, affineness or
quasi-coherence assumption.

Exactly two new sorries remain, each the whole proof of a public named theorem in its
own module with its source and full natural-language proof:

- `AlgebraicGeometry.alternatingCechSheafAugmentation_quasiIso`
  (node `lem-pc-s3-alternating-cech-sheaf-local-contraction`): local insertion contraction
  of the specified augmentation, also after additive tensor pullback along any scheme
  morphism. No affine, separated, quasi-coherent or flat assumption is made.
- `AlgebraicGeometry.alternatingCechSheafComplex_affineComparison`
  (node `lem-pc-s3-alternating-cech-sheaf-affine-comparison`): comparison of the specified
  complex's affine pushforward with the specified section model. It requires separatedness,
  affine members and quasi-coherence, but no cover or base change.

Edge cases checked against the formulas: empty tuple types give zero products; `r=0`
with a cover implies the empty scheme; tuples always have a nonempty finite domain,
so affineness of their intersections never requires an affine top open; repeated opens
and empty cover members are permitted; tensor pullback is not assumed exact or flat.
The two remaining statements are separate properties of a constructed object, not
existential repackagings of the original conclusion.

## No longer needed

None of the item's original imports or original planned dependencies is pruned:
the alternating section definitions, module pullback, tilde-Gamma adjunction and
affine model remain needed directly or transitively. All added proof imports are used.
No unused imported dependency is retained in the delivery. The new term-comparison
module needs only its construction import; redundant direct imports of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` and
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` were removed after compiling
without them, since those APIs are already available transitively.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof-dependency declarations define the section complex and tensor pullback
and provide tilde-Gamma, but do not themselves state the module-sheaf complex or its
local contraction and affine comparison. This delivery constructs the missing complex,
proves its algebraic identities and its term description, and leaves only those two
geometric comparison steps as new items.

The existing all-tuple intersection functor in
`Sheaf.AlgebraicGeometry.CechModuleSheafFunctor` had no compiled file in the shared green
snapshot during this work. The final proof uses Mathlib's presheaf pushforward and
sheafification directly, and needs no copy or adaptation of that existing module.
Its presheaf intersection objects are not alternative definitions of that module's
module-sheaf objects: the term proof relates the presheaf sheafifications to the
Mathlib over-site sheaves and then to scheme pushforward.

Mathlib searches were run through msearch: LeanFinder found only unrelated resolutions,
Loogle found extension-by-zero APIs, and grep found no matching module-sheaf alternating
construction. LeanSearch returned an internal server error, recorded as unavailable.
No interface correction, forced adaptation or statement dispute was needed.

## New nodes

`def-pc-s3-alternating-cech-sheaf-construction`: actual intersection presheaves, finite
increasing-tuple products, signed differentials, sheafified complex and restriction
augmentation. The differential-square and augmentation side conditions are proved.

`lem-pc-s3-alternating-cech-sheaf-terms`: proved comparison of its terms with products
of open direct images. It imposes no covering or affine hypotheses.

`lem-pc-s3-alternating-cech-sheaf-local-contraction`: the local homotopy argument for
the specified augmentation and arbitrary additive tensor pullback; one remaining sorry.

`lem-pc-s3-alternating-cech-sheaf-affine-comparison`: the natural tilde-Gamma comparison
for the specified complex over an affine base; one remaining sorry.

All four nodes inherit the item's chapter, unit and blueprint ancestor. The original
node's proof and proof_deps now record the actual Lean construction and reindexing route.
There are no change records because no existing interface changed.


## Second reading by H1

1. **Visible interfaces: pass.** Compared the only existing delivered module with the
   repository using `diff` and the declaration-table parser. Its declaration signature,
   docstring, visibility and three public imports are byte-for-byte unchanged; only the
   proof and three plain proof imports changed. The four additional modules are new.
   No existing definition or target statement changes, and no change record is needed.

2. **Proof and construction: pass, with the reported decomposition.** Independently
   compiled all five modules through `lcompile.py --all`, without warnings or errors.
   Read the intersection restriction maps, deletion-pair bijection, augmentation identity,
   sheafification construction and over-site/right-adjoint term comparison. There are
   exactly two `sorry` occurrences, both complete named theorem proofs as reported.
   There is no forbidden declaration or hollow definition. Scratch-copy `#print axioms`
   checks of all thirteen public construction declarations and the term theorem show
   only `propext`, `Classical.choice`, `Quot.sound`; the item's theorem also shows
   `sorryAx`, as expected from the two remaining geometric statements. The complex and
   augmentation use actual data, with no witness selected from an unproved existence.

3. **Split statements: pass.** Read both theorem signatures and their full docstring
   arguments against the specified construction. The contraction is the ordered
   insertion homotopy after restriction to a cover member; additive tensor pullback
   preserves that split homotopy locally, so no flatness assumption is needed. The
   affine comparison is a separate degreewise tilde-Gamma and differential-naturality
   claim, with no covering assumption. Neither statement repackages the existence
   theorem. Checked the empty cover/empty scheme case, one-member top cover, repeated
   or empty opens, degrees with no increasing tuples, and nonflat pullback. The terms
   theorem imposes no geometry assumptions. Independent LeanFinder, Loogle and grep
   searches, using local exactness/stalk and homotopy terms, found no direct replacement;
   these searches are recorded in the new nodes. The existing all-tuple module-sheaf
   construction and sorting comparison address different complexes and do not directly
   prove either hole. Neither geometric statement can be closed by a short existing-API
   application.

4. **Route, imports and pruning: pass.** The top proof constructs C and epsilon, combines
   the two geometric properties, proves intersection affineness, and reindexes the
   finite product; it does real work beyond applying a restated theorem. All original
   dependencies remain needed: `def-sc-alternating-cech-total-complex` by construction,
   `def-pc-module-pullback` by contraction, and the affine model and tilde-Gamma adjunction
   by affine comparison. They are replaced as direct proof-dependency edges by the new
   intermediate nodes, not pruned from the route. Added imports are used with appropriate
   public/plain visibility. No modules are pruned. The unit record
   `sk-thm-picard-f-representable.json` has pre-existing empty `realized` lists; this
   delivery changes no unit realization or chapter/unit route.

5. **DAG agreement: pass after repair.** Checked the parent proof and its dependency
   union, and each new node's statement, source, chapter, unit, blueprint ancestor,
   creation/search/Lean fields. The parent Lean signature matches its node unchanged.
   The construction node had empty `proof`, `proof_deps` and null `proof_origin` despite
   its proved identities. Filled them with the actual restriction construction,
   deletion-pair cancellation and sheafification/augmentation route, with the existing
   alternating-section dependency. Other node routes agree with their modules.

Second reading changed only DAG bookkeeping and this report: populated the construction
node's proof route and origin, added independent search records to all four new nodes,
and recorded the verified interfaces, axiom checks, decomposition and unchanged unit
realizations. No Lean code changed. One original hole is closed and two strictly smaller
holes are added; this is a decomposition, not a net reduction in holes.

Source checks: [Stacks 01FM](https://stacks.math.columbia.edu/tag/01FM) supplies the ordered
alternating-complex comparison; [Stacks 02KG](https://stacks.math.columbia.edu/tag/02KG)
and the separated-case complex calculation in
[Stacks 02KH](https://stacks.math.columbia.edu/tag/02KH) support the affine comparison
route. The stronger local split contraction is justified by the explicit insertion
argument in the split theorem's docstring, not by applying flat base change.
