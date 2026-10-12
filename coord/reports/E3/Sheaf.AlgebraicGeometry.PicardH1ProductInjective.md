## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.PicardH1ProductInjective`, declaration
`AlgebraicGeometry.Scheme.picard_h1_product_injective`, with a complete Lean reduction.
The existing signature, visibility, and docstring are unchanged. The proof writes the two
slices, computes their four composites with projection pullbacks, kills the cross terms
by affine-scheme cohomology vanishing, and uses a proved private additive-group lemma
to show that the difference of classes with equal slice pairs is zero.

Added two statement modules: `Sheaf.AlgebraicGeometry.PicardH1ProductSpanning` and
`Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackFunctorial`. These isolate,
respectively, the existence part of the degree-one Kunneth argument and canonical
pullback identity/composition laws. Neither restates slice injectivity. Updated the
parent node's proof, proof dependencies and proof origin to match the reduction.

The main proof now imports the two new modules, the existing affine Cech vanishing
module, and the upstream quasi-coherence instance for the unit module. The final additive argument is the proved private helper
`injective_pair_of_spanning`, which reasons with abstract additive homomorphisms and
one spanning expression for the difference of two classes. This avoids repeatedly
elaborating concrete cohomology types in the group calculation. No attribute or
definition changes. No other existing module was adapted.

Read Stacks Tags 0BED and 01F7 directly on the Stacks website because the cited `.tex`
files are absent from this machine. The source document identifiers in the DAG retain
those of the project. The unit `sk-prop-av-cube` has empty `realized` lists; the reduction
retains its Kunneth argument through the spanning lemma.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.picard_h1_product_injective`
(node `lem-sc-picard-h1-product-injective`), one of one original holes. Its proof contains
no `sorry`. This is a decomposition, not a completed proof from sorry-free dependencies.

Added and left with exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.picard_h1_product_spanning`
  (node `lem-sc-picard-h1-product-spanning`). This asserts existence of an expression as
  projection pullbacks, without rational points, uniqueness, or slice injectivity.
- `AlgebraicGeometry.Scheme.structureSheafCohomologyPullback_functorial`
  (node `lem-sc-structure-sheaf-cohomology-pullback-functorial`). This asserts the identity
  and composition laws for arbitrary scheme maps in every nonnegative degree. It has
  no field, properness, scalar-section or rational-point hypotheses.

Holes closed: 1. Holes added: 2. Net for these declarations: -1. Existing dependencies
retain their prior proof status. No holes in definitions, no axioms, and no arbitrary
witness construction were introduced. The spanning witnesses are used only in a proof.

Edge cases checked mathematically: for `X = Y = Spec k` all degree-one groups vanish,
so spanning and the parent hold. The spanning statement also allows absent rational
points: the Kunneth decomposition does not need points. Empty schemes cannot satisfy
the bijective scalar-section hypothesis over a field. Functoriality includes degree
zero, where it is ordinary pullback on global functions, and empty schemes, where the
same functorial construction applies. The cross terms are killed only in degree one;
no erroneous general positive/zero-degree vanishing assertion is used.

Validation: the three-module set compiles in import order with `lcompile.py`. The
main module also compiles separately against the sandbox overlay. The affine-vanishing
application uses the existing sorry-free `Modules.subsingleton_H_succ_of_isAffine`,
with the unit module's quasi-coherence instance explicitly fixed to the scheme universe.
An initial dry run printed OK. A repeat under increased compilation load exceeded
60 seconds, so the final additive proof was refactored to the private abstract-group
helper, in the same module. The final dry run validates that revised proof; the
second-reading section remains reserved for the independent reader. Nothing is pushed.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
  (`pqf-lem-affine-vanishing`): the cross-term proof instead applies
  `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
  (`lem-pc-affine-vanishing`) directly to the unit module of `Spec k`, avoiding the
  derived open-module comparison for that calculation.
- `Sheaf.AlgebraicGeometry.PicardKunnethQcoh`
  (`lem-sc-picard-kunneth-qcoh`): moved below the spanning statement, where it is needed.
- `Sheaf.AlgebraicGeometry.ProperBasic` (`pqf-lem-proper-basic`): moved below the spanning
  statement, where properness supplies the Kunneth hypotheses.

The latter two nodes are retained, not globally pruned. The affine-open module is still
reachable through the existing Kunneth proof dependencies. Consequently this delivery
claims no whole-module removal from the targets' transitive closure. No other original
proof dependency is discarded; the degree-one tensor/global-sections specialization
remains in the spanning lemma's proof plan.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement was found. The original plan calls the Kunneth
specialization elementary, but its Lean declaration uses module-derived scalar
cohomology and external tensor coefficients, while the item's type uses abelian-sheaf
Ext cohomology. The required comparison with canonical structure-sheaf pullback and
unit cup products is not an immediate application of the recorded signature. The
spanning statement isolates this actual interface work rather than pretending the
isomorphism is already expressed in the parent's cohomology type.

The original pullback module exposes a real construction but no identity/composition
laws. General site pullback has a composition statement for objectwise cohomology and
inverse-image coefficients; specializing that statement and identifying the structure
maps is still necessary. The new functoriality node isolates precisely these laws.

Searches were actually run using `msearch.py`: LeanFinder returned unrelated cotangent
and group-cohomology results for the product query, and scheme pullback-functor and
structure-map results for the functoriality query. Loogle did not find the needed theorem.
Mathlib grep found no Kunneth or named structure-sheaf-cohomology pullback declaration.
Both LeanSearch requests returned Internal Server Error and are recorded as unavailable,
not as evidence of absence. Blueprint searches found no structure-sheaf cohomology or
functoriality match; the Kunneth matches are etale/derived coefficient results, not this
Zariski structure-sheaf assertion.

A dependency-graph check found four cycles already reachable from the original parent,
unchanged by this delivery: the algebraic-structure object node through its abelian and
ring component nodes (two cycles), `lem-weil-pbc-horseshoe-delta-functor` through
`lem-weil-pbc-derived-functor-long-exact`, and
`lem-weil-pbc-higher-direct-image-presheaf` through
`def-weil-pbc-flat-base-change-open-choices`. No cycle involves either new node.
These pre-existing DAG issues are reported here for the maintainer; existing node
files outside this item were not changed. The delivery tool checks actual Lean import
cycles separately and accepted the delivered imports.

## New nodes

`lem-sc-picard-h1-product-spanning`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-h1-product-spanning.json`, carries the
existence-only projection-spanning statement and its full degree-one Kunneth proof plan.
Its Lean module is `lean/Sheaf/AlgebraicGeometry/PicardH1ProductSpanning.lean`.

`lem-sc-structure-sheaf-cohomology-pullback-functorial`, in
`dag/nodes/sec-abelian-varieties/lem-sc-structure-sheaf-cohomology-pullback-functorial.json`,
carries the canonical identity/composition laws and their resolution/Ext comparison
argument. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/StructureSheafCohomologyPullbackFunctorial.lean`.

Both inherit the parent's chapter, unit and nearest blueprint ancestor. Existing
signatures and definitions are unchanged, so there are no change records or forced
adaptations.

## Second reading by E3

1. Interface check: PASS. Read the complete diff of every existing delivered module
   against the repository. The only existing module is PicardH1ProductInjective; its
   theorem signature is byte-for-byte identical, including the proofs in its let-bound
   slice definitions. Its existing docstrings, public imports and visibility are
   unchanged. There are no definition changes, target changes or forced adaptations.
   The parent JSON differs only in proof, proof_deps and proof_origin.
2. Kernel/proof check: PASS as a decomposition. Independently compiled all three
   modules in import order after the repairs (6.5, 3.3 and 28.4 seconds). Read the
   additive helper and each slice calculation. The two cross composites factor through
   Spec k in the correct contravariant order, and the vanishing theorem applies in
   degree one to the quasi-coherent unit module. In a scratch copy, #print axioms of
   the parent and both split declarations showed only propext, Classical.choice,
   Quot.sound and sorryAx; the private helper has only the three allowed axioms.
   Exactly the two reported public named theorem holes remain. No forbidden construct,
   hollow definition or choice of an arbitrary unproved data witness was introduced.
3. Split statements: PASS. Read their full statements, docstrings and nodes against
   [Stacks 0BED](https://stacks.math.columbia.edu/tag/0BED) and
   [Stacks 01F7](https://stacks.math.columbia.edu/tag/01F7). Spanning is precisely the
   existence part of the degree-one decomposition, independent of points and slices.
   Functoriality is a general identity/composition law independent of Kunneth; neither
   merely renames the parent. Checked Spec k factors, the empty-scheme exclusion from
   scalar bijectivity, lack of rational points in spanning, and degree-zero identities.
   Independent LeanFinder queries used projection-sum surjectivity and induced Ext
   inverse-image maps; Loogle searched cohomology and Sheaf.H.mapFunctor; Mathlib grep
   searched Kunneth, and rg searched the local pullback and comparison declarations.
   No duplicate or immediate replacement was found. The existing site pullback theorem
   uses objectwise cohomology and inverse-image coefficients, and the existing module
   comparison requires the compatibility work described in the new docstrings. Neither
   remaining hole can be closed by a direct application of the inspected declarations.
4. Route/pruning check: PASS after missing-plan-import repairs. The parent follows
   Kunneth spanning, functoriality, affine vanishing and an elementary additive argument.
   Public imports serve its signature and newly added imports are private proof imports.
   The original three proof dependencies are all accounted for in No longer needed:
   Kunneth and properness move below spanning; affine-open vanishing is replaced directly
   but remains transitively reachable. No whole module is claimed pruned. Read
   dag/units/sk-prop-av-cube.json: its realized fields are empty; its fixed cube route
   is unchanged, and this reduction retains the Kunneth step.
5. DAG check: PASS after search-record repair. Parent proof_deps are exactly the three
   nodes used by its reduction. Both new nodes have source, self-contained statement,
   statement/proof dependencies, union of proof-step uses, proof_origin, split status,
   created record, blueprint ancestry, chapter/unit and the verbatim normalized Lean
   signatures. Added the independently run Loogle search to each new node, giving each
   LeanFinder, Loogle and grep records in addition to the unavailable LeanSearch record.

Changes by the second reader: added private import
Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural to PicardH1ProductSpanning and private
import Sheaf.CategoryTheory.SiteCohomologyPullback to
StructureSheafCohomologyPullbackFunctorial, because their nodes cite these declarations
in their remaining proof plans. These dependencies must stay reachable for later work.
Added the Loogle records and this review; did not rewrite the correct proof. No additional
hole was closed or added: one original hole closed, two split off, net -1 for the three
reported declarations. A transient lcompile overlay FileExistsError during the shared
build refresh disappeared on a normal retry; the repaired set and axiom scratch compile
then passed. Scratch material stays outside the delivered modules.
