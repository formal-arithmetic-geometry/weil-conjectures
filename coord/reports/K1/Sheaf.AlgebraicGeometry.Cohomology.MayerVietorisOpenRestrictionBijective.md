## What changed

Replaced the sorry in `H.openRestrictionExt_bijective` by a proof using induction on
Ext degree. The generic private induction uses injective presentations, commuting Ext
maps, the right-exact Ext sequences and the additive five lemma. Private helpers prove
transport across arbitrary source and coefficient isomorphisms and establish that the
constructed base-changed inclusion is open with image equal to the inverse-image open.
All existing signatures and public imports remain unchanged. Three new modules expose
needed geometric ingredients; the inverse-image/free-sheaf ingredient is proved outright
using the sheafification, free/forgetful and inverse-image adjunctions and Coyoneda.ext.
All additional imports of the assigned module are proof-only imports. The second reader
removed three redundant proof imports already supplied by the public dependency closure.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.Modules.H.openRestrictionExt_bijective`
(node `lem-pc-open-restriction-ext-bijective`) by reduction to the two geometric holes below.
This is a decomposition, not an axiom-free proof of the geometric result: one upper hole
closed, two lower holes added (net -1).

Also proved `AlgebraicGeometry.Scheme.Modules.H.invImage_openFreeSheaf_iso`
(node `lem-pc-inverse-image-open-free-sheaf`), with no sorry. All private helpers are proved.

Every sorry left in the delivery:

- `AlgebraicGeometry.Scheme.Modules.invImage_preservesInjectiveObjects_of_openImmersion`
  (`lem-pc-open-inverse-image-injectives`, OpenImmersionInverseImageInjectives.lean).
- `AlgebraicGeometry.Scheme.Modules.H.openFreeSheaf_restrictionHom_bijective`
  (`lem-pc-open-free-restriction-hom`, OpenFreeSheafRestrictionHom.lean).

These concern injective objects and ordinary Hom sets; neither asserts the assigned Ext
conclusion. Empty and top opens, zero coefficients, all degrees and arbitrary algebra
base changes are retained. No definition selects data from an unproved existence theorem;
the source isomorphism is obtained from the proved inverse-image/free-sheaf theorem.

## No longer needed

No existing import was removed: both public imports supply names in the unchanged
signature. The old proof dependency `lem-sc-ext-exact-adjunction` and its module
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective` are not used by
this proof and are pruned from this node's proof dependencies. The replacement uses
Mathlib's covariant Ext sequences and the additive five lemma instead.

Every old direct proof dependency absent from the new direct list is accounted for:
`lem-sc-ext-exact-adjunction` is bypassed; `def-pc-flat-cohomology-comparison` and
`lem-pc-free-mayer-vietoris-short-exact` remain definition dependencies and dependencies
of the new geometric nodes; `lem-weil-pbc-zariski-extension-by-zero-adjunction` remains
a dependency of the Hom lemma, and `lem-weil-pbc-zariski-extension-by-zero-exact` is
retained through the injective-preservation node's existing Zariski restriction lemma.
These last four nodes are not claimed globally pruned. FlatCohomologyComparison and
MayerVietorisFreeComplex remain required for definitions and are not pruned.

Second-reading import pruning removed the first worker's redundant plain imports
`Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`,
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` from the assigned
module. Its public dependency closure already supplies all three APIs; the module
compiles with just the two original public imports and the three new proof imports. The restriction
square lemma is not used here, but remains in the existing restriction-map module; that
module's separate proofs use it, so it is not claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The planned adjunction declarations use different presentations of the localized site;
they do not directly supply an exact left adjoint to the concrete `invImage` functor or
its unit on the represented free sheaf. The existing `zariski_open_restriction_injectives`
theorem concerns sectionwise `U.sheafRestrict`, not the concrete inverse-image functor for
an arbitrary open immersion; the new preservation lemma isolates precisely that bridge.
The Hom-restriction lemma isolates the degree-zero supported-source argument. The existing
Ext adjunction API has the opposite edge-map orientation to the required restriction
map. Dimension shifting proves the required map directly without a derived-adjunction
coherence lemma. No mathematical statement was changed or disputed.

The blueprint ancestor tool returns None for this item because an earlier created.item
contains a module name rather than a node id. New nodes follow the existing parent's explicit ancestor
`lem-sc-flat-base-change-coherent` and its quasi-separated Mayer–Vietoris paragraph. Unit
sk-thm-picard-rr has no realized statement or step among the dependencies changed here;
its fixed route is unaffected.

The local compiled cache initially lacked MayerVietorisOpenRestrictionData,
MayerVietorisExtRestrictionMap and MayerVietorisExtFunctorSquare. Work continued on
isolated scratch checks while waiting; no repository source or compilation tool was
modified. The cache subsequently supplied the missing modules, allowing the full check.

## New nodes

`lem-pc-open-inverse-image-injectives` names the concrete inverse-image injectivity bridge
from the existing sectionwise Zariski-open theorem. Its new module contains one named
sorry with a complete proof in words, including the image-open equivalence.

`lem-pc-open-free-restriction-hom` states only the degree-zero morphism restriction from
an image-open represented free sheaf, for arbitrary coefficients. Its new module contains
one named sorry, with the extension-by-zero/unit argument in its docstring.

`lem-pc-inverse-image-open-free-sheaf` is proved from Mathlib adjunction and Yoneda APIs.
It states the free-sheaf inverse-image isomorphism for arbitrary scheme morphisms.

Searches were actually run through msearch.py (LeanFinder, Loogle, grep), and repository
sources and the cited Mathlib APIs were read. Blueprint-wide searches for restriction
injectives, extension zero, free restriction and inverse free found no exact duplicate
blueprint statement of these concrete APIs. The source Stacks Tags 03DI, 03DJ and 04J0
were read online; the literature checkout is absent on this machine. The conservative interface checker flags the new proof-scope commands. The record
`coord/changes/mayer-vietoris-restriction-private-proof-scope.md` documents the scoped
private helpers and local instance; no existing signature or visibility changed and
no downstream adaptation is required. LeanSearch was additionally attempted for each
new node and returned Internal Server Error; these searches are recorded as unavailable.

## Second reading by K1

1. Compared all four delivered modules with the repository sources. Only the assigned
   module already exists; its two public imports, namespace, variables and complete
   theorem signature are unchanged. Restored the one extra space before the final
   proof delimiter so the signature is byte for byte identical. No definition or
   target statement changed. The private-scope change record describes the added
   local commands accurately; it requires no downstream adaptation.

2. Compiled all four modules in import order with lcompile.py: no errors or warnings.
   Read every proof, including the degree-zero Ext.mk₀ argument, successor-degree
   right-exact sequence argument, source transport and pullback-pasting calculation.
   Scratch #print axioms checks cover every private helper and every public theorem:
   the private helpers and H.invImage_openFreeSheaf_iso use only propext,
   Classical.choice and Quot.sound. The target and the two expressly listed open
   geometric theorems additionally use sorryAx. Exactly those two named theorem
   bodies contain sorry; no definition contains sorry and no forbidden declaration
   or compiler escape appears. The injective presentation is supplied by Mathlib's
   proved EnoughInjectives instance, not an arbitrary witness from an open theorem;
   the free-sheaf source isomorphism comes from the proved Yoneda construction.

3. Read both open lemmas and their matching new nodes. Restriction preserves
   injectives because exact extension by zero is its left adjoint; restriction on
   Hom from L_image is bijective because L_image is extension by zero of the top
   free sheaf and its adjunction unit is invertible. These are strictly smaller
   geometric ingredients than the all-degree, two-square Ext assertion and neither
   merely renames it. Checked empty image (zero category/source), top image (an
   equivalence), zero coefficients, n=0, n=1 and arbitrary base changes. Read Stacks
   Tags 03DI, 03DJ and 04J0 independently. Repeated searches with different phrasing
   using msearch LeanFinder, Loogle and grep, plus rg over both library roots and
   Mathlib: no exact duplicate was found. Read ZariskiOpenRestrictionInjectives:
   its proven sectionwise functor differs from invImage j and still needs the
   image-open equivalence/natural-isomorphism bridge. Read sheafPullbackIso and
   the adjoint injectivity criterion; they supply tools, not an immediate closure
   of that bridge. The Hom lemma likewise still needs the canonical-unit comparison.
   Neither hole closes by a short existing-lemma application. Both have complete
   mathematical docstring proofs and nodes. The new inverse-image/free-sheaf lemma
   is proved, including naturality in the coefficient sheaf, with no geometric hole.

4. Checked the reduction top downward. The Mathlib fully faithful mapExt theorem
   cannot apply: open restriction is not full and faithful on all ambient sheaves;
   the proof only needs bijective Hom from the supported free source. Its specialized
   induction is appropriate. Removed three redundant proof imports and compiled
   again successfully. Expanded No longer needed to enumerate every old direct
   proof dependency absent from the new list, distinguishing the bypassed Ext
   adjunction from the four retained transitive/definition dependencies. Read
   sk-thm-picard-rr.realized, sk-prop-cd.realized and sk-thm-p1.realized: no realized
   statement or step is bypassed; extension and exactness remain in the geometric
   argument. No unit or chapter record changes, and no globally unreached module
   is claimed merely from removing a direct dependency.

5. Compared all node records with the declarations and arguments. The existing
   node changes only proof, proof_deps and proof_origin. Its new proof_deps equal
   the union of the steps' uses and identify the actual dimension-shifting and
   geometric route. The three new nodes have the required statement, source,
   proof, dependency, origin, search, created, blueprint, chapter, unit and Lean
   records. Each Lean statement matches its declaration and each proof plan
   matches the implementation or the explicitly remaining geometric hole.

Changes by the second reader: restored exact signature whitespace; removed three
redundant proof imports; made the pruning account complete; appended this review.
The delivery remains a decomposition: one original hole closed, two geometric
holes added (net -1), plus one new axiom-free geometric theorem. It is not reported
as an axiom-free proof of the original target.
