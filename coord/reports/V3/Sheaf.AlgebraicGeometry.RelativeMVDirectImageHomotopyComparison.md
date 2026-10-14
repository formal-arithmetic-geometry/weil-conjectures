## What changed

Replaced the sorry in
`AlgebraicGeometry.relativeMV_direct_image_homotopy_comparison` by a complete
proof from short exact resolved rows. The existing theorem signature, universes,
visibility and docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows`, with the one residual
construction theorem `AlgebraicGeometry.relativeMV_direct_image_rows`. It constructs
actual short exact rows and their quotient-component comparison; it does not assert
any cone comparison, homotopy-cone map or tensor-pullback model.

The parent proof constructs the specified homotopy with `Homotopy.ofEq`, obtains
both cone/quotient isomorphisms from `quasiIso_descShortComplex`, and proves the
third identity using the additive cone comparison, `map_descShortComplex`,
localization naturality, and left/right naturality of the adjunction Hom equivalence.
Two proved private helpers keep these calculations generic and avoid unfolding
the scheme adjunction during rewriting. No heartbeat or timeout limit is changed.
Updated the parent node's proof route and added the residual node.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.relativeMV_direct_image_homotopy_comparison`
(node `lem-pc-relative-mv-direct-image-homotopy-comparison`).

Added exactly one hole:
`AlgebraicGeometry.relativeMV_direct_image_rows`
(node `lem-pc-relative-mv-direct-image-rows`). Its entire proof is `by sorry`;
its docstring gives the source and the resolved-row construction in words.

This is a decomposition: one upper hole closed and one lower hole added, net zero.
The cone-to-quotient and adjunction-naturality parts are proved; the simultaneous
resolved-row construction, homotopy-pullback replacement, and identification
of its quotient component with the pinned overlap arrow remain in the new theorem.
The private helpers `cone_quotient_naturality` and `cone_mate_quotient` contain no sorry.
There are no remaining sorries in the assigned module and no holes in definitions.
Both modules compile locally without warnings under the standard per-file limit.

The residual statement was checked on empty opens (zero local and overlap terms),
repeated opens (split restriction rows), zero coefficients (zero rows), and zero
phi (zero comparison). It keeps the source complexes on S and target complexes
on S', and never assumes that underived direct image preserves quasi-isomorphisms.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`

They remain proof dependencies of the residual row-construction module. Therefore
no module or node is claimed pruned from the target import closure. The original parent proof-dependency nodes
`prop-pur-kinjective-resolutions-exist`,
`lem-pc-kinjective-mayer-vietoris-presentation`, and
`lem-pc-mayer-vietoris-underived-open-counit-square` are no longer used directly
by the parent proof; they remain used by the new row-construction theorem.
The second reading also removed the new row module's unused private import
`Mathlib.CategoryTheory.Localization.CalculusOfFractions` and its planned
`lem-pc-right-fraction-representation` and
`lem-pc-right-fraction-common-refinement` dependencies. The explicit row homotopy
pullback replaces that proposed route. No global pruning is claimed.
All three original public imports remain public and unchanged. The cone/short-exact APIs already come through the unchanged public import
`MayerVietorisImageChainData` via `DerivedDirectImageSplitTriangle`; the second
reading removed the redundant private
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact` import from the parent and
the redundant public `Mathlib.Algebra.Homology.ShortComplex.ShortExact` import
from the new row module.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide absolute K-injective rows and an underived open
counit equation, but none states the simultaneous relative row comparison into
underived g_* of the target row with its retained quotient component. The new
node isolates this missing construction. `RelativeMVCoverRows` cannot supply it:
it is downstream of this item through `RelativeMVCoverChainSquare`, and importing
it would cycle. The proof does not use a generic completion of a triangle square.

LeanSearch was unavailable (Internal Server Error). LeanFinder, Loogle and source
searches were completed and recorded. The second reading found that the residual construction needed a more precise
unbounded-computation argument. Its new docstring now uses the existing
`RingedSpace.isIso_moduleDirectImage_unit_on_kInjective` and an explicit
homotopy pullback of the actual row roof. Termwise flasqueness is used only for
sectionwise exactness. No statement is marked disputed, no existing interface
is changed, and no consumer adaptation is required. The unit's route is
unchanged; its recorded `realized` lists are empty and this is a split below that level.

## New nodes

`lem-pc-relative-mv-direct-image-rows`, at
`dag/nodes/sec-picard-framework/lem-pc-relative-mv-direct-image-rows.json`, states the
resolved exact-row construction before cone passage. Its module is
`lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRows.lean`. It inherits the
parent chapter, unit and blueprint ancestry and cites the existing resolution,
absolute-row, counit, localization and unbounded direct-image acyclicity tools. No change record is
needed: the new public declaration is in its own module, imported privately by
the assigned module, and all existing interfaces remain identical.

## Second reading by V3

1. **Interface comparison: pass.** Compared every delivered source against the
   repository. The original theorem's entire signature is byte for byte identical,
   with the same universes, hypotheses, existential witnesses and three equations.
   Its existing docstring and three public imports are unchanged. The second module
   is new; there are no changes to any definition or existing public declaration,
   no change records, and no forced adaptations. The existing DAG node changes only
   `proof`, `proof_deps` and `proof_origin`.

2. **Proof and trust audit: pass as a decomposition.** Read both private generic
   helpers and the parent proof. `map_descShortComplex` and the additive cone
   comparison give the actual quotient identity. Localization naturality and both
   adjunction naturality identities transport it to the stated mate identity.
   Short exactness supplies the two cone-to-quotient quasi-isomorphisms; applying
   Lg* to the source comparison gives exactly the requested witness. No target
   quasi-isomorphism is sent through underived G. Both modules compile without
   warnings. Scratch copies with `#print axioms` check both private helpers, the
   parent and the residual theorem; the helpers use only standard axioms, while
   the parent and residual may additionally use `sorryAx`. There is exactly one
   delivered `sorry`, the entire proof of `relativeMV_direct_image_rows`, and no
   definition is added or filled by an arbitrary existence witness.

3. **Residual statement and sources: pass after documentation repair.** Read
   [08BV](https://stacks.math.columbia.edu/tag/08BV),
   [08HZ](https://stacks.math.columbia.edu/tag/08HZ),
   [08FE](https://stacks.math.columbia.edu/tag/08FE),
   [08HY](https://stacks.math.columbia.edu/tag/08HY), and
   [08BS](https://stacks.math.columbia.edu/tag/08BS), together with the existing
   direct-image acyclicity declaration. The residual states short exact rows and
   their component maps; the parent separately proves the cone identifications
   and cone-map mate equation. Thus it is a construction step, with no restatement
   of the parent's cone conclusion. It remains substantial and cannot be closed
   in a few minutes from the available declarations. Tested the empty-open case
   (the other open is full), repeated opens (both must be full), both coefficients
   zero, and phi zero. The construction uses complexes on S and S' separately;
   it requires neither flatness nor preservation of quasi-isomorphisms by G.
   Independent LeanFinder search for morphisms of exact cochain rows returned
   generic cone and homology-sequence APIs. Loogle search with `descShortComplex`
   and `mapHomologicalComplex` returned the existing additive comparison, already
   used. Source searches in both library roots and Mathlib found the acyclicity
   theorem used in the repair, and no duplicate relative construction. In
   particular, `RelativeMVCoverRows` imports `RelativeMVCoverChainSquare`, which
   imports this item, so it cannot shorten this proof without a cycle.

4. **Route and pruning: pass after repair.** The parent takes the direct Mathlib
   cone/quotient route. The residual docstring formerly invoked common denominators
   on an unspecified finite diagram. Replaced that with a concrete row homotopy
   pullback: for a strict roof S -> R <- T with the second map a vertexwise
   quasi-isomorphism, use the differential
   `(s,t,z) |-> (ds,dt,-dz+u(s)-v(t))` on
   `S_i^n ⊕ T_i^n ⊕ R_i^(n-1)`. Projection to S is a quasi-isomorphism because its
   kernel is the shifted acyclic cone of v, and projection to T is a strict row
   map retaining the quotient component. The new docstring invokes unbounded
   direct-image acyclicity explicitly before forming this roof. Removed the
   obsolete fractions import and dependencies. `No longer needed` now names all
   three original parent dependencies transferred to the residual. None leaves
   the target import closure. The unit `sk-thm-picard-coherence` has empty
   `realized.statement` and `realized.steps[0]`; these records and the unit's route
   are unchanged.

5. **DAG agreement: pass after repair.** Checked the proof-step dependency unions,
   both verbatim Lean statements, and the new node's source, ancestry, chapter,
   unit, creation and search records. The parent names the residual construction,
   the Mathlib cone quasi-isomorphism and the mate calculation it actually uses.
   The residual node now records the explicit homotopy-pullback construction and
   the existing direct-image acyclicity node, with obsolete fraction dependencies
   removed. It stays a single named open construction theorem. No new hole was
   added by this second reading.

Changes made by this reader: repaired the residual proof docstring and DAG route,
added its private acyclicity import, removed its private fractions import and two
obsolete dependencies, removed two redundant Mathlib imports, completed the
pruning report, and wrote this review.
The parent Lean proof was correct and was left unchanged. Accounting remains
one original hole closed and one lower construction hole added, net zero.
