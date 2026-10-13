## What changed

Repaired the false universal `schemeMV_image_resolution_comparison_intersection` as
required by return X-8738a: its short-complex morphism is now explicitly constructed
from one normalized chain map. The corrected theorem is reduced by an actual Lean
proof to source-only localization compatibility and naturality of open-image
localization. The parent `schemeMV_image_resolution_comparison` uses that same map
for both equations; its signature and visibility are unchanged.

Added explicit sectionwise image components and general localization maps in
`MayerVietorisImageChainData`, named commuting-square and source-localization
obligations in separate modules, and the concrete `schemeMVImageChainMap` and proved
`schemeMV_normalized_chain_map_exists` in `MayerVietorisImageChainMap`. The restriction
comparison abbreviates the existing `schemeMVUnderivedOpenRestriction`, rather than
constructing it twice. No data is chosen from an unproved existence theorem.

The interface repair is recorded in
`coord/changes/schemeMV_image_resolution_comparison_intersection.md`.

## Proved and sorry left

The corrected `AlgebraicGeometry.schemeMV_image_resolution_comparison_intersection`
now has no local sorry. This repairs a false holed statement; it does not prove the
old arbitrary-morphism claim. The previous local hole is removed and these two
strictly smaller holes are added:

- `AlgebraicGeometry.schemeMV_image_chain_squares`, node
  `lem-pc-mayer-vietoris-image-chain-squares`: underived naturality of the explicit
  components and the pair/difference arrows.
- `AlgebraicGeometry.schemeMV_image_localization_compatibility`, node
  `lem-pc-mayer-vietoris-image-localization-compatibility`: the source-only
  localization equation, without a target resolution or normalized chain map.

This is a statement repair and decomposition, not an axiom-free proof or a claimed
positive ledger net. No sorry remains in the item's module, and no other local
sorry is delivered. In particular `schemeMV_normalized_chain_map_exists` is proved
by Mathlib `CochainComplex.IsKInjective.Qh_map_bijective`, fullness of the homotopy
quotient, and cancellation of isomorphisms. The parent theorem already had a proof;
its necessary adaptation is not counted as another hole closed.

The data module's three auxiliary localization theorems and
`schemeMVImageComponent_factor` are proved. Each constructed map has real component
data. `schemeMVImageChainMap` uses the square theorem only for its propositional
commutativity fields. Its axioms, and those of the intersection and parent proofs,
include sorryAx from the outstanding obligations; normalized-map existence and the
data-module declarations use only propext, Classical.choice and Quot.sound.

## No longer needed

Removed the parent's proof-only import
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonFirst`.
Its old arbitrary existential morphism does not identify the intersection component.
The modules `DerivedMayerVietorisImageResolutionComparisonFirst` and
`MayerVietorisDirectImageChainSquares` have no other importers and are pruned from
this route. Their nodes `lem-pc-mayer-vietoris-image-resolution-comparison-first`
and `lem-pc-mayer-vietoris-direct-image-chain-squares` are no longer used here.

Removed redundant direct imports of `DerivedMayerVietorisCanonicalData` and
`DerivedDirectImageSplitTriangle` from the item: the signature-required chain-map
module exposes the needed data. The canonical-data node remains used for its
resolution and comparison definitions, so none of the old proof dependencies is
silently discarded. In the new chain-map module the square import must be public: Lean requires it
when exposing the definition of the constructed morphism, including its
commutativity fields. The redundant separate image-data import is removed.
The localization-compatibility import of the item is likewise proof-only.

## Where the brief, the DAG or earlier work was wrong

The old statement quantified over every short-complex morphism. For X=Y=Spec(k),
h=id, U=V=top, E=O_X in degree zero and m=0, its left side is zero whereas its right
side is an isomorphism between nonzero objects. Merely assuming the first-component
normalization would not specify the third component. The repair instead constructs
all three components from f and normalizes f, as the return requires.

The first worker's report was stale: normalized-map existence was already proved,
two smaller sorry lemmas were omitted, and the removed First import was not listed.
The new definition and normalized-map node records also had stale signatures or
incorrect proof routes. These are corrected. The parent's pre-existing node named
`schemeMV_image_resolution_comparison_components`, whereas its Lean declaration is
`schemeMV_image_resolution_comparison`; its Lean attachment is corrected without
changing its statement.

## New nodes

`def-pc-mayer-vietoris-image-chain-data`: explicit image isomorphism, component chain
maps and localization maps, with the existing restriction construction reused.

`def-pc-mayer-vietoris-image-chain-map`: the short-complex morphism with prescribed
three components; the square obligation supplies only proof fields.

`lem-pc-mayer-vietoris-normalized-chain-map`: the proved normalization existence
step using the existing Mathlib leaf `lem-weil-pbc-kinjective-hom-derived`.

`lem-pc-mayer-vietoris-image-chain-squares` and
`lem-pc-mayer-vietoris-image-localization-compatibility`: the two outstanding
compatibility statements with source references and complete proof sketches.

## Forced adaptations

`Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparison` (unclaimed)
keeps its existing signature byte for byte. Its old final application passes an
arbitrary short-complex morphism where the repaired theorem takes a chain map f
and normalization hf. The forced change replaces the old choice of m by a choice
of f and the explicit m, then applies the intersection theorem to f and hf. Removing
its now-unused proof-only First import is part of this replacement. The delivery
tool records the original compiler error against the changed dependencies below.

## Second reading by C4

1. Compared all six modules with the read-only repository using diff and the
   declaration parser. Four modules are new. Of the two existing modules, only the
   item's explicitly documented false signature changes; the parent theorem's
   signature and visibility are identical. The change record now contains the
   exact current signature, including the implicit h argument to the construction.
   `downstream.py --uses` and a source search find exactly the item and parent as
   direct users. No target statement or existing definition changes.
2. Compiled the six modules in import order with lcompile.py. No local sorry is
   inside a definition, no forbidden axiom/unsafe/opaque/extern implementation is
   introduced, and the only two delivered local sorries are exactly the named
   square and localization theorems. Printed the axioms of every public delivered
   declaration in an importing scratch module: only propext, Classical.choice,
   Quot.sound and the reported sorryAx dependencies occur. The constructed
   short-complex morphism fixes its data before supplying its propositional fields;
   the arbitrary chain representative is chosen only inside the parent's proof.
3. Read the two split statements and their docstrings against Stacks
   [08FE](https://stacks.math.columbia.edu/tag/08FE),
   [08BV](https://stacks.math.columbia.edu/tag/08BV), and
   [0D5T](https://stacks.math.columbia.edu/tag/0D5T), as well as the actual canonical
   derived-comparison definitions. The square theorem is sectionwise restriction
   naturality, valid even for empty/repeated opens and zero f; it needs no cover.
   The localization theorem has no target resolution or chain map and uses a
   general localization map on h_*I, so does not assert that h_*I is K-injective.
   For identity h and W=top it is the computation-map identity; for W empty the
   open-image terms are zero. Both are true and strictly smaller than the item.
   Ran new leanfinder, loogle and grep searches with different phrases, and searched
   lean/: found the existing underived restriction model and reused it. The
   K-injective fullness step is Mathlib, not another sorry. Leansearch returned an
   Internal Server Error, recorded as unavailable. No existing exact
   theorem for the two new compatibility obligations was found.
4. Checked the real reduction from the third component down through its
   factorization, general localization naturality, source-only compatibility and
   the normalized-map equation. It does not just apply a renamed copy of the item.
   Reviewed imports for signature versus proof use and recorded all pruning above.
   `dag/units/sk-thm-picard-semicon.json` has no realization attachment to any
   affected node; its statement and route are untouched. The underlying concrete
   Mayer–Vietoris construction is retained. The two source obligations did not
   admit a short closure from the available declarations during this reading.
5. Updated the item's proof/proof_deps and statement-change record, the parent's
   actual proof route and stale Lean attachment, and all new nodes' verbatim Lean
   signatures, proof routes, origins and recorded searches. The new chain-map
   definition has its own node, avoiding a circular dependency between the image
   data and its square theorem. All nodes keep the item's chapter and unit.

Second-reading changes: proved the repaired intersection reduction; reused the
existing restriction comparison by abbreviation; inlined the Mathlib fullness
argument to avoid duplicating the existing private surjectivity lemma; made
the localization theorem import proof-only and removed redundant imports; restored the declaration
docstring and copyright; corrected the change record, node metadata and stale
report. The extra local heartbeat budget is documented, and the compiled module
remains below the single-file time limit.

## Forced adaptations

### Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-a0jrgc9m/lean/Sheaf/AlgebraicGeometry/DerivedMayerVietorisImageResolutionComparison.lean:98:70: error: Application type mismatch: The argument
  m
has type
  (schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) (schemeMVResolution X E)).map
      ((RingedSpace.moduleDirectImage (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom h))).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
    schemeMayerVietorisComplex Y U V (schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
but is expected to have type
  ((RingedSpace.moduleDirectImage (LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom h))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
      (schemeMVResolution X E) ⟶
    schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
in the application
  schemeMV_image_resolution_comparison_intersection X Y h U V E m

(with the modules compiled into /tmp/forced-adaptation-a0jrgc9m/.lbuild) [7.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
