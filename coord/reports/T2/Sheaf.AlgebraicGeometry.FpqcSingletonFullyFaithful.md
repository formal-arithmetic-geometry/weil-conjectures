## What changed

Proved `CategoryTheory.fpqc_singleton_pullback_fullyFaithful` from three separately stated steps: arbitrary pullback construction, unique descent of the underlying morphism, and descent-data compatibility of the reconstructed morphism. The main proof constructs an inverse on homs using choice, proves `map_preimage` by the two jointly monic pullback projections, and proves `preimage_map` by uniqueness. Its signature is unchanged.

Moved `Over.DescentDataCategory`, `Hom`, and the category instance unchanged into `SchemeDescentDataCategory`, publicly imported by the item. This removes the import cycle that separate intermediate modules would otherwise create. The original public Mathlib and source imports are re-exported through this common module. No target definition or statement changes meaning.

## Proved and sorry left

The item's one original sorry is reduced: `CategoryTheory.fpqc_singleton_pullback_fullyFaithful` has a complete compiling proof.

Remaining named sorries (one per new module):
- `CategoryTheory.descent_pullback_construction`, node `lem-galois-descent-pullback-construction`.
- `CategoryTheory.fpqc_descent_underlying_morphism`, node `lem-galois-fpqc-descent-underlying-morphism`.
- `CategoryTheory.fpqc_descent_morphism_compatibility`, node `lem-galois-fpqc-descent-morphism-compatibility`.

The construction makes no fpqc assumption. Underlying descent asserts a unique X-morphism, with no datum compatibility conclusion; the compatibility step assumes an already reconstructed underlying map and establishes its transport equation. Each is strictly part of the argument, and the inverse laws are proved in the item.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` from the item: morphism descent now belongs below the two new morphism steps. Its node `lem-galois-fpqc-morphisms-descend` remains needed there and is not globally pruned. The direct public imports `Mathlib.AlgebraicGeometry.Sites.Fpqc` and `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum` moved to the common category module and remain publicly available. No mathematical dependency is globally pruned.

The original direct proof dependencies `def-pd-descent-datum`, `lem-galois-descent-datum-diagonal-identity`, `lem-galois-fpqc-morphisms-descend`, `def-weil-pbc-fpqc-covering`, and `lem-galois-fpqc-covering-base-change` move below the new steps. `def-pc-fibre-product` remains direct for the projection argument. No unit statement or unit step is bypassed; the unit's realized table names no node of this subargument.

## Where the brief, the DAG or earlier work was wrong

The original node omitted the construction of the functor and comparison data from its numbered proof, although its Lean conclusion requires them. Added this step from Stacks 023Y(1). The planned underlying descent and compatibility steps have suitable mathematical content but require substantial translation between canonical overlap isomorphisms and the transport encoding, so they remain separate items. No statement was found false. `r = 𝟙 X` gives the identity situation; empty schemes give the corresponding trivial objects/maps, with no hidden nonemptiness assumption. Arbitrarily chosen cartesian representatives are allowed since they are uniquely isomorphic to canonical pullbacks.

A direct construction was attempted and repeatedly compiled in scratch work: the pullback transport and functor maps can be written explicitly, but naturality requires transporting dependent over-category hom types across associativity equalities. The final deliverable exposes the complete construction statement rather than leaving a sorry in a definition.

Searches were run through `msearch.py`: LeanSearch returned Internal Server Error (recorded unavailable); Loogle did not recognize `Functor.FullyFaithful` in its index; grep found generic over-category pullback and fully-faithfulness APIs, not this scheme descent theorem. Existing `DescentPullbackCanonicalIso` supplies construction but imports the item, so importing it here would cycle.

## New nodes

`def-galois-scheme-descent-data-category` records the unchanged category definitions relocated to `SchemeDescentDataCategory`. It introduces no duplicate notion.

`lem-galois-descent-pullback-construction` records Stacks 023Y(1), in `DescentPullbackConstruction`.

`lem-galois-fpqc-descent-underlying-morphism` records the overlap restriction and unique underlying map from original steps 1–2, in `FpqcDescentUnderlyingMorphism`.

`lem-galois-fpqc-descent-morphism-compatibility` records the compatibility portion of original step 3, in `FpqcDescentMorphismCompatibility`.

Change record: `coord/changes/fpqc-descent-category-relocation.md`.

## Second reading by T2

1. **Visible declarations: passed.** Diffed every delivered module against the repository. The
   sole original theorem signature is byte for byte identical. Compared the entire relocated
   category block: structures, fields, instance body, and declaration names are identical,
   modulo the blueprint tags in docstrings. The relocation is explicitly covered by
   `coord/changes/fpqc-descent-category-relocation.md`; the original public import closure
   remains available. No target statement, hypothesis, conclusion, or definition changed.
2. **Proof and axioms: passed as a partial reduction.** Compiled all five modules using
   `lcompile.py --all`. The three reported public named theorems are the only sorries;
   no definition contains sorry and no forbidden declaration or kernel option is present.
   Scratch-copy `#print axioms` checks showed only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` for the main theorem and the three open steps. The relocated
   category instance has only the three permitted axioms. Read both inverse laws: the first
   uses both pullback projections, and the second uses uniqueness of the underlying map.
   Thus the main proof is complete relative to its three openly stated dependencies,
   rather than an unconditional sorry-free result.
3. **Split statements: passed.** Read all three signatures and docstring arguments against
   Stacks descent.tex, Lemmas pullback (023Y) and fully-faithful (0241), including the
   double-overlap argument. Construction assumes no cover; underlying descent asserts
   existence/uniqueness over X only; compatibility assumes an already reconstructed map.
   Each is a proper part of the argument, not a renamed full-faithfulness assertion.
   For r=id, the cartesian comparison maps are isomorphisms and all three claims reduce
   to transport and ordinary morphisms. Empty X forces X' and the objects over them empty;
   arbitrary test schemes and empty source objects add no nonemptiness hypothesis.
   Repeated independent LeanFinder, Loogle and grep searches with new queries, and read
   the library's DescentDatum, FpqcMorphismsDescend, DescentPullbackCanonicalIso and
   FpqcRefinementFullyFaithful. Generic Mathlib pseudofunctor descent needs a different
   encoding; downstream canonical-isomorphism statements would create import cycles.
   Found the proved object-level `exists_canonical_pullback_descent_datum` in
   `FpqcCanonicalPullbackDatum`. It does not state the functor-on-morphisms construction,
   so the split is not a duplicate. Tried extending it to that functor, but the module's
   olean is not yet in the last green build: lcompile refused its import. Per the contract,
   did not copy/restate it or build the library. Retained the original named construction
   sorry and recorded this shorter future route in its node; the attempted extension is
   saved only as scratch text.
4. **Route and pruning: passed.** The main module uses exactly the three private proof
   imports and publicly imports the relocated category required by its signature. The
   remaining imports provide the types in public statements and preserve the original
   public API. Checked all six original proof dependencies against the report: fibre
   products remain direct; the other five are explicitly reported as moving below the
   split steps. None is globally pruned. Read dag/units/sk-prop-h2.json: its realized
   statement and step lists are empty and name no node of this subargument; the
   Kummer/Brauer unit route is untouched.
5. **Nodes: passed after metadata clarification.** Read all five delivered node records.
   The main node's steps and dependency union match the construction, lift and inverse
   laws in Lean. Each open step has a separate matching module, signature, source,
   natural-language proof, creation record and node. Existing-node changes stay within
   lean/proof/proof_deps/proof_origin. Added the independent search evidence to the new
   nodes, supplied the source origin of the relocated definition node, and recorded
   the available object-level construction in the construction node's proof-origin note.

Changes made by the second reader: restored the original item's module documentation,
removed an extra blank line, added independent search records and the metadata
clarifications above, and appended this review. No Lean signature or proof term changed.

The first dry run found eight additional modules missing from the change record's
Users table. Checked their sources: none refers to DescentDataCategory; the static
Hom-name scan conservatively flags unrelated Hom names/imports. Added all eight
with their no-adaptation verdict, without changing any tool or downstream file.
This conservative scanner behavior is recorded here for the maintainer.
