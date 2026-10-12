## What changed

Proved `AlgebraicGeometry.fpqcDescentEffective_of_affine` without changing its signature.
The proof uses the existing finite affine refinement, constructs its chosen pullback datum,
applies `haffine` using `hbase`, reflects effectivity through the refinement, and invokes
affine-base gluing. The statement's finite-coproduct hypothesis is retained but unnecessary
for this singleton route.

Added three separate modules: `FpqcCanonicalPullbackDatum` (fully proved),
`FpqcRefinementReflectsEffectivity`, and `FpqcEffectivityAffineBaseGluing`.
Each has a matching DAG node. Updated the original node's proof route.
All four modules compile locally without warnings. Searches found property-descent lemmas
but no direct object-effectivity reduction. The Stacks sources were read at Tags 02W3 and
023Y online because the local literature checkout is absent.

## Proved and sorry left

Proved `AlgebraicGeometry.fpqcDescentEffective_of_affine` (the item's sole original sorry).
Also proved `AlgebraicGeometry.exists_canonical_pullback_descent_datum`, including transport
naturality, identity, cocycle, and the projection's IsBaseChange equation, directly by the
pullback universal property and the supplied datum's laws.

Exactly two new sorries remain:

- `AlgebraicGeometry.fpqc_refinement_reflects_effectivity`, node
  `lem-galois-fpqc-refinement-reflects-effectivity`.
- `AlgebraicGeometry.fpqc_effectivity_of_affine_bases`, node
  `lem-galois-fpqc-effectivity-affine-base-gluing`.

Each is a named public theorem in its own module, with an exact `by sorry` proof and a
complete sourced proof in words. The first needs an effective pulled-back datum; the
second assumes effectiveness for arbitrary sources over affine bases. Neither repeats
the original affine-source criterion. The delivered theorem is a reduction to these
statements, not yet an axiom-free proof of effective descent.

## No longer needed

Removed direct imports `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` and
`Sheaf.AlgebraicGeometry.FpqcRefinementFullyFaithful` from the item; they are now imported
by the respective gluing and reflection modules, so neither node nor module is globally
pruned. The following old direct `proof_deps` are no longer direct dependencies of the item:
`lem-galois-fpqc-covering-base-change`, `lem-galois-fpqc-refinement-fully-faithful`,
`lem-galois-fpqc-morphisms-descend`, `lem-weil-pbc-relative-glueing-affine-opens`, and
`lem-weil-pbc-scheme-morphism-gluing`. They are retained under the two new supporting
nodes: base change, morphism descent and gluing under affine-base gluing, and refinement
full faithfulness under reflection. None is globally pruned. Fibre products, descent data
and singleton affine refinement remain direct dependencies.

Second reading removed the unused public import `Mathlib.AlgebraicGeometry.Sites.Fpqc`
from `FpqcCanonicalPullbackDatum`; its statement and proof need no fpqc hypothesis.

The canonical pullback construction needs no `DescentPullbackCanonicalIso` import or node:
it is proved directly from the pullback universal property and the existing descent datum.
No unit's statement or proof step is bypassed. The unit record `sk-prop-h2` has no realized
nodes constraining this auxiliary reduction; the original four mathematical phases remain.

## Where the brief, the DAG or earlier work was wrong

The original dependency statements provide an existential pullback object; this is not
enough to apply `hbase` to an arbitrary property P, which is not assumed invariant under
isomorphisms. The new canonical-pullback theorem uses exactly the chosen second projection
required by `hbase`, avoiding any extra invariance hypothesis. No existing statement or
definition was changed.

Edge cases checked in the statement design: identity refinements, empty schemes and
empty finite affine refinements are allowed; reflection requires both composite singleton
covers to be fpqc and does not assert that the refinement morphism itself is fpqc.
The gluing hypothesis allows non-affine sources over affine bases.

## New nodes

`lem-galois-fpqc-canonical-pullback-datum` records the fully proved chosen pullback
construction in `lean/Sheaf/AlgebraicGeometry/FpqcCanonicalPullbackDatum.lean`.

`lem-galois-fpqc-refinement-reflects-effectivity` records Stacks 02W3's reflection of an
effective object through full faithfulness in
`lean/Sheaf/AlgebraicGeometry/FpqcRefinementReflectsEffectivity.lean`.

`lem-galois-fpqc-effectivity-affine-base-gluing` records the general-base part of Stacks
02W3 in `lean/Sheaf/AlgebraicGeometry/FpqcEffectivityAffineBaseGluing.lean`.
No change records are needed: existing statements and definitions are unchanged.


## Second reading by S2

1. Compared the entire original module with the repository using `diff`, and checked the
   theorem signature byte for byte up to `:=`. PASS: the original signature and docstring
   are identical; only private proof imports and the proof body changed. The sole existing
   node changes only `proof`, `proof_deps` and `proof_origin`. No definition or target was
   changed, and no change record is needed.
2. Compiled all four delivered modules in dependency order without errors or warnings.
   PASS: the original theorem has no textual sorry, and the only two delivered sorries
   are the public named reflection and affine-base-gluing theorems listed above. No axiom,
   unsafe, opaque, implemented_by or extern declarations occur. A scratch `#print axioms`
   check gave `[propext, Classical.choice, Quot.sound]` for the canonical-pullback theorem;
   each open auxiliary theorem and the original reduction additionally uses `sorryAx`.
   Thus the original sorry is replaced by a checked reduction, not a completed axiom-free
   effective-descent theorem. The existing singleton-refinement theorem also remains open.
3. Read the two new sorry signatures, their full docstrings and nodes, and checked them
   against [Stacks 02W3](https://stacks.math.columbia.edu/tag/02W3) and
   [02W0](https://stacks.math.columbia.edu/tag/02W0). PASS: reflection requires two fpqc
   singleton covers, a genuine pullback square and transport compatibility, not that the
   refinement itself is fpqc. Fullness descends both directions of the identification;
   faithfulness proves inverseness. Gluing assumes effectiveness for arbitrary sources
   over affine bases and concludes it for arbitrary bases, preserving the property by
   the exact chosen pullback. These are separate parts of the argument, not restatements
   of the affine-source hypothesis. Identity refinements, empty bases, and the finite
   refinement with zero components introduce no exceptions. No intersection of affine
   opens is assumed affine: glue using all smaller affine opens covering the overlap.
   Read [023Y](https://stacks.math.columbia.edu/tag/023Y) for the canonical construction.
   Independent searches used `leanfinder` for locality/reflection of effective objects,
   `loogle` for pullback pasting, and `grep` for effective descent/refinement, plus `rg`
   across Sheaf and upstream descent modules. Hits concerned property descent, pullback
   pasting or finite/quasi-projective special cases; none replaces these statements.
   `descent_pullback_canonical_iso` specifies existential pullback objects and cannot
   ensure P for their projections without an unprovided isomorphism-invariance condition.
   Neither remaining step has a short direct closure from the available declarations.
4. PASS: the proof starts at the original theorem, reduces to affine bases, uses the
   existing finite affine refinement, constructs the exact chosen pullback, applies
   `hbase` and `haffine`, and reflects effectivity. `hcoprod` remains unchanged and is
   unnecessary for singleton covers. The new canonical module's fpqc import was unused
   and removed; the other public imports supply the signatures. The admitted modules'
   private imports retain their planned proof tools. Expanded `No longer needed` to name
   every removed old direct proof dependency and distinguish relocation from global
   pruning. No module is globally pruned. Read `dag/units/sk-prop-h2.json`: its realized
   statement and step lists are empty, and no unit route is bypassed.
5. PASS after repair: all three new nodes have the required creation, source, search,
   blueprint, chapter, unit and Lean records; their statements match their declarations.
   Their proof dependencies equal the union of their steps' uses. The item's six direct
   dependencies agree with the actual reduction; the old tools are assigned to the
   corresponding supporting nodes. Changed the item's proof step from `elementary: true`
   to `false`, since it uses substantive refinement, reflection and gluing results.

Changes in this second reading: removed the unused fpqc import from the proved canonical
pullback module; corrected the item's elementary flag; completed the direct-dependency
pruning inventory. No theorem statement or proof argument was rewritten.
