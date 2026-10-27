## What changed

In `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`, replaced the proofs of
`AlgebraicGeometry.Monoscheme.existsUnique_componentGenericPoint` and
`AlgebraicGeometry.Monoscheme.existsUnique_torusEmbedding`.
All existing public signatures, definitions, attributes, public imports and docstrings
are unchanged. Added private proof imports of
`Sheaf.AlgebraicGeometry.MonoidGenericSingletonAffine` and
`Mathlib.Topology.LocallyConstant.Basic`.

The component proof establishes T0 separation from the affine cover, constructs each
point's unique maximal generalization, and proves that this function is locally constant.
It is therefore constant on each connected component. This proves existence of a point in
all its component charts. A singleton affine chart proves uniqueness.

For the torus embedding, construct one singleton component chart W. Its inclusion in every
component chart U identifies the degree homomorphisms by germ naturality. Functoriality of
monoid algebras and Spec, together with the realization colimit relation and cancellation
of the component open immersion, makes all prescribed torus maps equal. The formula for W
also proves uniqueness. This argument requires no torus action, density, or normalization
results.

The only new unfinished statement is the local assertion that the generic singleton of
one ordinary fine monoid chart is affine. It applies to an arbitrary ambient monoid
sheafed space with one chart; it does not mention a finite atlas, connected components,
realization, a field, or a torus. Its module depends only on FineFanBlowup, avoiding any
import cycle. Added its node and updated the item's proof steps and dependencies.

Validation: `lcompile.py --all` compiled both modules successfully without warnings.
The assigned module took 13.7 s and the new module 3.2 s, both within the 60 s limit.
A dependency traversal found no path from the new obligations back to the item.

## Proved and sorry left

Two of the original seven textual holes are closed:

- `AlgebraicGeometry.Monoscheme.existsUnique_componentGenericPoint`
- `AlgebraicGeometry.Monoscheme.existsUnique_torusEmbedding`

One new hole is added:

- `AlgebraicGeometry.Monoscheme.monoid_generic_singleton_affine`, node
  `lem-trf-monoid-generic-singleton-affine`.

This is a decomposition of the component theorem plus a complete proof of the embedding
from the resulting chart geometry. Net hole reduction: one. Both replaced theorems still
transitively depend on the new local obligation; no claim of an axiom-free component or
torus theorem is made.

The following five original holes remain unchanged, all attached to
`def-trf-monoscheme-toric-realization` and retaining their complete source proofs in words:

- `AlgebraicGeometry.Monoscheme.sharpening_properties`
- `AlgebraicGeometry.Monoscheme.realizationDiagram_open`
- `AlgebraicGeometry.Monoscheme.realizationDiagram_locallyDirected`
- `AlgebraicGeometry.Monoscheme.existsUnique_torusAction`
- `AlgebraicGeometry.Monoscheme.existsUnique_realizationMap`

There are six holes in the delivered modules: five original and one new. All new private
helpers are proved. The private choice of maximal generalization uses a proved unique
existence theorem; no definition chooses arbitrary data from an unproved existence claim.

## No longer needed

No existing imports are removed and no existing module or node is withdrawn. The original
node had no proof dependencies or numbered proof plan to prune. Its six statement
dependencies remain. The new topological proof needs neither a finite-point census nor
`Sheaf.AlgebraicGeometry.MonoschemeFiniteChartComponents`; the embedding proof uses neither
`existsUnique_torusAction` nor any action/coaction comparison module. These modules are not
claimed globally unnecessary: other declarations and unfinished parents may still need them.

The singleton comparison uses only restriction and the colimit cocone, so separate density,
open-immersion and group-lattice coordinate lemmas are unnecessary for the embedding's
stated existence-and-uniqueness conclusion. No such proof imports were added.

## Where the brief, the DAG or earlier work was wrong

The definition node's proof and proof_deps were empty, although the module has seven
remaining theorem obligations. The proof follows the existing theorem docstrings and ILO
VIII 3.1.4, 3.1.10(ii), and 3.2.4 directly. No statement is disputed or weakened.

Existing ordinary smallest-neighborhood and spectrum-universal-property modules import
the assigned module; importing them here would create a cycle. The new statement isolates
only the generic singleton case with its ordinary localization sheaf, at the definition
level. It is strictly smaller than the component theorem and has a genuine combining
proof in the item. Its proof does not assert sharpness or torsion-freeness, so group
monoids with torsion and the trivial monoid are included. The empty monoscheme has no
connected-component input and introduces no false nonemptiness requirement.

The current blueprint's unit route is unchanged. The item records its historical
monoidal-resolution supporting branch under lem-trf-local-term-locality; this packet
neither replaces the current contracting-correspondence route nor changes a unit record.

## New nodes

`lem-trf-monoid-generic-singleton-affine` records the generic-point localization of one
ordinary fine monoid chart. Inverting the product of all generators makes its spectrum a
singleton and its section monoid the group completion. Singleton covers are trivial, so
sheafification preserves that monoid; the sheaves agree also on the empty open, giving the
required ordinary affine chart. The new module carries this complete proof in words and
its named public theorem is exactly `:= by sorry`. Searches through LeanSearch, LeanFinder,
Loogle and Mathlib grep returned only topological generic-point or ring-spectrum results.
No blueprint node matched the search for a generic singleton. Both delivered theorems use
this one local obligation; no additional split statements or change records are added.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
