## What changed

Closed the sole proof hole in
`AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
in `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`.
Every existing signature, definition, visibility and public import is unchanged.
No other Lean module is delivered.

The proof uses the existing integral-model and clear-denominator theorems. It proves
an equality-detection lemma from the specified scalar-unit telescope, bounded-source
Hom continuity, and equality of representatives in a filtered colimit. A private
categorical argument then proves that the functor induced on the rationalization is
fully faithful and essentially surjective, and uses uniqueness of localization.
The cone argument takes place in the ambient rational derived category and uses only
the valid integral bounded-constructible triangulation.

Added private proof imports:

- `Sheaf.Paper.ContinuousConstructibleIntegralModel`;
- `Sheaf.Paper.ContinuousConstructibleIntegralDenominators`;
- `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport`;
- `import all Sheaf.Paper.IntegralConstructibleSequentialHom` (its already proved
  private bounded-devissage and isomorphism-transport helpers);
- `WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap`.

The DAG proof, proof dependencies and proof origin now describe this implementation.
Large coefficient pullback and derived-functor definitions are locally irreducible
while elaborating the comparison; no definition or global attribute is changed.
The complete assigned module compiled cleanly with the ordinary limits in 32.6 s
before final comment cleanup. The delivery dry run rechecks the final version.

## Proved and sorry left

Holes closed (1 of 1):
`AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
(node `thm-sfb-extend-scalars-localization`).

Holes added: 0. Holes remaining in the assigned module: 0. Split-offs: 0.
All new private helpers have complete proofs. This is a proof from existing library
statements, not a decomposition or a claim that all imported statements have already
been proved without inherited holes.

## No longer needed

No existing import is removed, and no module is withdrawn. Both original private
imports are still used by the existing bounded-constructibility preservation proof.
All added imports contribute declarations to the new proof. No globally pruned
module is claimed: the reused higher-level integral-model and denominator theorems
may still depend transitively on lower-level lattice and gluing statements.

The following old direct proof dependencies are replaced by the higher-level inputs
listed in the updated node, or by direct existing category-theory APIs. They are not
restated or proved again here:

- `def-sbc-standard-tstructure-derived-category`.
- `def-sfb-constructible-module`.
- `def-weil-closed-immersion`.
- `def-weil-open-immersion`.
- `def-weil-pbc-condensed-e-module-category`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`.
- `def-weil-pbc-proetale-site`.
- `def-weil-triangulated-category`.
- `det-prop-sfb-qlbar-colimit-x-invert-ell`.
- `lem-pc-module-filtered-colimits-tensor`.
- `lem-sf-derived-ses-triangle`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-sf-triangle-morphism-iso`.
- `lem-sfb-topological-stratified-lisse-lattices`.
- `lem-weil-pbc-condensed-constructible-serre`.
- `lem-weil-pbc-condensed-lfp-local-triviality`.
- `lem-weil-pbc-hom-colimit-extension`.
- `lem-weil-pbc-integral-constructible-serre`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `lem-weil-pbc-proper-fp-permanence`.
- `sk-def-sfb-bounded-constructible`.
- `sk-def-sfb-pullback-from-point`.
- `sk-prop-sfb-cartesian-coefficients`.

The obsolete direct `tool_uses` entries removed, preserving the order of the retained
approval, are:

- `det-prop-sfb-qlbar-colimit-x-invert-ell`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-weil-pbc-hom-colimit-extension`.
- `lem-pc-module-filtered-colimits-tensor`.
- `lem-sf-triangle-morphism-iso`.
- `lem-weil-pbc-proetale-ringed-open-closed`.
- `sk-prop-sfb-cartesian-coefficients`.
- `lem-sf-derived-ses-triangle`.
- `lem-weil-pbc-integral-constructible-serre`.
- `lem-weil-pbc-condensed-constructible-serre`.
- `lem-weil-pbc-condensed-lfp-local-triviality`.
- `lem-weil-pbc-proper-fp-permanence`.

The retained sheaf-Hom approval is used directly by the telescope argument. The
unit's integral-model / localized-Hom route is preserved; only its repeated lower
construction is replaced by already declared results.

## Where the brief, the DAG or earlier work was wrong

The original 16-step plan expanded lattice, finite-stratum gluing and Postnikov
construction that existing declared integral-model and denominator theorems already
provide. Reusing those results gives a shorter proof without changing the statement.
The old plan additionally triangulated the rational bounded subcategory. That is
unnecessary: the ambient rational derived category suffices for the cone argument,
and the full bounded inclusion reflects isomorphisms. This avoids the disputed
arbitrary-coefficient triangulation assertion entirely.

The actual remaining gap in the reusable inputs was equality detection, since a
finite-stage factorization theorem alone gives surjectivity, not injectivity. The
new private telescope argument proves that gap, including equality at a common
stage, rather than assuming it or moving it into a new hole.

No new statement excludes the empty scheme, zero objects, or exponent zero. The
categorical helpers allow these cases; the telescope starts at zero, the zero-stage
map is the identity, and scalar cancellation only uses the supplied isomorphisms.
The coefficient presentations and their map are definitionally equal after installing
the induced norm; this was checked separately before assembling the instance.
No target, definition, or existing theorem statement is changed. No forced
adaptations are needed. The static visibility check requested a record for the new
lexical commands; `coord/changes/F1-ell-adic-rationalization-proof-scope.md` documents
them and audits the sole downstream aggregate module. There is no semantic interface
change and no consumer adaptation.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
