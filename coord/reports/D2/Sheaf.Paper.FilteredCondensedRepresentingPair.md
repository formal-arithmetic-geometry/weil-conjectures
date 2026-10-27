## What changed

Replaced the original theorem's hole with a proof that constructs the descended
bijections from the explicit extended counit and three coefficient lemmas. The
proof establishes naturality, the counit formula and identity, uniqueness, all
model/representative formulas, pair-map naturality, and the invertibility,
counit equation, uniqueness and naturality of the chosen-adjunction transpose.

Moved the original finiteSupport through Pair.IsDescent declarations verbatim into
Sheaf.Paper.FilteredCondensedRepresentingPairData, reexported publicly by the original
module. Only their blueprint tags change. This avoids a cycle between the original
theorem and its new proof-step modules. No existing mathematical signature or
non-proof body changes, and no source-library file is edited. The change record is
coord/changes/D2-filtered-condensed-data-interface.md. The five downstream modules
listed by tools/downstream.py retain all their definitions and statements without
adaptation.

The proof does not choose any object from an unproved existence theorem. Its scalar
comparison choice is over the original existential in the theorem; IsCanonical
fixes its components through a faithful inclusion. Equiv.ofBijective uses only a
proposition about a fully specified function; its inverse is uniquely determined.

## Proved and sorry left

Original holes: 1, in
WeilConjectures.FilteredCondensedRepresentingPair.filtered_condensed_representing_pair
(node lem-pur-filtered-condensed-representing-pair). Its proof is now complete from
the three named coefficient statements below. This is one decomposition, not an
unconditional proof or a positive net hole reduction.

Added holes: 3, each the entire proof of one named public theorem in its own module:

- WeilConjectures.FilteredCondensedRepresentingPair.canonical_scalar_comparisons
  (lem-pur-filtered-condensed-canonical-comparisons).
- WeilConjectures.FilteredCondensedRepresentingPair.counit_finite_formula
  (lem-pur-filtered-condensed-counit-finite-formula).
- WeilConjectures.FilteredCondensedRepresentingPair.counit_map_bijective
  (lem-pur-filtered-condensed-counit-bijective).

The data module has zero holes. Four private helpers are proved: the generic
transpose criterion and transpose square, and induced-bijection uniqueness and
pair-map naturality. Their proofs contain no holes.

## No longer needed

Removed proof-only imports from the original module:
Sheaf.NumberTheory.Padics.FiniteCoefficientFields, Mathlib.RingTheory.FiniteType,
and Mathlib.RingTheory.Spectrum.Prime.Noetherian. Their original public import
closure is preserved through the new data module. Finite-field directedness and
Noetherianity remain relevant inside the new bijectivity lemma's proof plan; these
are not claimed as globally pruned dependencies.

The original node's direct proof dependencies are replaced by the three new
coefficient lemmas. The original plan's extra object/morphism descent for uniqueness
is unnecessary: apply the induced formula at H=E and the identity, then cancel the
support image of the invertible scalar-transitivity map and use naturality. Pair-map
naturality similarly follows directly from the finite formula at the common field,
without another descent lemma. The general chosen-adjoint transpose argument uses
Mathlib isIso_of_yoneda_map_bijective and Adjunction.homEquiv naturality, so no global
finite-stage right-adjoint construction is needed. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement. The original proof plan is sound,
but its uniqueness and data-map steps can be proved without further descent.
The realization projection lemmas use one universe for coefficient fields and schemes;
applying them to finite intermediate fields requires the coefficient-universe transport
described in the new canonical-comparison lemma, rather than direct instantiation.
The original file packages its data and large theorem together; extracting its
unchanged data is necessary for independent split-off proof modules to avoid an
import cycle. No unit route is bypassed, and the original two-colimit comparison
remains the tool used by the bijectivity step.

The split statements were checked on H=E, identity scalar extension (with the actual
transitivity isomorphism), zero objects, empty schemes, unrelated finite models,
and pair maps first defined at a common finite overfield. The original projection
mates and finite-valued closure ring are retained throughout. The canonical
comparison statement concerns only scalar comparisons; the finite formula concerns
only an equality; the bijectivity statement concerns only the explicit counit map.
None restates the full descent theorem or its adjunction conclusions.

## New nodes

- def-pur-filtered-condensed-representing-pair-data: attaches the verbatim original
data declarations to their new module, without changing any construction.
- lem-pur-filtered-condensed-canonical-comparisons: existence of the normalized
restriction of the original projection mates to constructible subcategories.
- lem-pur-filtered-condensed-counit-finite-formula: the finite-representative equality
obtained by naturality and the projection composition equation.
- lem-pur-filtered-condensed-counit-bijective: bijectivity of the global explicit
counit map from finite-stage beta and the recorded two-colimit comparisons.

All new nodes inherit the parent's chapter and unit. Sources are the current
blueprint sk-thm-sp-qbar and, for the proved transpose part, the categorical
unique-adjoint proof. LeanFinder, Loogle, LeanSearch and Mathlib grep searches were
run; the generic adjunction lemmas found are used in the completed assembly.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
