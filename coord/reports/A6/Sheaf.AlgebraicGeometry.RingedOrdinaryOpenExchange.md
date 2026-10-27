## What changed

Proved `AlgebraicGeometry.Scheme.RingedRestrictionExchange.ordinary_open_isIso`
without changing its statement. Only the item module and its own DAG proof record change.
The proof works directly with the specified ringed square: it proves bijectivity of the
unit-defined object coprojections for arbitrary coefficient presentations, computes the
normalized mate on these sections, and uses an explicit inverse of the Cartesian
section arrow. All helper declarations are private and proved. The coefficient transport is handled
by equality induction inside a generic pasting lemma. Small private proposition
wrappers keep the normalization formulas identical at specialization, avoiding
expansion of the tensor and sheafification constructions in the kernel.

The proof reuses the generic sectionwise isomorphism criterion and equality-transport
helper from the proved open-restriction module. The coefficient coprojection argument
adapts that module's proof, and the compositor unit calculation adapts the proved
private calculation in `TateInverseLimitBaseChange`, without importing that large module.

Validation: the complete module compiled through `lcompile.py` in 34.3 seconds,
including every helper and the final theorem, with zero holes. Profiling options
and temporary diagnostic modules were removed before delivery. The public theorem
statement was checked verbatim against the assigned source.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.ordinary_open_isIso`
(node `lem-sf-ringed-ordinary-open-exchange`). No holes added or split off.
No `sorry` remains in the delivered module.

## No longer needed

The planned dependency `lem-weil-pbc-proetale-ringed-open-comparison`
(`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`) is unnecessary for this
proof: the coprojection comparison is constructed directly from the two actual
adjunctions, with arbitrary specified coefficient isomorphisms.

The planned dependency `lem-weil-pbc-site-morphism-composition`
(`WeilConjectures.CategoryTheory.SiteMorphismComposition`) is unnecessary for this
proof: `exchangeModuleComposition_existsUnique` already gives the precise module
normalization needed, and equality induction handles coefficient transport.

No existing import was removed. `ProEtaleOpenRestrictionCounit` is retained as a
private proof import for its generic proved helpers. These pruning statements concern
this item's dependency edges; no global withdrawal of either module is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned transport of the entire actual-ring comparison is avoidable. A direct
section calculation gives the chosen-square, arbitrary-coefficient assertion and
identifies the specified mate by its actual units. The statement itself is unchanged;
the six-operations unit route is preserved. The proof uses no nonempty-open or
nonzero-ring assumption, so empty opens and zero coefficients require no special case.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
