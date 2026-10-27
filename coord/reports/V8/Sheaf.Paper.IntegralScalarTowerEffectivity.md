## What changed

Replaced the hole in `WeilConjectures.integralScalarTower_effectivity` by the
normalized quotient-tower argument, using the existing simultaneous
coefficient-extension interfaces. The theorem statement and both public imports
are unchanged. The proof explicitly fixes the standard site-size and abelian
sheafification instances to prevent ambiguous coefficient universes. Competing
generic sheafification and semilinear derived-category instances are disabled
only for elaboration in this module. Five private proof imports supply finite balanced association,
strict representatives, the representative Roos comparison, the sequence Roos
model, and normalized DVR effectivity.

The proof obtains the normalized L-coefficient sequence on the given good
representative. It compares its specified total limit with the scalar extension
using the published representative comparisons. It transports the Roos triangle
through this isomorphism by explicitly precomposing its first arrow and
postcomposing its third arrow with the shifted inverse. DVR effectivity then
gives completeness. The counit isomorphism, the tower evaluation, the strict
representative comparison and the localization/evaluation factorization compose
to give the required finite reduction isomorphisms.

The node's proof, proof dependencies and proof origin now describe this Lean
argument. No definition, statement, other module, target or public interface was
changed. No change record is needed.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.integralScalarTower_effectivity`
(node `lem-sf-integral-scalar-tower-effectivity`). Added 0 holes and split off 0
statements. No `sorry` remains in the delivered module. The proof uses existing
stated dependencies; it does not claim that their transitive holes are closed.

## No longer needed

No existing import was removed, and no module is withdrawn. The original node
listed the following direct proof dependencies, which are now supplied inside
the existing coefficient-system construction theorems rather than reproved or
imported directly here:

- `lem-pur-kflat-change-of-rings` (`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`);
- `lem-pur-derived-change-of-rings`
  (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`);
- `lem-weil-proetale-countable-products-exact`
  (`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`);
- `lem-sf-strict-roos-derived-limit-comparison`
  (`Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`);
- `lem-weil-integral-scalar-extension-well-defined`
  (`Sheaf.Paper.IntegralScalarExtensionWellDefined`), used through the fixed
  `integralScalarExtensionComparison` of the retained definition module.

These nodes/modules are not asserted globally unnecessary: the construction
lemmas and scalar extension definition can still need them. Consequently the
pruned-module count is zero. The normalized-tower, effectivity and reduction
nodes remain used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The earlier search missed an
available connection between the scalar tensor models and normalized systems:
`coefficientExtensionStrictRepresentative_exists` together with
`coefficientExtensionRepresentativeRoos_exists` and
`coefficientSequence_roosModel` supplies exactly that connection. LeanFinder
returned ordinary adic completion algebra, Loogle returned no result for
`IsDerivedComplete`, and project searches located these more specific
coefficient-system declarations.

The generic construction tools come from other units:
`lem-coef-derived-system-evaluation-calculus`,
`lem-coef-semilinear-derived-sections`,
`stage3-pur-finite-extension-association`,
`stage3-pur-extension-strict-representatives`,
`stage3-pur-extension-representative-roos`, and
`lem-coef-sequence-roos-model`. They implement the original node's normalized
scalar-tower and strict Roos steps; they do not replace a unit's argument.
`dag/units/sk-def-sf-operations.json` has no realized statement or proof steps
that this proof bypasses. The node's existing use of normalized DVR effectivity
is retained. The six additional dependency nodes were checked not to reach
this item through statement or proof dependencies, and the relevant Lean import
directions were checked for cycles.

The edge cases require no special branch: identity coefficients, the zero
complex, level zero (positive exponent one), unbounded representatives, and
ramified extensions are all covered by the signatures of the construction
lemmas. No scheme finiteness, invertibility of l on Y, boundedness,
constructibility, or completeness of P was added. The auxiliary finite-field
datum D and l != D.p are exactly the original parameters.

Source verification: read Bhatt--Scholze, Section 3.5, Proposition 3.5.1,
Definition 3.5.2, and Lemmas 3.5.4--3.5.7 in the local paper, including the
regular-ideal extension to unbounded complexes. Read the current blueprint's
`sec-smooth-purity/sk-lem-sp-tower/lem-coef-normalized-dvr-effectivity.md`
and its proof. The Lean argument uses the DVR specialization and retains the
canonical quotient transitions, rather than imposing a false flatness condition
on finite quotient maps.

Consumer check: the parent `integralScalarExtension_constructible` obtains
`hc` and `he` from this unchanged signature and transports its finite-level
constructibility bounds through `he`. No consumer adaptation is necessary.

Validation: the final module compiled cleanly through `lcompile.py` in 11.2 s,
exit 0, with no errors or warnings. A source comparison confirmed that the
original theorem signature is verbatim. Only the existing node's `proof`,
`proof_deps` and `proof_origin` fields differ; all delivered Lean lines are at
most 100 characters. Each of the five proof imports supplies a declaration used
by the proof, and the two original public imports are preserved.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
