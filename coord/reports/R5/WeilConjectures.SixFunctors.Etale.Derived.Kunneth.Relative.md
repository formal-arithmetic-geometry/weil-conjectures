## What changed

The existing theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
now has a complete Lean assembly following the four arrows of the current blueprint:
composition, projection for the second projection, compact-support base change, and
projection for the second structure map, with the required two tensor symmetries.

The proof also establishes the coefficient reduction in Lean: constructibility gives
finitely generated geometric homology stalks; the source coefficient hypothesis makes
their underlying types finite; faithfulness makes their endomorphism groups finite;
therefore their identities have positive finite additive order. The three comparisons
receive these annihilators explicitly, instead of implicitly treating an arbitrary
Grothendieck category as a finite module category.

Three new modules, imported privately, state the independent composition, base-change
and projection steps. No existing public declaration, signature, attribute, definition
body, public import or other theorem proof changes. No consumer adaptations or definition
change records are required. The source-interface text comparison reports no interface
change. All four delivered modules compile together; the final delivery repeats validation.

## Proved and sorry left

Original holes: one. Its declaration is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`.
The declaration now has no sorry, but its proof depends on three admitted comparisons.
This is a decomposition of one upper hole into three lower holes, not a complete proof
or positive net hole reduction. The coefficient torsion argument and the combination of
all comparisons are fully proved Lean.

New holes, each exactly the whole proof of a named public theorem:

- `AlgebraicGeometry.Etale.nonempty_iso_constructible_external_composition`, node
  `lem-sf-constructible-external-composition`.
- `AlgebraicGeometry.Etale.nonempty_iso_constructible_compact_support_base_change`, node
  `lem-sf-constructible-compact-support-base-change`.
- `AlgebraicGeometry.Etale.nonempty_iso_constructible_compact_support_projection`, node
  `lem-sf-constructible-compact-support-projection`.

No other sorry remains in the assigned module. No definition contains a sorry. The
remaining tasks are the general-coefficient extensions of composition, proper base
change with compactification comparison, and the torsion projection formula. Existing
finite-ring results do not instantiate those signatures. The statements retain the
actual derived categories, tensor and compactification functors of the source library.

## No longer needed

None of the original imports is removed: the source-library boundary preserves its
public imports verbatim, and the original private Ordinary import is used by another
already-proved theorem in this file. No source declaration or module is withdrawn.

For this source theorem's new assembly, no constructibility-preservation theorem for
`Rf_!K` is needed: the final projection statement uses the constructible source factor
M. On the arbitrary schemes of the original signature, claiming constructibility of
`Rf_!K` would introduce hypotheses absent from the source theorem.

The modern framework nodes `def-sf-datum`, `def-sf-pf`,
`thm-sf-comp-composition`, and the modern coefficient-stage Kunneth theorem do not type
this generic A-valued etale statement, so they are not added as private imports.
They remain needed by their existing consumers. No pruning of their DAG routes is claimed.

## Where the brief, the DAG or earlier work was wrong

Neither `sk-thm-sf-kunneth-relative` nor `thm-sf-kunneth-relative` currently has a primary
Lean attachment to this source module. Their modern statements concern canonical maps,
coherence and specified coefficient stages; this source theorem only asserts a Nonempty
object isomorphism for a generic coefficient category. Attaching this weaker source
statement as their realization would be incorrect. A separate exact source-statement
node records this assembly, and the modern nodes and unit records are untouched.

The existing `_of_finite` theorem already proves the finite-ring case with no holes.
The generic assembly `_of_iso` additionally assumes upper-star flat preservation,
reflection of isomorphisms and colimit/sheaf compatibility of the concrete forgetful
functor. The assigned theorem has none of those extra assumptions. They cannot be added
to its signature or silently inferred from FiniteOfIsFinitelyGenerated. Hence this
packet uses objectwise comparison statements that do not require building that
more restrictive projection-map interface.

SGA 4 XVII 5.1.8, 5.2.6 and 5.2.9 were read in the obtained re-edition PDF. They give the
composition, base-change and projection arguments for torsion ring sheaves. They do not
by themselves supply a Lean theorem for arbitrary A. The new nodes identify their
additive-coefficient extension as remaining work, rather than claiming the module-ring
specialization is an exact match. This is why all three holes are reported honestly.

Edge cases checked in the mathematical reading: the zero complex and empty source give
zero on both sides by additivity; identity factors give the identity comparison and tensor
symmetry; a proper morphism gives the ordinary proper formula; finite coefficient rings
recover the existing proved formulas. A zero stalk has a positive annihilator (one),
so the coefficient proof does not assume a nonzero object. No characteristic-invertibility
or dimension-based constructibility claim is introduced.

## New nodes

`lem-sf-constructible-external-composition` records blueprint arrow (1), with explicit
positive annihilators on both input homology stalks. It compares only the compact-support
composite at the external object, without asserting a global functor isomorphism.

`lem-sf-constructible-compact-support-base-change` records arrow (3), for arbitrary base
change of a single bounded constructible finite-Tor input with torsion homology stalks.

`lem-sf-constructible-compact-support-projection` records arrows (2) and (4). The same
separate projection formula is used twice, once with a constructible target factor and
once with a constructible source factor. The other factor may be unbounded.

`lem-sf-relative-product-finite-stalk-coefficients` records the exact existing adopted
source statement, with its complete new assembly and actual dependencies. It adds no
Lean declaration or hole and does not replace either modern blueprint theorem.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
