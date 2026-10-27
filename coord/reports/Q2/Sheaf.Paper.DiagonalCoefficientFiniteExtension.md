## What changed

Proved the assembly of `diagonalCoefficient_finiteExtension` from normalized scalar
comparisons, without changing its statement or public import. The item now constructs
the integral Diagram and then the rational Diagram. For each extension it explicitly
conjugates the diagonal and three traces by the endpoint isomorphisms and the three
scalar/direct-image mates. It proves the class and trace squares by inverse cancellation
and the two integration identities by `CategoryTheory.integration_transport`.

The regular endpoint is proved using
`sfbRegularScalarExtensionMultiplication` and
`diagonal_flat_scalar_endpoint_iso`; its normalized isomorphisms are uniquely determined.
Rational line endpoints are proved using the definition of `spRationalTwist` as ordinary
scalar extension of the flat integral line and its actual extension unit. Flatness follows
from `spTwists_locallyFree`, the signed-line tensor equivalence, and internal/section-module
flatness. The supported endpoint and source squares use the existing
`diagonal_supported_scalar_source`, separately for the two projections. Adjoint
normalization proves that the resulting supported endpoint homs coincide.

The generic assembly and trace conjugation adapt the existing private proofs in
`DiagonalUniformizerScalarFrame` and `DiagonalCoefficientUniformizerReduction`.
Those existing files are untouched. The generic construction is now the proved
`diagonal_scalar_diagram_of_squares` in the new module
`Sheaf.Paper.DiagonalScalarDiagramTransport`, with private proved endpoint helpers.
It takes the needed comparisons as arguments and constructs the diagrams directly. It does
not import either uniformizer module or their quotient comparison obligations. The two
comparison modules contain only the still-missing geometric comparison steps,
not replacement diagonal existence assertions. The parent node's proof and dependencies
now describe this actual Lean argument.

Validation: profiling found a 63--66 second compile for the combined file. Keeping
`derivedScalars` locally irreducible after endpoint normalization did not bring the
file under the limit. The proved generic transport was therefore extracted into its
own module; no shared definition changed and no additional hole was introduced.
Remote single-file compilation through `lcompile.py --all` passed for all four
modules after the split (exit code 0). This includes the two comparison statements,
the proved generic transport and the item theorem. The required `deliver3.py` command
performs the final delivery preflight.
Static checks verified the unchanged public theorem signature, matching Lean signatures
in the new nodes, valid dependency references, and the 100-character Lean line limit.
No dependency cycle passes through the edited node or any new node.

## Proved and sorry left

Closed the original named hole
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_finiteExtension`
(node `lem-sfb-diagonal-finite-coefficient-extension`). There is no `sorry` in the item.

Added two named holes, each the entire proof of a public theorem in a separate module:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalFinite_integralEndpoint`
  in `Sheaf.Paper.DiagonalFiniteIntegralEndpoint`
  (node `lem-diagonal-finite-integral-endpoint`). This asserts only the normalized
  integral root-line endpoint on one scheme.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalFinite_scalarSquares`
  in `Sheaf.Paper.DiagonalFiniteScalarSquares`
  (node `lem-diagonal-finite-scalar-squares`). This asserts only the normalized
  restriction/direct-image squares and invertibility of their scalar mates on a
  shifted line. It includes the finite-free and localization cases.

This is a decomposition: one old hole closed, two new holes added, not a net proof
closure. Neither new assertion contains a diagonal class, a trace, a Diagram, or an
integration identity. Both are needed by the explicit construction and strictly
smaller than the original obligation. All private helpers are proved. No hole is
added inside a definition and no arbitrary existence witness supplies definition data.
The endpoint homs are determined by their fixed underlying maps and adjoint
normalizations; the restriction-square isomorphisms are determined by their full
universal units. Target classes and traces are actual displayed composites of these
comparisons, not arbitrary witnesses of a Diagram existence theorem.

Existing imported obligations, notably `diagonal_supported_scalar_source`, remain
separate items and are not new holes of this delivery.

## No longer needed

No original import was removed and no module is withdrawn. The delivery avoids importing
`Sheaf.Paper.DiagonalUniformizerScalarFrame` and
`Sheaf.Paper.DiagonalCoefficientUniformizerReduction`: the generic construction
is proved separately from the uniformizer comparisons, so their
uniformizer-specific obligations are not introduced into this item's import closure.
The original public import
`Sheaf.Paper.DiagonalCoefficientDiagrams` is retained. Every added proof import is used
by a declaration in its importing module.

The original direct proof dependency `lem-exc-proetale-closed-exact`
(`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`) is replaced
by `lem-diagonal-supported-scalar-source`, which supplies the actual condensed-module
supported endpoint, normalized target source and scalar equation required here. It is
not necessary to invoke the finite constant coefficient exactness assertion directly.
This is removal of a direct DAG dependency, not a claim that the source module is
unreachable or may be deleted.

The original direct dependencies `sk-prop-sfb-cartesian-coefficients`,
`sk-prop-sfb-qlbar-colimit-x`, `det-lem-bounded-continuity-direct-image`, and
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` are used within the new
comparison obligations rather than by the parent assembly. They remain necessary
mathematics: the two coefficient nodes are retained directly, and bounded continuity
and exact filtered colimits are reused through the existing
`lem-sfb-localized-direct-image-comparison` in the scalar-square node. The canonical
right-derived and integration-transport dependencies are retained through the proved
generic transport theorem. No original planned
mathematical step is bypassed. No finite-field transition or algebraic-closure
construction is imported for this proof.

## Where the brief, the DAG or earlier work was wrong

The original dependencies do not themselves state the full-unit-normalized
finite-integral Tate-line endpoint or the corresponding finite/localization scalar
restriction squares. Their results must be connected to the actual `integralLineMap`
and the actual scalar adjunction mates. The new nodes isolate precisely those bridges;
the remainder of the original plan is written in Lean.

The `blueprint_refs.py ancestor` helper returned `None` for this module-created node.
Its existing recorded ancestor is `det-prop-diagonal-tower-coefficients`; the new nodes
preserve that ancestor and extend its existing `via` chain. Blueprint searches for
"finite integral scalar" and "scalar direct image" found zero matching blueprint
nodes; local searches found the reusable interfaces noted above.

Edge cases checked in the comparison proof sketches: the bottom finite field,
ramified extensions, the empty scheme and zero root line. Rationalization uses the
single line shifted by two, so its telescope has common lower bound -2; it does not
need a bound on an arbitrary unbounded input or a global commutation theorem on every
complex. The scalar-square assertion requires qcqs, and the actual three projections
meet that hypothesis. The original target assumptions are unchanged.

## New nodes

`lem-diagonal-finite-integral-endpoint`, module
`Sheaf.Paper.DiagonalFiniteIntegralEndpoint`, is the finite-free root-limit part of
paragraph (1). It asserts the normalized integral line comparison alone and records
its finite-level scalar-unit and inverse-limit proof.

`lem-diagonal-finite-scalar-squares`, module
`Sheaf.Paper.DiagonalFiniteScalarSquares`, is the finite-free direct-image step of
paragraph (1) and the rationalization step of paragraph (2). It records the full
universal-unit restriction square and its scalar mate, with only the shifted-line
invertibility needed by trace conjugation. Its source argument uses finite
biproducts and the existing `localizedDirectImageComparison_isIso` on the shifted
single line, respectively. The latter already proves the rational mate is invertible;
the remaining bridge identifies the full-unit-normalized square with that canonical
comparison.

`lem-diagonal-scalar-diagram-transport`, module
`Sheaf.Paper.DiagonalScalarDiagramTransport`, is proved without any local hole. It
contains the generic regular-endpoint, supported-source, class/trace-conjugation and
integration assembly. This is a code split after profiling the combined file, not an
additional split-off proof obligation.

No existing interface changed and no change record is required.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
