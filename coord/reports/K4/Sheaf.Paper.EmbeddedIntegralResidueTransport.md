## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.embeddedIntegralResidueTransport`
with a complete Lean proof from the ordinary coefficient square and the existing proved
`constantModelCtf_coefficientIso`. The original theorem signature and public imports stay
unchanged. The proof imports `EmbeddedIntegralResidueSquare` and privately imports all of
`CondensedCoefficientIsoConstructible` to reuse its proved `constructible_iso` helper.

The proof constructs inverse scalar-restriction equivalences. The quotient square gives
an isomorphism of their composites with restriction along the quotient maps. Deriving this
square and using uniqueness of left adjoints supplies the comparison of derived reductions.
The scalar square identifies the actual restrictions of K. Finite Tor amplitude implies
bounded cohomology, so the existing constructible finite-Tor transport theorem applies;
its inverse and the equivalence unit give reflection. Isomorphism invariance finishes.
The generic derived-square helper avoids elaborating the coefficient constructions inside
the adjunction calculation; the cleaned item compiles in 39.3 seconds.

The only remaining part is the ordinary scalar/quotient square, in a new module. It has no
scheme, complex, cohomology, constructibility or Tor predicates, and is strictly the first
algebraic step of the original node, rather than a renamed transport theorem. Its docstring
and node specify the construction from evaluation on the point and quotient ring maps.
Direct attempts at the sectionwise ring-object interface exposed non-definitional ring
structure identifications; no unfinished private helpers are included in the delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.embeddedIntegralResidueTransport` (1 of 1 original holes).
Added one hole:
`AlgebraicGeometry.ProEtale.embeddedIntegralResidueSquare`, node
`lem-sfb-embedded-integral-residue-square`, in
`Sheaf.Paper.EmbeddedIntegralResidueSquare`.

This is a decomposition: one upper hole closed and one strictly smaller algebraic hole
added, net zero holes. There are zero sorrys in the item module and one in the new module.
All private helpers are proved. The new theorem has exactly `:= by sorry` as its proof.
No definition, existing statement, target signature or source-library module changed.

## No longer needed

No original public imports were removed and no module is withdrawn. The proof does not
reprove the constructibility or Tor transport argument: it uses the existing proved
`lem-sfb-condensed-coefficient-iso-constructible` instead. Its definitions and dependencies
remain needed through that theorem. The DVR dependency
`lem-weil-l-adic-extension-integers-dvr` is needed only in the split ordinary coefficient
square, not directly in the derived transport proof. The node now records this dependency
through the new node. No claim is made that any source-library declaration is globally
unnecessary. The unit route and all unit realizations are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original one-step plan omitted a usable
Lean interface for the ordinary coefficient square; that step is now explicit. The rest
of the plan is implemented without additional derived or constructibility holes. No
completeness assumption or boundedness assumption on K was introduced: boundedness is
proved only for the residue object from its finite Tor amplitude.

## New nodes

`lem-sfb-embedded-integral-residue-square` records commuting isomorphisms of ordinary
constant integer coefficients and their first quotients. Evaluation of the given continuous
ring-object isomorphism at the point determines the integer-ring map. Naturality gives
the scalar square; uniqueness of maximal ideals and `Ideal.quotientEquiv` give the residue
square. Edge cases checked mathematically include an arbitrary coefficient automorphism,
the identity chart and a different uniformizer generating the same ideal. No arbitrary
witness is selected into a public definition. No change record is needed because no
existing signature or definition changes.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
