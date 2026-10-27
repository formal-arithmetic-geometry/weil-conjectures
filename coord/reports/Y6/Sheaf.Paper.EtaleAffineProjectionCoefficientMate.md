## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etaleAffineProjectionCoefficientMate`
by an explicit counit and adjunction-transpose proof, keeping every existing declaration
signature and definition unchanged. Added proved private helpers for the purity counit,
uniqueness of normalized P1 data, and abstract cancellation of normalized mates and
coefficient/counit squares. A private elaborator routine builds explicit heterogeneous
congruence proofs for the different synthesized site-instance proofs in the realization
record and its consumers. It uses reflexivity and proof irrelevance, and every resulting
proof term is checked by the kernel. The site assembly is proved for arbitrary finite
coefficient rings before instantiating the p-adic quotient stages, keeping the large
coefficient constructions out of the generic cancellation calculation. Scoped options
disable replay by the unused-tactic linter for the two concrete calculations; kernel
checking and the compile limit are unchanged. The ordinary clause
uses `affine_counit_scalar`, compact scalar coherence, and naturality. The site clause is a real Hom-bijection
calculation from the recorded realization counits and the intrinsic site/coefficient
pasting square. The latter is isolated in `Sheaf.Paper.ReductionSiteCoefficientPasting`.

## Proved and sorry left

The original module had one sorry, in
`AlgebraicGeometry.Etale.etaleAffineProjectionCoefficientMate`. Its ordinary coefficient
clause is proved, including invertibility and the exact reassociation equation.
The assigned module contains zero sorrys. The full theorem is reduced to the
site/coefficient square below. This is a decomposition, not a net hole closure:
one original hole closed and one independent lower hole added (net zero).

The only retained sorry is
`AlgebraicGeometry.ProEtale.reductionSiteCoefficientPasting`, node
`lem-sp-reduction-site-coefficient-pasting`. It states a coefficient/site square for
arbitrary fixed proper/open factorizations and a map between two bounded-below
endpoints. It contains neither purity, exceptional right adjoints, nor a mate assertion.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.NormalizedMateScalarSiteTransport` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
The componentwise Hom-bijection proof does not require node
`lem-pur-normalized-mate-scalar-site-transport` or `sbc-lem-affine-space-smooth`.
The site formula uses the already supplied `ReductionExceptionalRealization` counit
fields, rather than invoking `det-sp-et-proet-adjunction-transfer` to construct them.
The adjunction-transfer module is still needed for the ordinary finite-Tor predicate.
The coefficient-compatibility module remains needed for its proved identification of
the etale coefficient map with the actual compact scalar map. Its principal theorem
has a smaller finite-Tor constructible domain than the new site square; the latter's
proof plan uses the endpoint comparison-counit equations and normalized presentations.
No module is withdrawn and no source-library public declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The planned generic site-transport theorem requires whole-category equivalences and
natural isomorphisms, whereas the retained realization record provides ordinary
origins and bounded-below comparisons only at the needed objects. A componentwise
argument works with exactly those hypotheses. The specified intrinsic realization
boundaries and the fixed-module boundaries in the coefficient-compatibility theorem
are separate constructions; their identification is not definitional. The new square
records precisely this missing pasting step. It avoids asserting that arbitrary
coefficient extension preserves all bounded-below objects. Zero rank, zero objects,
empty bases, the identity coefficient map and non-flat coefficient maps introduce no
cancellation of a non-isomorphism or extra assumptions.

## New nodes

`lem-sp-reduction-site-coefficient-pasting` is the independent intrinsic-coordinate
coefficient/site square in `lean/Sheaf/Paper/ReductionSiteCoefficientPasting.lean`.
Its source is the blueprint Charts argument and Stacks Tags 0GL6, 099R and 00YV;
its docstring gives the section normalization, proper/open pasting and naturality
argument. It has three kinds of Mathlib search and its own Lean attachment.
A duplicate search across the live Sheaf tree found no theorem in these intrinsic
coordinates. `etaleProEtaleCoefficientCompatibility` instead uses fixed-module
presentation comparisons and assumes a finite-Tor constructible ordinary input.
The new mixed-endpoint square needs normalization of those presentations, and does
not assume the scalar-extended intermediate object is bounded below.
Blueprint-wide search for "coefficient site square" returned no matching node.
Both delivery modules compiled in import order; the standalone full proof also compiled
without the broad Mathlib.Tactic import. No definition or statement change record is required.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
