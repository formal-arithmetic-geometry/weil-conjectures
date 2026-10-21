## What changed

Filled both original proofs in `Sheaf.Paper.AdicStratumCompletionUnit` without changing
any public declaration signature or definition body. The coefficient comparison is proved
by preservation of the finite-quotient limit cone, including its actual projections.
The derived-pullback computation follows from exactness and the universal left-derived
comparison. The finite-reduction normalization follows by cancellation of the two
finiteDerivedComparison isomorphisms in the specified completedFinitePull normalization.
Exact products are transported to the small sites and their slices by actual site/module
equivalences. The completeness criterion for an arbitrary supplied Koszul presentation
is proved by comparing its unit to the reflector presentation through the same Cech unit.

Added `Sheaf.Paper.AdicStratumCoverConservativity`, with a complete proof: coefficient
isomorphisms make scalar insertions invertible; covering slices detect zero underlying
sheaves; finite quasi-compact jointly surjective stratum immersions detect zero abelian
sheaves; exactness and homology extend detection to unbounded derived objects; cones give
joint reflection of isomorphisms. The proof explicitly transports arbitrary algebraic
inverse-image data and the small site models. It uses proved private helpers from the
existing adjunction and Noetherian detection modules through proof-only `import all`.

Added `Sheaf.Paper.ExactCompletedKoszulPullback`, isolating the genuinely separate,
source-based finite Koszul tower and normalized derived-limit transport calculation.
The parent uses it for immersions and slices, and proves its other assertions itself.
The original unit route is retained: coefficient comparison, finite reduction, augmented
Koszul completion transport, completeness criterion, stratum-cover detection.

## Proved and sorry left

Original holes closed (two):

- `AlgebraicGeometry.Scheme.SfbAdicRestriction.adicStratumCompletionUnit`.
- `AlgebraicGeometry.Scheme.SfbAdicRestriction.adicStratumCompletionUnit_detection`.

New theorem proved (zero holes):
`AlgebraicGeometry.Scheme.adicStratumCoverConservativity`, node
`lem-sfb-adic-stratum-cover-conservativity`.

One hole added and retained:
`CategoryTheory.ConstantCompletion.exactCompletedKoszulPullback`, node
`lem-sfb-exact-completed-koszul-pullback`. Its entire proof is `by sorry`; its docstring
states the source and complete augmented-tower/Roos argument. It assumes a left exact
left adjoint preserving products and an invertible coefficient comparison, and concludes
only transport of the actual Koszul unit. It has no scheme, stratification, covering,
Noetherian, finite-reduction, or completeness conclusion. Thus the packet is a reduction
of the two original holes to one separate transport calculation, with the geometric
conservativity calculation proved. It is not a claim that the two original declarations
are free of all transitive sorries. No sorry occurs in a definition or private helper.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.CategoryTheory.StrictRoosAdditiveComparison`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`.
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` (used by the proved new detection
  module instead).
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` (a dependency of the
  remaining strict Koszul transport calculation, not directly used by the parent).
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.

The parent no longer directly uses these old proof nodes:
`lem-pe-constant-left-module-inverse-image`, `lem-pur-roos-additive-comparison`,
`lem-pur-site-restriction-module-adjunction-exact`, and
`lem-sfb-proetale-object-inverse-image-restriction`. Its
coefficient and slice calculations are direct, and arbitrary small-model detection uses
the forgetful inverse-image comparison. The stronger proved `det-pe-products-exact`
replaces `lem-weil-proetale-countable-products-exact` here. The normalized strict Roos
and derived tensor statements remain dependencies of the new transport lemma, and
NoetherianStratumDetection remains used by the proved conservativity module. None of
those modules is claimed globally unnecessary. No module is withdrawn or deleted. Obsolete parent tool-use approvals removed are
`lem-pe-constant-left-module-inverse-image`, `lem-pur-roos-additive-comparison`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-proetale-countable-products-exact`, `lem-weil-strict-roos-comparison`, and
`lem-sfb-proetale-object-inverse-image-restriction`; surviving approvals retain their order.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or target change. The cited generic tensor and normalized Roos
lemmas do not by themselves state the comparison of the actual strict augmented Koszul
towers under the supplied algebraic inverse image; the remaining transport node makes
that missing calculation explicit. The canonical original-site detection theorem also
requires transport to the arbitrary algebraic lifts and terminal covering sieves in this
item; that bridge is now proved rather than assumed. Local reducibility attributes on
completedPull/finiteComparison and standard derived-category instances were adjusted
inside the module to allow proof elaboration; the constructions themselves are unchanged.

## New nodes

`lem-sfb-exact-completed-koszul-pullback`: the separate finite-free augmented Koszul tower
and normalized strict-limit transport calculation, sourced to Stacks 0A0E, 07A4, and
0941. Tested in words on the empty generator list, zero and unit scalars, repeated
scalars, zero rings, and arbitrary unbounded inputs. No generation hypothesis is needed.

`lem-sfb-adic-stratum-cover-conservativity`: proved joint conservativity of actual
algebraic derived inverse images on all covering slices of the finite strata. Its
coefficient and exactness assumptions are supplied by the parent proof. Empty strata,
empty schemes and empty covers are included by the sheaf and joint-surjectivity arguments.
Change record: `coord/changes/W3-adic-stratum-proof-elaboration.md` documents the local
elaboration commands conservatively flagged by preflight. Existing statements and
definition bodies are preserved; no consumer adaptation is required.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
