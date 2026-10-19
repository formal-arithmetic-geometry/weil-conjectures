## What changed

Proved `AlgebraicGeometry.ProEtale.siteClosedCounitTransport` with its existing signature,
visibility, hypotheses and conclusion unchanged. No definitions changed.

A proved private helper identifies `fixedCompactSupportComparisonIso` with
`compactSupportSiteComparison`: restrict the exact composition/natural-isomorphism factors
to D+, then use naturality of the right-derived inclusion comparison on their composite. The main
proof uses the specified `homEquiv_normalized`, unit naturality and ordinary-adjunction
naturality to obtain the general adjunct formula. The comparison unit makes alpha an
isomorphism and supplies the etale-origin witness. Source naturality and injectivity,
specialized to the ordinary counit, prove the counit equation.

Retained both public imports and added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for the derived
natural-isomorphism inverse law. Removed the six unused proof imports listed below.
Updated the existing node's proof, proof dependencies and proof origin to match the Lean,
and withdrew its obsolete `lem-exc-closed-ambient` tool-use entry.

The complete module compiles through lcompile.py (20.2 seconds on the current check).
The static declaration comparison confirms no changed public signature, public import
or interface command. The consumer scan reports 196 transitive importers, with no
downstream mention of the theorem name and no required adaptation. The direct importer
is `Sheaf.SixFunctors.FiniteDualizing`. No heartbeat or wall-clock limit was raised. The comparison calculation uses one naturality rewrite on the composite
of the three open-extension factors. No reducibility or elaboration options remain.
The costly intermediate `change` was eliminated in favor of direct naturality rewriting.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.siteClosedCounitTransport`
(node `lem-coef-site-closed-counit-transport`).

Holes closed: 1. Holes added: 0. Holes remaining in this module: 0. No split-off statements.
The private helper is fully proved. Dependencies retain their existing proofs and holes;
none was changed or copied into this delivery.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`: the ambient comparison-unit
  invertibility theorem is available directly through the retained source interfaces.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`: its abbreviation is unused;
  the proof uses the existing exact-derived comparison and etale-origin API.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`: the ordinary adjunction is an explicit
  input, so its existence theorem (`lem-exc-closed-ambient`) is not a proof dependency.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`: its canonical mate definitions
  are still used by the comparison calculation, and are publicly supplied by the retained
  comparison interfaces; this additional direct import is redundant. The node stays needed.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`: the supplied C already includes
  its normalized Hom equivalence and naturality, so no construction of a new one is used.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the global coefficient
  system (`def-weil-exceptional-inverse-image`) is unused. The right functor here is the
  explicit composite with the supplied G, and no constructibility is needed.

These are local dependency removals; this report makes no claim that other target branches
stop using the modules. The statement dependencies are unchanged, including the ordinary
closed-adjoint and exceptional-inverse-image notions used in the original node's statement.
The unit record has no realized steps assigned to this node; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier Lean placeholder did not supply an equality between the fixed compact-support
comparison used by C and the canonical compact-support site comparison used in delta.
Their constructions agree, but through naturality of the right-derived inclusion
compatibility, rather than by definitional equality alone. The private helper supplies
this calculation for every compactification.

The DAG's original proof invoked existence of an ordinary closed adjoint and the global
exceptional coefficient system although G, adj and C are already supplied as inputs. The
proof now explicitly uses those inputs and omits the unused existence constructions.
No mathematical statement was corrected or weakened. Empty schemes and zero objects
require no exceptions: the proof uses only naturality, isomorphism laws and injectivity of
Hom equivalences. The given hIH supplies exactly the bounded-below object needed for the
counit specialization.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
