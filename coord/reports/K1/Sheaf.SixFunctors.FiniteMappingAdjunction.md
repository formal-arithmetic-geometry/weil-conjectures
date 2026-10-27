## What changed

The unchanged statement of `WeilConjectures.finiteMappingAdjunction` now has a complete
Lean assembly proof. It obtains a natural transformation with its etale comparison
square, obtains componentwise invertibility separately, constructs `NatIso.ofComponents`
using the transformation's naturality, and applies a separate normalized transpose theorem.
The hom components of that isomorphism are definitionally the original transformation.

The nineteen existing helper definitions moved verbatim (names, signatures and bodies)
to `Sheaf.SixFunctors.FiniteMappingAdjunctionData`, publicly re-exported by the original
module. The original public imports remain. This avoids a cycle between the final theorem
and the three new modules whose statements require the arrow lists. The data module's
blueprint tags now point at its dedicated definition node. A declaration-local unused-variable
linter suppression preserves the original `hJ` binder while removing its warning.

The initial five-module compile passed, with only that subsequently suppressed warning.
The final versions compiled cleanly with no warnings. The unchanged direct consumers
CoefTowerNaturalCurrying, FiniteAdjunctionTransition and IntegralDualizing also compiled
cleanly against the final files; their temporary copies were removed from the packet.
The delivery preflight checks the declarations' axioms and direct hole inventory.
No target or source-library declaration has changed.

## Proved and sorry left

This is a decomposition, not a net mathematical proof or a claim of sorry-free closure.
Original holes: 1. Original holes replaced by complete combining proofs: 1,
`WeilConjectures.finiteMappingAdjunction` (lem-coef-finite-mapping-adjunction).
The item now has 0 direct holes. The data module has 0 holes.

Three new public theorem holes remain, each as its entire proof and in its own module:

- `WeilConjectures.finiteMappingEtaleDescent`
  (lem-sf-finite-mapping-etale-descent): descent and etale agreement only; no isomorphism
  or transpose equation is asserted.
- `WeilConjectures.finiteMappingEtaleDescent_isIso`
  (lem-sf-finite-mapping-etale-descent-is-iso): invertibility for any transformation
  satisfying etale agreement; no construction or transpose equation is asserted.
- `WeilConjectures.finiteMappingEtaleDescent_transpose`
  (lem-sf-finite-mapping-etale-descent-transpose): the normalized scalar and transpose
  formula for such a transformation, without its invertibility.

Holes closed minus holes added is 1 - 3 = -2. The complete assembly explicitly constructs
an inverse natural transformation from component isomorphisms; none of the three statements
is the original existence-and-two-characterizations theorem under a new name.

## No longer needed

No mathematical dependency, library module or unit step is pruned. The original finite-site
comparison route is retained in the new nodes. Existing tool approvals are retained unchanged.

Proof-only imports removed from the final theorem module (the separate steps now carry
their dependencies):

- Sheaf.SmoothPurity.InternalAdjunctionEvaluation
- Sheaf.Paper.BoundedSiteAdjunctionTranspose
- Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
- Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
- Sheaf.SixFunctors.CtfStabilityDirectImages
- Sheaf.Paper.ComparisonTorAmplitude
- Sheaf.Paper.ProEtaleConstructibleOrigin
- Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
- Sheaf.Paper.FiniteStageVerdierBiduality
- Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

These are import relocation through the new proof steps, not a claim that their mathematics
is unnecessary. No adopted-source declaration is removed, weakened or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

No false statement was established. The existing six-step plan leaves substantial glue
between its comparison APIs and this endpoint-sensitive arrow-list formulation. In
particular the finite duality theorem is stated using a Nagata compactification, while
this theorem fixes an arbitrary c; the descent and invertibility proofs must transport
that presentation by compactification independence and right-adjoint uniqueness.
The separate statement docstrings and nodes spell out that step rather than concealing it.

The unit's statement and route are retained. The latest blueprint places the unit under
sec-six-functors-basics, while the existing DAG retains its older sec-six-functors chapter;
the new nodes inherit the assigned node's chapter and unit as required.

The edge cases checked before stating the lemmas are the zero input, the empty scheme,
the geometric point, and arbitrary choice of compactification. Zero and empty inputs
make the mapping functors zero and the pairing identity automatic; the point unit and
its scalar normalization are independent of X. General c is handled by the canonical
compactification independence maps. No ambient unbounded pro-etale adjunction is assumed.

## New nodes

`def-sf-finite-mapping-adjunction-data` records the nineteen relocated, real constructions.
They are not new notions or altered definitions: their source text was compared after
stripping comments, and every declaration signature and body is unchanged.

`lem-sf-finite-mapping-etale-descent` records steps 2, 4 and 6 of the original argument:
transport the ordinary etale mapping transformation, then descend it along the fully
faithful origin equivalence. The prescribed comparison square determines it.

`lem-sf-finite-mapping-etale-descent-is-iso` records the invertibility argument of steps
1--4: all surrounding comparison factors and the ordinary etale adjunction are
isomorphisms, so cancel them and transport along an origin isomorphism.

`lem-sf-finite-mapping-etale-descent-transpose` records step 5: the etale adjunction
mate calculation, finite-site projection/evaluation/counit transport and normalized
point scalar identify the entire Hom-first pairing, then naturality handles all inputs.

All nodes cite paragraph 2 of the latest integral-dualizing proof, carry the three
search kinds and complete proofs in words, and have their exact Lean statements.
The change record is `coord/changes/K1-finite-mapping-adjunction-data.md`.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
