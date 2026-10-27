## What changed

Proved `AlgebraicGeometry.ProEtale.etaleClosedOutput_bounds` in
`Sheaf.AlgebraicGeometry.EtaleClosedOutputBounds`, without changing its signature,
public imports, definitions, or either independent implication.

Transport the two `HasOpenComplementCondition` clauses across
`rightDerivedFunctorPlusCompatibility`. Apply the existing closed-support amplitude
lemma for (a). The canonical finite-ring constructible derived comparison supplies
intrinsic bounded constructibility directly; exact comparison preserves the stated
cohomology interval.

For (b), reuse the proved generic `closed_support_boundedConstructible_torAmplitude`
helper of `EtaleClosedSupportTorAmplitude` and `residue_test` of
`ResidueTorAmplitudeTest`, accessed with private `import all`. The recorded
uniformizer has nilpotent image and maximal principal ideal in the quotient.
A proved private helper transports maximality to its ULift, so the same residue
argument applies to `P.Coefficient` without changing any coefficient construction.
Apply `comparison_torAmplitudeIn_iff` and explicitly compose the exact-composite and
bounded-below/unbounded comparison isomorphisms. The output still tests every
pro-etale module sheaf.

Updated the existing node's proof, proof dependencies, and proof origin to match.
No dependency module was edited, no public declaration was added, and no change
record is needed. The unit's closed-support route remains intact.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.etaleClosedOutput_bounds`
(node `lem-pur-etale-closed-output-bounds`).

Added 0 holes; split off 0 statements; 0 `sorry` remain in the delivery.
The private helper `ulift_span_isMaximal` is fully proved.

The complete proof compiled cleanly through `lcompile.py` (22.5 seconds before
removing unused proof imports); the pruned version is checked again for delivery.
The cohomological branch uses no Tor premise. The Tor branch uses no premise of
(a). Ordering of the enlarged interval follows from r<=s and c>=0. The residue
argument uses n>=1; it also handles n=1, where the uniformizer image is zero and
its zero ideal is maximal. Empty schemes and the identity closed immersion
require no extra geometric hypothesis. No axiom or data-valued hole was added.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`: no direct
  reference is needed; the actual full-site Tor predicate comes from the recorded
  comparison theorem and the existing statement imports.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`: its continuous-coefficient origin
  equivalence is unnecessary for this canonical intrinsic comparison.
- `Sheaf.Paper.ComparisonPullbackExact`: exactness and preservation of intervals
  are supplied directly by `finiteCoefficientIntrinsicComparison` and the generic
  exact-functor API.

The direct proof dependencies `lem-sf-proetale-constructible-origin` and
`lem-sf-comparison-pullback-exact` and their obsolete top-level `tool_uses`
approvals were removed from the item node. The existing
`lem-weil-pbc-finite-ring-constructible-derived-origin` replaces the former at
exactly the required intrinsic coefficient presentation. These modules may still
be reached transitively or by other consumers; no whole module is withdrawn.
All other declared dependencies are retained. No blueprint unit step was pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematics of the planned argument is sound. Its interfaces need glue that
was omitted: the complement condition is stated with the bounded-below derived
functor, while the closed-support bound uses the unbounded functor. The proof now
supplies their homology isomorphisms explicitly.

The public specialization `closedImmersion_rightAdjoint_torAmplitude` takes
E : Type (u+1), whereas the purity setting has E : Type u and uses ULift of its
quotient for fixed coefficients. Rather than identify separately chosen
uniformizers after lifting E, the proof uses the already proved generic helpers
of the same residue argument, with the lifted image of the original uniformizer.
This is a proof-only specialization, with no definition or statement repair.

The original constructible-origin theorem has a continuous-ring derived-category
presentation. The existing arbitrary-finite-ring comparison theorem works
directly with the intrinsic comparison in this statement and avoids this extra
presentation conversion. The final Tor comparison likewise needs the explicit
composite-functor and plus-compatibility isomorphisms, now present in Lean.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
