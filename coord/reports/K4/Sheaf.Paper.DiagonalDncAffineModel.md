## What changed

Restored the assigned module from quarantine/Sheaf/Paper/DiagonalDncAffineModel.lean,
following its current rework row. Preserved its theorem statement and docstring.
The theorem now has a complete categorical assembly proof from two separate geometric
equations, imported privately from new modules.

RestrictedAffineDiagonalSectionTrace constructs the intermediate arrow S explicitly.
For B = p inverse V and h = p restricted to V, the self-product of h and the affine
tower over B are pullbacks of the same cospan. Their unique limit comparison gives
the coordinate isomorphism; its projection equation is proved in Lean. Restrict the
actual affine counit mate over B to the image of the diagonal under this isomorphism,
then apply the canonical section and site comparisons. This defines S without an
existence witness, DNC, alpha, rho, or the counit mate over Y.

RestrictedAffineDiagonalDncTrace states S delta beta = identity. It concerns only
DNC specialization and integration on the source and normal section objects.
RestrictedAffineDiagonalTraceBaseChange states the separate trace base-change equation
S alpha rho.inv c = tate.inv m_Y. Its input H contains only geometry; it has no chart
beta, normalization assumption, or DNC comparison.

The private, proved helper assemble_section_trace cancels delta and beta to identify
beta.inv delta.inv with S, substitutes the independent trace equation, and cancels
tate against its inverse. No existing module other than the assigned item is changed.

Validation: lcompile.py --all on the sandbox compiled all four Lean modules with
exit code 0. The assigned theorem signature was also compared against its archive
and is unchanged; all Lean lines are at most 100 characters.

Delivery attempt: deliver3.py again compiled all four modules successfully, but
refused with COMPILES WITH WARNINGS (local), nothing pushed. The warnings were
from the unpublished dependency Sheaf.AlgebraicGeometry.SfP1ChartExchange,
lines 565-566: unused simp arguments ordinaryFinitePullback, ordinaryFiniteLine,
and ordinaryFiniteDegreeZero. They were emitted while the compile service built
its private dependency overlay, not by any delivered module. The current claim
record assigns that module to B2. This is an upstream-warning delivery-gate
blocker; no launcher tool or other group's module was changed to bypass it.

Retry on 2026-10-27: ran the required initial deliver3.py check against the retained
sandbox. It again reported all four delivered modules as compiled, then exited 1
with COMPILES WITH WARNINGS (local), nothing pushed. The same three unused-simp
warnings came from SfP1ChartExchange in the private dependency overlay at
360cd023feb858778e000872ea3becb49fe0a920. The current source still contains those
simp arguments, and its current claim is B2. This confirms the prior tool failure;
no delivery branch was pushed and all retained work is preserved.

Dispatcher retry (following the prior worker's try 2 of 5): the required initial
deliver3.py invocation again exited 1 with COMPILES WITH WARNINGS (local), nothing
pushed. All four sandbox modules were reported compiled. The private overlay again
replayed the three unused-simp warnings from SfP1ChartExchange at lines 565--566,
source revision 360cd023feb858778e000872ea3becb49fe0a920. The current claim file
coord/claims/Sheaf.AlgebraicGeometry.SfP1ChartExchange.lock still names B2.
Our packet changes no interface that forces an adaptation of that dependency;
the other-group ownership rule therefore does not authorize its warning cleanup.
No tool, dependency, archive, or budget file was changed. The retained delivery
and its two explicitly reported split-off holes remain available for resumption
after the dependency warning or the dependency-warning gate is repaired.

Dispatcher retry after try 3 of 5 (2026-10-27): the required initial delivery check
again exited 1 before pushing. All four sandbox modules compiled; the only warnings
were the same three unused simp arguments in SfP1ChartExchange, lines 565--566,
replayed from the private overlay cache at 360cd023feb858778e000872ea3becb49fe0a920.
The current library source still has those arguments, and the claim still names B2.
The assigned library source is identical to its quarantined text; comparison with
the retained repair confirms its statement and public import are preserved.
The warning gate in deliver3.py rejects dependency warnings together with packet
warnings. No authorized forced adaptation applies, and launcher tools may not be
patched. Nothing was pushed; the Lean files, node files and two holes are retained.

Final dispatcher retry after try 4 of 5 (2026-10-27): the required initial
deliver3.py check again exited 1 with COMPILES WITH WARNINGS (local), nothing
pushed. All four sandbox modules compiled. The only diagnostics were the same
three unused-simp warnings from unpublished SfP1ChartExchange, lines 565--566,
replayed from private overlay revision 360cd023feb858778e000872ea3becb49fe0a920.
The current claim names B2 and K4 has no return entry authorizing a dependency
adaptation. A subsequent source check found the current shared source now omits
these three arguments: the failure replayed cached diagnostics from the older
private overlay despite that source repair. Since this packet does
not change an interface forcing that dependency to change, cleaning its proof is
outside the other-group adaptation exception. The launcher warning gate cannot be
patched by workers. All four Lean modules and all four node files remain retained;
the original theorem has zero holes and the two split-off theorem holes remain.

## Proved and sorry left

Closed the original hole in
WeilConjectures.PurityFiniteSetting.diagonalDncAffineModel
(lem-pur-diagonal-dnc-affine-model) by decomposition, not by an independent proof
of its geometric normalization. Its module has zero remaining holes.

Added exactly two holes, each the entire proof of a named public theorem in its own
new module, with its source and complete proof in words:

- WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalDncTrace
  (lem-pur-restricted-affine-diagonal-dnc-trace).
- WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalTraceBaseChange
  (lem-pur-restricted-affine-diagonal-trace-base-change).

The coordinate construction, its projection theorem, and the actual section trace
construction have no holes. No axiom or hole in a definition is introduced.
The delivery therefore closes one original hole and adds two simpler holes; it is
a decomposition with net hole change +1, not a claim of net sorry reduction.

Each remaining theorem is a separate part of the argument. The first compares S with
the normal section through delta and beta, without alpha, rho or m_Y. The second
compares S with m_Y through alpha and rho, without delta or beta. Neither is the
assigned four-factor equality under another name or with a repackaged hypothesis.

Edge checks: the universal-property construction works for d=0 and the empty open;
the Tate comparison uses the empty ordered tensor at rank zero. No choice of point,
positive dimension, nonempty scheme, or separatedness of aY was introduced. The
separated local source required for DNC is supplied by E.geometry, as before.

## No longer needed

No original public import was removed and no existing module is withdrawn. No claim
of pruning from the targets' import closure is made.

The assigned node's old proof dependencies are replaced by the actual construction
and two equations used by its Lean proof. In particular the old separate invocation
of lem-pur-affine-target-diagonal-dnc is unnecessary because the chart already supplies
its geometry; lem-asd-tensor-mate-etale-precomp is not used in the categorical assembly.
The other geometric dependencies are retained below the two equations where relevant.
Some modules remain present through the unchanged public import of
DiagonalCounitComparisonData; changing a proof-dependency edge does not remove those
modules from the library or its import closure.

Did not import AffineDiagonalIntegrationOrientation, AffineDiagonalDncNormalization,
AffineDiagonalDncCoordinateIdentity, DiagonalDncChartNormalization, or
ChartDncVectorFactors. The apparent earlier affine-diagonal route is circular: for
example AffineDiagonalIntegrationOrientation imports VectorIntegrationSiteComparison,
which reaches CartierKummerMap, CartierKummerDescent, AdicPurityRootComparisons,
FiniteCoefficientSmoothPurity, SmoothPurityMap, PurityDiagonalDualizingObject,
DiagonalOrdinaryOrientationNormalization, DiagonalAffineCounitRestriction, and this
item. The new section-trace construction uses the independent pullback and ordinary
affine-counit API, without changing that shared chain.

## Where the brief, the DAG or earlier work was wrong

The assigned source is absent from lean/ because it is quarantined, not because it
was withdrawn. Its archive and Lean attachment are preserved, and the restoration
is part of this delivery. The archived theorem compiled before editing.

The earlier plan does not supply the two exact derived-arrow equations needed to
combine its geometric steps. Those equations are now stated independently, with an
explicit intermediate arrow whose construction is checked by Lean. The prior full
affine-diagonal calculations cannot simply be imported because of the cycle above.
No mathematical statement or target definition was changed and the unit route stays
the diagonal, DNC, normal-vector integration route.

## New nodes

- def-pur-restricted-affine-diagonal-section-trace: the canonical coordinate isomorphism,
  its proved first-projection equation, and the concrete section restriction of the
  actual affine counit over B. Module RestrictedAffineDiagonalSectionTrace.
- lem-pur-restricted-affine-diagonal-dnc-trace: the DNC/normal-section integration
  equation S delta beta = identity. Module RestrictedAffineDiagonalDncTrace.
- lem-pur-restricted-affine-diagonal-trace-base-change: the separate trace base-change
  and diagonal-restriction equation. Module RestrictedAffineDiagonalTraceBaseChange.

No change record is needed: only the assigned module and new modules/nodes are changed,
and every existing declaration signature and public import is preserved.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
