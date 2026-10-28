## What changed

Corrected the non-target arbitrary-Diagram transport theorem by adding the
missing scalar first-trace base-change square as `ht`. Its original conclusion
is unchanged. The canonical caller retains its original signature and obtains
`ht` from its existing Family and Reference through `first_scalar_trace`.

Constructed `firstTraceExchange` as the actual opposite mate of the fixed
self-square comparison, followed by the specified line comparison. It contains
no unproved data. Separated the trace-free Kunneth identity, the scalar trace square, and normalized
projection scalar evaluation. The item combines their path equalities by symmetry and transitivity.
Functoriality and scalar whiskering belong to the Kunneth and projection steps.

The intermediate statements use the fixed coefficient object and line to avoid
reconverting their large generic module-category presentations.
The native combining proof uses symmetry and transitivity of the two path equalities.
The Kunneth equality permits an arbitrary first-projection functional and keeps
firstTerminalFunctional folded; projection evaluation permits arbitrary prefix arrows. These avoid unfolding the large geometric prefix
when combining the genuine separate steps. Experimental structural comparison
code was removed after it exposed the projection normalization obligation. All edits are under Sheaf, its DAG records, and the
change record.

## Proved and sorry left

The assigned module originally had one hole, in
`AlgebraicGeometry.ProEtale.RationalP1.rationalP1_first_trace_transport_counit_expanded_for_diagram`.
The corrected theorem has a complete combining proof and zero holes. The old
false arbitrary-Diagram statement has not been proved. This delivery is a
statement repair and decomposition, not a net theorem-proof gain.

The delivery adds exactly three named holes:

- `AlgebraicGeometry.ProEtale.RationalP1.first_trace_pretrace`, node
  `lem-sfb-rational-p1-first-trace-pretrace`: the comparison before any trace is
  inserted. Its functional is arbitrary. Diagram supplies only the fixed first-direct-image
  identification, with no use of its chosen traces or integration equations.
  It contains no Family, Reference, or scalar trace compatibility.
- `AlgebraicGeometry.ProEtale.RationalP1.first_scalar_trace`, node
  `lem-sfb-rational-p1-first-scalar-trace`: normalized scalar trace base change.
  It has no arbitrary M or any of its projection/exchange invertibility
  assumptions, and no expanded counit or terminal-functional equation.

- `AlgebraicGeometry.ProEtale.RationalP1.projectionMate_scalar_evaluation`, node
  `lem-sfb-rational-p1-projection-scalar-evaluation`: evaluation of the normalized
  right projection mate on a scalar-compatible functional for the fixed coefficient object. It has no trace, Diagram,
  line object, Reference, base-field hypothesis, or invertibility hypotheses.
  It uses the fixed prime l and coefficient option c of the project.

Thus one old holed declaration is repaired/reduced, three holes are added, and
there are three holes in the packet. The combining proof and the exchange definition are complete. The canonical
caller has zero holes before and after adaptation.

## No longer needed

No whole existing module or node is withdrawn. Both trace base change and the
Kunneth route of the blueprint unit are retained. The old node's unused
localizing-closure and constructibility statement dependencies are removed:
`sk-def-localizing-closure` and `sk-def-sfb-constructible`. The generalized
statement has no localizing-closure hypothesis; the canonical caller still
retains its existing one.

Removed the item's direct public imports of RationalTatePullback (already
re-exported by RationalP1SecondPretraceData), LocalizingClosure, and
DiagonalCoefficientReference. The last two have no role in the conditional
arbitrary-Diagram statement; the canonical caller retains its own public imports.
The new exchange definition imports only RationalP1DiagonalTensor and
CondensedAmbientExchange. Its consumers import SectionEvaluation and
SecondPretraceData explicitly for the definitions their statements use.
No adopted-source declaration has become unnecessary or been changed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old version): `Diagram.traceq` has no normalization or
compatibility field tying it to `trace₁`. Only trace₁ and trace₂ occur in the
integration axioms. Changing traceq to zero leaves every old hypothesis intact
and makes the left-hand composite zero. For a normalized canonical first trace
over a geometric point, with M the coefficient unit, the right-hand terminal
functional is nonzero on the Chern summand. Arbitrary diagrams therefore cannot
satisfy the old claim. The earlier generalization removed Family and Reference
while also forgetting the scalar square they supplied.

The correction adds exactly the missing square. The sole caller already has
the canonical data needed to supply it, so neither its statement nor any target
statement is weakened or changed. The new scalar trace lemma is only a trace square; the Kunneth lemma uses an arbitrary first-projection functional
and no scalar trace compatibility. The projection scalar evaluation is a generic unitality
calculation, independent of either geometric assertion. None is the original
combined obligation under a different name.

Edge checks: all comparison and evaluation equations remain identities for
M = 0 and the zero line. The trace-free statement makes no trace assumption.
The canonical scalar statement uses Reference's completed trace normalization;
it does not assert a square for an arbitrary Diagram. The opposite mate is
constructed without requiring the exchange on its scalar object to be
invertible.

## New nodes

`def-sfb-rational-p1-first-trace-data` records the constructed opposite mate
`firstTraceExchange` in RationalP1FirstTraceData. Its source is the first
triangle identity's trace base-change step.

`lem-sfb-rational-p1-first-trace-pretrace` records the trace-free factorization
in RationalP1FirstTracePretrace. Its proof plan applies the existing two ringed
Kunneth factorizations, transports their maps to the native module interface,
and cancels the specified inverse projection and tensor-shift factors.

`lem-sfb-rational-p1-first-scalar-trace` records first_scalar_trace in
RationalP1FirstScalarTrace. Its proof plan uses the completed trace pullback
square, Reference's full-unit-normalized realization squares, and Family's
scalar squares. Each new statement carries a source and a full proof in words.

`lem-sfb-rational-p1-projection-scalar-evaluation` records normalized scalar
projection evaluation in RationalP1ProjectionScalarEvaluation. The generic scalar-whiskering,
naturality/right-unitality argument is available in the adopted projection-map
library. Its specialization, after tensoring the assumed scalar square with M, needs
the normalized projection family's HEq comparison and the equality of the
original oplax unit with the cached strong unit. Attempts exposed distinct cached instance expressions such as
projectionDerivedMonoidal versus internalMonoidal and reached the elaboration
limit while converting them. The final interfaces retain an arbitrary first functional and arbitrary prefix
arrows, and leave firstTerminalFunctional folded. This avoids reopening its
large cached tensor instance expressions in the combining proof. This technical interface transfer is the part
left in the third, genuinely independent lemma. Specializing the intermediate
statements to the fixed coefficient object avoids the kernel conversion cost of
instantiating their generic module-category presentations in the combining proof.

The corrected item node records its new hypothesis and its only caller; the
parent node records its revised proof dependencies. The statement-change
record is `coord/changes/rational-p1-first-trace-scalar-square.md`.

## Forced adaptations

The only existing module adapted besides the assigned item is
`Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded`, currently unclaimed
in the shared snapshot. Its proof import and the last application line are
changed to supply `first_scalar_trace l c k p hpl Y δ family reference`.
Its existing signature, visibility, hypotheses and conclusion stay verbatim.
Compiling the original caller against the repaired signature fails at its final
application (original line 141): the expression has type `scalar_square → terminal_equality`,
but the goal is `terminal_equality`. The proof import of RationalP1FirstScalarTrace
and the added final argument supply exactly this missing scalar square. The adapted
caller compiled in 13.6 seconds without changing its statement.

Validation: the six-file packet compiled in import order; the repaired item took
20.3 seconds and kernel checking took 2.3 seconds. The longest new statement module
took 16.0 seconds. The final compile after removing profiler options and formatting passed without
warnings: 20.0 seconds for the item, 13.3 seconds for its caller, and at most
16.4 seconds for any new statement module. The three holes are exactly the three
named split statements listed above.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1FirstScalarTrace": "47f2eaf8a24956a7c344ef421fd76e3699d459f2", "Sheaf.Paper.RationalP1FirstTraceData": "a23c62fe95cac8b86fab18c01217213ed1720141", "Sheaf.Paper.RationalP1FirstTracePretrace": "5374f688dcf21d6b99b3cdf6ddad328090d88092", "Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded": "3e2028f0a32bd238495c71abf4a10cacffb1a342", "Sheaf.Paper.RationalP1FirstTraceTransportCounitExpandedForDiagram": "b01e8bda03ad021096bbe5df269f637e346bd2bd", "Sheaf.Paper.RationalP1ProjectionScalarEvaluation": "6c17164ab0fa0f00c1c2543bab1be2884b1bb9ae"}, "results": {}, "time": "2026-10-28T12:33:13+0800", "transitive": 0, "version": 1}
```

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
