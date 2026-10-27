## What changed

Proved `WeilConjectures.PurityFiniteSetting.SectionRestriction.section_base_comparison_laws`
in `Sheaf.Paper.PuritySectionBaseComparisonLaws`, preserving its complete signature and
public import. Only this module and its own DAG node are changed.

Composition comes from the existing ordinary-etale section exchange composition theorem
and naturality/composition of `Dnc.pullComparison`. Identity follows by specializing
composition to identity squares and cancelling, using the published fixed-coefficient
pro-etale pullback unit law.

For restriction, proved private implementation lemmas identify the actual `rho c`
comparison with the inverse of counit-normalized structural locality. The existing chart
comparison formula identifies the compact-support mates; adjoint locality uniqueness and
`rho_canonical` identify their conjugates. The existing structural-locality base-change
and section pullback coherence equations then prove the ordinary-etale square. Naturality
of `Dnc.pullComparison` transports it to the actual pro-etale invariants.

Added only proof imports: `ComparisonPullbackDerivedCoherence`,
`FiniteEtaleDualizingNormalization`, `SectionExceptionalFibreCoherence`,
`ChartNormalizedModelIdentification`, `EtaleAmbientAdjointLocality`,
`SmoothSectionExchangeComposition`, and the source-library pro-etale
`UpperStarCompCoherence`. The `import all` forms access already proved private helpers;
no imported file is modified. Updated the node proof, dependencies and proof origin to
record this route. No definition or statement used by consumers changes.

Validation: the complete delivered Lean module compiled through `lcompile.py` with
exit code 0, no warnings or errors, in 37.9 seconds. Its theorem signature and public
import were checked byte-for-byte against the archived original. The source contains
no `sorry`, forbidden declarations, or lines exceeding 100 characters; node proof
uses agree with `proof_deps`.

The trace-formula node `lem-trf-section-exceptional-fibre-coherence` is used as a
tool for its already proved structural-locality and section-pullback helpers. This
reuses their ordinary-etale square for general commuting section diagrams; it does
not import a trace-formula conclusion or bypass a realized step of smooth purity.
The node proof records the exact source declarations used, including these helpers.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.PurityFiniteSetting.SectionRestriction.section_base_comparison_laws`.
All private helpers are proved. Zero holes remain in this module; zero holes are added;
zero statements are split off. The proof uses existing library declarations as intended
by stage 3; it does not assert that all of their transitive dependencies are axiom-free.

## No longer needed

No original import is removed: the original module had only its public restriction-data
import. The following planned proof dependencies are not needed by this proof:

- `lem-pur-smooth-exceptional-tensor-pasting`
  (`Sheaf.Paper.SmoothExceptionalTensorPasting`): the actual restriction is identified
  with counit-normalized adjoint locality and its already proved base-change equation,
  so no tensor-pasting argument is required here.
- `lem-weil-pbc-proetale-derived-pullback-composition`
  (`Sheaf.Paper.IntegralFinitePullbackComposition`): the statement uses the source
  library's fixed-coefficient pullback compositor directly, including its proved unit
  coherence, rather than arbitrary ring-sheaf pullbacks or integral encodings.

The node retains finite-etale normalization, DNC section geometry and mate calculus,
and records the existing section-exchange, site-comparison, chart-model and locality
lemmas actually used. These pruning claims are local to this proof; no upstream
module, declaration or archived attachment is withdrawn. The blueprint unit route
and its realized statements are preserved.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan suggested tensor-pasting, but the existing counit-normalized
locality API provides a shorter route once its agreement with `rho c` is proved.
No mathematical statement correction was needed. At session start the item was
quarantined; it was restored from its recorded archive without changing its Lean
attachment or treating its absence as withdrawal. Shared-source restoration during
this session did not change the theorem signature.

Delivery attempt: `deliver3.py Q1 Sheaf.Paper.PuritySectionBaseComparisonLaws`
refused the packet as `COMPILES WITH WARNINGS (local), nothing pushed`. Its combined
compile/probe output contained only three unused-simp warnings at lines 565–566 of
an unpublished dependency, `Sheaf.AlgebraicGeometry.SfP1ChartExchange`, compiled from
server revision `2a0c43ce3f788af2905d8e5d188a47531e764730`. The probe reached
`SHEAF-PROBED 9`; the item itself compiled in 27.8 seconds during that attempt.
The standalone compile was warning-free in 37.9 seconds. The delivery warning gate
at `deliver3.py:313` rejects warnings anywhere in the combined output, including
these dependency messages. This dependency is reached through the required public
restriction-data import and DNC comparisons, so removing proof imports cannot
avoid it. No launcher script was patched or bypassed, and nothing was pushed.

`coord/claims/Sheaf.AlgebraicGeometry.SfP1ChartExchange.lock` records holder B2.
The warning is pre-existing in its unpublished repair; no interface change in this
packet caused it. The cross-group forced-adaptation exception therefore does not
authorize editing that module merely to silence its warnings. This is a delivery-tool
blocker, not an unfinished proof or a file over the compile-time limit.


Resumed attempt, 2026-10-27: started with the required delivery check on the
retained packet. It again exited 1 with `COMPILES WITH WARNINGS (local), nothing
pushed`, reproducing the same three unused-simp warnings at
`SfP1ChartExchange.lean:565-566` from the cached unpublished dependency revision
recorded above. The check again reached `SHEAF-PROBED 9` and compiled the item in
27.8 seconds. Current ownership still records B2 for that dependency and Q1 for
this item. No interface change here forces an adaptation of B2's module, so no
cross-group edit is authorized. The archived theorem signature was rechecked
byte-for-byte; the retained item still has zero holes and no overlength lines.
The completed Lean proof and node are retained unchanged for the next attempt.

Latest retained-packet check, 2026-10-27: delivery again exited 1 at the
warning gate with the cached 27.8-second result and `SHEAF-PROBED 9`, without
pushing. The shared clone now has the warning cleanup in
`SfP1ChartExchange`: the three redundant simp arguments are already removed
after an explicit `dsimp only` at the corresponding proof. Nevertheless the
delivery result still reports the older unpublished dependency revision
`2a0c43ce3f788af2905d8e5d188a47531e764730` and its three warnings.
This is stale compile-result/dependency diagnostic reuse by the delivery
service; its normal command exposes no refresh option. B2 still holds the
dependency. No launcher/cache file was altered, and no cross-group module
was edited. Rechecked the item against the quarantine: exact theorem
signature preserved, zero holes, all lines at most 100 characters, and node
proof uses exactly match its proof dependencies. Work remains retained.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
