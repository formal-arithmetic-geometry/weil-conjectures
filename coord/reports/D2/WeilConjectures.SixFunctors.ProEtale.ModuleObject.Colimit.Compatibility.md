## What changed

Removed the upstream-sync reintroduced declaration
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`,
whose proof was `sorry` and whose docstring marked the all-unbounded assertion as disputed.
Removed the anonymous all-unbounded Omega-coefficient Shriek example that depended on that
instance. Updated the module documentation to describe the retained bounded-below component
comparison. The existing theorem
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE` and its proof are unchanged.

The removed declaration is not needed by the target route: the bounded constructible consumer
uses the retained component theorem and extracts a lower cohomological bound. The module compiles
cleanly after the repair.

## Proved and sorry left

The retained bounded-below component theorem already had a complete local proof, which is
unchanged. It still depends transitively on the existing scalar-basis obligation
`AlgebraicGeometry.ProEtale.CondensedRing.exists_condensedQbar_scalar_basis_unit`
(node `lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit`); its axiom audit includes
`sorryAx`. This delivery does not close that dependency.
The finite-extension push instance and finite-extension Shriek example remain proved.
Original direct holes: 1. Holes proved with their original signatures: 0. Holes added: 0.
The retired hole is
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`.
It is removed as unused by the reviewed bounded target route, not reported as proved. The repaired
item module has zero direct `sorry` declarations. No remaining direct holes or new split-offs exist.

## No longer needed

The disputed all-unbounded instance
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper` and the anonymous Omega
Shriek example are no longer needed. No proof-dependency imports were removed, and no DAG node
is removed. The new blueprint ambient assertion remains unresolved; this restores the reviewed
retirement and does not prove that assertion. The bounded-below scalar-basis and copower-continuity
imports remain required by the retained component theorem.

## Where the brief, the DAG or earlier work was wrong

The 2026-10-17 upstream synchronization reintroduced an all-unbounded ambient instance that had
already been retired by the reviewed repair. Its own comment records that the available argument
only establishes bounded-below coproduct continuity and that the ambient exceptional right
adjoint is not available in this module. The target consumer requires only the bounded-below
component theorem, so restoring the retired instance would leave an unjustified `sorry` in the
library. This delivery restores the reviewed interface and removes that accidental regression.


Change record: `coord/changes/condensed-qbar-sync-retirement.md`.

The first worker left the independent second reading to the reader below.

Validation: the repaired item compiled in 46.8 seconds, then in 44.6 seconds, and in the
consumer-check set in 53.1 seconds. All 21 direct importers were checked against the repaired
item: 19 compile. The complete per-module summary is in `scratchpad/consumer-summary.md`.

Two published-snapshot failures prevent completing the consumer validation:
`Sheaf.Paper.CondensedQbarBaseChangeCompatibility` cannot import
`Sheaf.AlgebraicGeometry.OverSquare` because its object file is missing.
`Sheaf.Paper.CondensedFiniteModelProofAPI` cannot find
`isTriangulated_boundedConstructible_of_serre` at line 216. Each unchanged original consumer
independently fails identically without the repaired item overlay (0.2 and 4.8 seconds,
respectively). No consumer was adapted for these baseline failures. There were no timeouts.

Required dry run: `deliver3.py D2
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility --no-push` printed
`OK (dry run)` for commit `3eff85eea9`: the item compiles and preflight passes except for the
second reading, which the wrapper explicitly reserves for the independent reader. Nothing was
pushed. The worker has not written the independent reader's section.

## Second reading by D2

1. **Existing interfaces:** compared the complete repository and sandbox modules with `diff`
   and the delivery declaration parser. All 74 retained declaration signatures and bodies are
   identical; all imports are unchanged. The only named declaration removed is the disputed
   all-unbounded instance, and its dependent anonymous Omega Shriek example is also removed.
   This intentional interface retirement is declared in
   `coord/changes/condensed-qbar-sync-retirement.md`, with verbatim old signature and the
   downstream-user table. It restores the interface explicitly approved in the landed F3
   `condensed-qbar-bounded-push.md` record. No definition or target statement changes.
   Verdict: pass as a declared repair, not as a proof of the retired statement.

2. **Proof and axioms:** read the entire module and independently compiled it through
   `lcompile.py`: exit 0, 52.7 seconds, no warnings. There are no direct holes, new axioms,
   unsafe declarations, opaque declarations, or hollow definitions. A scratch copy with
   `#print axioms` compiled in 50.5 seconds. The coefficient-composition lemma, adjoint and
   colimit witnesses, both flatness instances, and finite-extension push instance use only
   `propext`, `Classical.choice`, and `Quot.sound`. The bounded-below component additionally
   uses `sorryAx`; the existing scalar-basis-unit theorem is still open upstream of it.
   The scratch audit's only warnings concerned the length of the appended audit commands;
   they are absent from the delivered file. Verdict: pass with the existing transitive
   obligation explicitly recorded, not a claim of an axiom-free bounded comparison.

3. **Split statements:** no statement or node is added, no hole is split off, and no proof
   is replaced by a restatement. The retired claim is not replaced by a weaker statement
   under its name. The finite basis is constructed from continuous coordinate maps, and
   the existing scalar-basis existence theorem is eliminated only inside a proof, not used
   to manufacture public data. Verdict: no new split obligations to validate or deduplicate.

4. **Route and pruning:** checked the retained finite-basis and bounded-below arguments,
   their imports, the bounded constructible consumer, the landed retirement record, and
   the relevant unit records. The consumer extracts `N` from boundedness and invokes the
   component theorem, so it does not require the removed ambient instance. A source-wide
   name search finds no external use of the removed declaration. The four existing bounded
   comparison proof dependencies remain used; `FreeLifting` supplies `flat_colimit`, and
   the other proof imports supply the free-module, additive, mate, coproduct, scalar-basis,
   and continuity APIs actually invoked. No unused import or module was identified.
   The unit `sk-thm-properbasechange` and its realized steps are unchanged. The separate
   imported unit `sk-prop-sfb-finite-extension-compatibility` still has its unresolved
   all-unbounded assertion; this repair does not discharge it or change its route.
   Verdict: no new route substitution and no module pruning claimed.

5. **DAG agreement:** opened `lem-weil-pbc-condensed-qbar-bounded-push` and its four proof
   dependencies. Its recorded signature matches the retained theorem, and its proof steps,
   `proof_deps`, and `proof_origin` still describe the scalar-unit/mate/copower argument.
   No existing node record is edited. The imported
   `lem-sfb-qlbar-push-iso-proper` remains unresolved and already flags the missing Lean
   declaration; the report does not count it as proved. Verdict: consistent with the
   restored interface and with the explicitly remaining mathematical obligation.

Second-reading changes: corrected the report's claim that the bounded-below comparison was
fully proved, named its existing transitive hole, and added this review. No Lean code, import,
node, or change record required repair. Net delivery: zero original holes proved, one disputed
hole retired, zero holes added, zero split-offs, and no module pruned. The two pre-existing
consumer snapshot failures remain recorded above; they are not attributed to this repair.

Independent-reader dry run: `deliver3.py D2
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility --no-push` printed
`OK (dry run)` for commit `ab8179001f`: compilation and preflight passed. The tool correctly
classified the declared public-declaration retirement as `CODEX`.
