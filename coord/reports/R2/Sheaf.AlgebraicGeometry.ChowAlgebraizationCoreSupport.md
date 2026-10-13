## What changed

Marked `AlgebraicGeometry.chow_algebraization_candidate_support` as
`STATEMENT-DISPUTED`, with an explicit counterexample immediately above its declaration.
Its signature, imports, visibility and proof are unchanged. No definitions, target
statements or other modules were changed. This is a dispute delivery, not a proof or
a decomposition. The stage-3 worker rule requires reporting a false statement rather
than proving a weaker replacement.

## Proved and sorry left

Closed: none (0 of 1). Added: none. Split off: none.

The original hole remains:
`AlgebraicGeometry.chow_algebraization_candidate_support`
(node `new-chow-algebraization-core-support`). It is disputed for the counterexample
below; it cannot safely be proved or reduced to true intermediate statements.

## No longer needed

None. No imports or nodes were pruned. The two planned dependencies were read:
`lem-weil-pbc-support-pullback-finite-type` in
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`, and
`lem-weil-pbc-closed-subset-proper-over-base-properties` in
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`. Both are legitimate
support results, but neither implies reflection of proper support by completion.
No claim is made that they are unnecessary for a corrected compactification argument.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the theorem quantifies over **every** coherent `F` with the specified
completion, whereas its source constructs **one particular** `F` by restriction from a
projective compactification. The latter property was lost in the earlier decomposition.
The parent `exists_chow_algebraization_core` does not have the same problem as a
mathematical existence statement, but its current proof applies this false lemma to
the arbitrary witness supplied by `exists_chow_algebraization_core_candidate`.

Counterexample, checking each hypothesis:

* Set `A = Q[[t]]`, `I = (t)`. This is a Noetherian complete discrete valuation ring.
* Set `Z = Y = Spec Q((t))` and let `f` be induced by the inclusion
  `Q[[t]] -> Q((t)) = Q[[t]][1/t]`. This is the quasi-compact principal open immersion
  `D(t) -> Spec A`, hence separated and of finite type. Both schemes are Noetherian.
* Set `q = identity`, which is proper. Let `Q` be exactly the ideal sheaf in `hQ`.
  Since `t` becomes a unit on `Z`, `Q` is the unit ideal sheaf. Thus `hQ` holds by
  construction, including the global-sections identification in its written type.
* Let `G` be the zero inverse system, with its zero coherent modules, zero ideal
  products and identity quotient comparisons. Its degree-zero support is empty,
  which is proper over `A`; this gives `hR`.
* Let `F = O_Y`, a coherent module on the spectrum of a field. Every positive-power
  quotient by `Q.comap q` is zero, because that ideal is the unit ideal. Hence its
  entire completion is the zero system, giving the required natural isomorphism `hF`.
* Nevertheless `Supp(F) = Y`. Its reduced induced closed subscheme is `Y` itself.
  The morphism `Y -> Spec A` has image `D(t)`, the generic point of this DVR spectrum,
  which is not closed. It is not universally closed, hence not proper. The asserted
  conclusion `HasSupportProperOver (q >> f) F.obj` is false.

The failed step is the first sentence of the node's sole proof step: Nakayama does
not identify all of `Supp(F)` with the support of its completion. It detects support
only on `V(I O_Y)`, which in this example is empty. Completeness of `A` puts `I` in
the Jacobson radical of `A`, but does not put `I O_Y` in the Jacobson radical of the
coordinate rings of arbitrary finite type schemes over `A`.

Source checked directly: Stacks Project, Theorem 30.27.1, Tag 088E,
https://stacks.math.columbia.edu/tag/088E . Its compactification paragraphs first
algebraize on a projective `Y'`, then use properness of `Y' -> Spec A` to exclude
support on the boundary, and finally restrict to `Y`. The proof does not assert that
an arbitrary module on `Y` with the same completion has proper support.
Tag 056J, https://stacks.math.columbia.edu/tag/056J , gives support under pullback,
not the false converse for completion. The exact affine formula found by search is
Mathlib `Module.support_quotient`: `Supp(M/IM) = Supp(M) intersect V(I)`.

The safe repair is to retain the projective candidate and its boundary-support
calculation in the construction's existential conclusion, rather than quantify over
an arbitrary candidate using only its completion. This would change the interface
of this lemma and require a coordinated repair of the parent/candidate modules;
those modules are not silently adapted in this delivery.

Searches run with the required `msearch.py`: LeanFinder on proper support from adic
completion (returned completion definitions and `Module.support_quotient`), Loogle
on `Module.support_quotient` (exact hit), and grep on support/completion/proper-support
names (no matching reflection theorem). Local `rg` searches and the actual signatures
of the planned dependencies and `CoherentFormalModule` were also inspected.

A scratch-only Lean check in `scratchpad/CompletionObstruction.lean` tests the algebraic
part of the example: the Laurent series field is nontrivial, the image of `(t)` is
the unit ideal, and all its positive-power quotient rings are subsingleton. This is
not a formal Lean refutation of the scheme theorem, and is not a delivered module.


## Second reading by R2

1. Compared the entire delivered module with the repository using `diff -u`.
   The only change is seven comment lines marking the statement disputed and
   explaining its counterexample. The existing signature, docstring, visibility,
   imports and proof body are byte for byte unchanged. No change record is needed.
   Verdict: no accidental interface or target change.
2. Compiled the delivered module with the required `lcompile.py`: exit 0, no
   warnings or errors. Independently compiled a scratch copy with
   `#print axioms AlgebraicGeometry.chow_algebraization_candidate_support`:
   it uses exactly `propext`, `Classical.choice`, `Quot.sound` and
   `sorryAx`, with `sorryAx` belonging to the original named hole.
   No new declarations, definitions, holes or forbidden trust mechanisms appear.
   Recompiled the algebraic counterexample scratch file: exit 0. It certifies
   invertibility of t and vanishing of the positive-power quotients, not the
   complete scheme-level counterexample. Verdict: correctly reported as a dispute,
   not a completed proof.
3. There are no split-off statements or new nodes. Independently checked each
   hypothesis of the counterexample against `IsCoherentFormalModule`,
   `formalCompletionSystem` and `HasSupportProperOver`: the zero system meets the
   coherence, annihilation and quotient conditions; empty support is proper;
   identity q is proper; the structure module on the field spectrum is coherent;
   localization at t is separated, quasi-compact and of finite type. Its support
   is the whole field spectrum, whose image is the nonclosed generic point.
   Independently fetched Stacks Tags 088E and 056J. The former computes support
   intersected with V(I) on the projective compactification, then excludes its
   boundary using properness. The latter proves support under pullback, with no
   completion-reflection assertion. Repeated `msearch.py grep support_quotient`
   and read Mathlib's formula `Supp(M/IM) = Supp(M) intersect V(I)`; local searches
   found no valid reflection theorem. Verdict: the counterexample is sound and
   the original universal statement is false; no true reduction can prove it.
4. Read the candidate and parent modules and the two planned dependency modules.
   Their statements do not supply the missing projective-origin property for an
   arbitrary F. There is no shorter sound proof of the unchanged false statement.
   No proof has been completed, so no dependency is claimed pruned; imports remain
   the unchanged plan. The unit `sk-thm-p1` and all its `realized` entries are
   unchanged, and this node realizes none of those entries. Verdict: no bypass of
   the unit's route and no false progress or pruning claim.
5. Read node `new-chow-algebraization-core-support`, its recorded signature,
   `proof`, `proof_deps`, `proof_origin`, source and unit. The Lean signature agrees
   with the node; its proof remains open. The planned Nakayama step is invalid
   away from V(I), precisely as the report and declaration comment flag. No node
   proof fields were rewritten to pretend this plan was implemented. Verdict:
   the existing plan is disputed and needs coordinated repair with the candidate
   and parent, rather than an unsupported proof or a silent statement change.

Second reading changed only this report: added the independent checks and verdicts.
The first reader's module comment and counterexample needed no repair. Closed holes:
none; added holes: none; remaining original hole: exactly the named theorem above.
