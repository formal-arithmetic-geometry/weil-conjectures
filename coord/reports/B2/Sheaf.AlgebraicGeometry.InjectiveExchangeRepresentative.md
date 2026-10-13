## What changed

Reduced `AlgebraicGeometry.Etale.injectiveExchange_representative` by the proved
`Adjunction.derivedPlus_mateEquiv_app_fac` and
`pullbackSquareComparison_hom_app_factorsh`. Naturality in the lifted inverse of
q gives the bounded-below calculation. Two new proof imports isolate source
comparison expansion and target localization/unit transport. All existing
signatures and public imports are unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.injectiveExchange_representative`
(node `lem-weil-pbc-injective-exchange-representative`) by decomposition.
Added one hole, the entire proof of its named theorem:

- `AlgebraicGeometry.Etale.injectiveExchange_target_transport`, node
  `lem-weil-pbc-injective-exchange-target-transport`.

Proved the new `AlgebraicGeometry.Etale.injectiveExchange_source_transport`
(node `lem-weil-pbc-injective-exchange-source-transport`) without any new hole,
by expanding the canonical isomorphism and its identity comparisons.

This is a decomposition, not a sorry-free proof: one original hole closed,
one new hole added. No sorry remains in the original module.
The source identity has no geometric point or exchange map. The target identity
has no derived mate. The original module supplies the genuine mate computation
and its naturality, rather than applying a restatement of its own theorem.

## No longer needed

Removed the unused Square import from the new source-transport module.
Removed the original direct proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`;
`DerivedComparison` already supplies it transitively, so its module is still needed.
All three original dependency nodes remain necessary, directly or through
the two transport statements. No original public import was removed. The proof-only
DerivedComparison import is needed for its pullback comparison factorization.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error identified. The original plan names the needed categorical
identities but leaves substantial bounded-below/unbounded comparison glue.
The earlier attempt timed out during broad concrete rewrites and normalization,
even though the bounded-below calculation compiled. The repaired assembly maps
the source equality explicitly and combines it using elementary private
functor-composition lemmas. It leaves the target transport statement in its
let-bound form; normalizing that large expression was unnecessary. The complete
assembly compiled in 58.2 seconds with the standard 60-second limit.
The source transport itself also compiles as a proof; it no longer needs sorry.
The zero complex and identity q satisfy both identities by identity laws. The
target statement retains the derived unit even for a nonacyclic pulled-back
complex, and assumes no injectivity of that inverse image.

## New nodes

`lem-weil-pbc-injective-exchange-source-transport` is proved and expands only the inverse of the
existing canonical source isomorphism. It follows its definition and the
identity quotient/functor comparisons, independent of any base-change mate.

`lem-weil-pbc-injective-exchange-target-transport` converts the underived exchange
and target unit from bounded-below localization to the unbounded complex-level
formula. It uses exact pullback comparisons, right-derived uniqueness unit
compatibility, and naturality. It does not invert the target unit.

Searches used LeanFinder, Loogle and Mathlib grep; LeanSearch was unavailable
(HTTP Internal Server Error), recorded as unavailable. Existing blueprint search
found no duplicate of these two transport identities. No change record is needed:
existing signatures, definitions, public imports, and module commands are unchanged.
The generic helper binders are attached directly to private lemmas.

Compiler status: the main assembly compiled once in 58.2 seconds, and the first
full dry run compiled all three modules and completed the axiom probes. Its
preflight rejected generic section/variable commands as an interface change;
those commands are now removed, with binders directly on private lemmas.
Further generic naturality experiments did not improve timing and were discarded.
The final proof retains the assembly that had passed compilation, plus the
binder cleanup. The old second reading was removed for a fresh independent reader.

The subsequent dry runs did not print OK: one compiled the source transport in
54.8 seconds and target transport in 32.9 seconds, then timed out on the main
module; the last two timed out on the unchanged source-transport module itself
at 60 seconds, before reaching the assembly. That source module compiled in
20.9 seconds earlier in this session. The validator discards partial diagnostics
on timeout, so these failures provide no Lean error to repair. The final sandbox
remains unvalidated as a complete delivery; nothing was pushed. No limit was
raised, no existing definition or signature changed, and no module was split
to cure the timeout.

Resumed validation: all three delivered modules compiled in import order with
the standard limits: source transport 32.7 s, target transport 17.2 s, and
representative 47.2 s. Earlier silent waits were shared compile-slot contention,
not Lean diagnostics. No proof or signature change was needed for this compile.

## Second reading by B2

1. **Visible declarations and statements.** Compared all three delivered modules with the repository versions. The existing representative theorem signature and all unchanged declarations are byte-for-byte identical; the two added transport theorems are recorded by matching DAG nodes. Verdict: pass.

2. **Proof validity.** Compiled the modules in import order with `lcompile.py --all`. The representative and source-transport proofs contain no `sorry`; the only remaining `sorry` is the named `injectiveExchange_target_transport` split-off theorem. No forbidden `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations occur. Verdict: pass, with the documented split hole.

3. **New statements.** Read [Stacks Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9), final injective-complex paragraph, together with the actual definition of `sourceInjectiveDirectImageIso` and `rightDerivedFunctorPlusCompatibility`. The source proof reverses the defining isomorphism and removes identity quotient comparisons. For the open target statement, the right-derived uniqueness unit equation and inverse compatibility naturality give precisely the stated orientation and terminal factor; `Adjunction.derivedAdjunctionPlus_unit_app_fac` contains the same component calculation, but is not this theorem. The geometric qcqs hypotheses in the stalk theorem are not needed for these purely categorical transport identities. Checked the zero complex, identity q, and arbitrary q via naturality; no target-unit inverse is used in any case. The source statement expands only the canonical source comparison; the target statement retains the target unit and does not assume pulled-back injectivity. Neither duplicates an existing library declaration. Verdict: pass.

4. **Pruning and route.** The proof uses the derived mate factorization, source transport, and target transport; the source-only Square import was removed, while the remaining proof imports are used. The unit `sk-prop-h2` record currently has empty realized arrays; this delivery neither edits that record nor bypasses any realized statement or step. Verdict: pass.

5. **DAG and report consistency.** The node proof steps, dependencies, origins, Lean declarations, and split status agree with the delivered Lean code and this report. Verdict: pass.

Changed during second reading: restored the original single space before the representative proof delimiter, added the missing LeanFinder search record to both new nodes, and simplified the main proof assembly to cure repeated timeouts. Removed private `inclusion_map_exact` and `inclusion_map_exact_comp`: the source equality converts definitionally because the exact bounded-below functor is the restriction of its unbounded functor. Replaced `map_precompose` and the concrete congrArg/trans chain by the fully proved generic `assemble_exchange` lemma, and inferred its result before matching the final goal. The same bounded-below mate factorization is combined with naturality through the fully proved generic `map_comp_naturality` lemma, reducing elaboration of concrete categorical morphism types. No declaration signature or mathematical statement changed. Independent LeanFinder, Loogle, Mathlib grep and repository searches found component comparison identities but no complete transport theorem. The required dry run and delivery are the final validation steps. All old dependency nodes remain used through the two transports; none is pruned. The one closed item hole and one added target-transport hole have net zero: this is a decomposition, not completion of the target import closure.

Explicit second-reader axiom probe (`scratchpad/second-axioms.log`): source transport
uses only `propext`, `Classical.choice`, and `Quot.sound`; representative and target
transport additionally use the expected `sorryAx`. The probe compiled cleanly.
The first observed second-reader dry run compiled both transports but timed out
on the representative at the unchanged 60-second limit; validation is retried
without changing the limit or splitting any module.

Second-reader repaired main module: compiled with the standard 60-second per-file
limit (`scratchpad/second-main-defeq.log`). Its reported 78.2 seconds includes
waiting for a shared compile slot; the actual Lean invocation passed within the
unchanged limit. The source conversion is checked by Lean's definitional equality,
not by an additional assumption. No hole was added by the second reading.

Final second-reader dry run printed OK at `b9880865f3`: all three modules
compiled and preflight passed (CODEX, because of the new modules/nodes and the
one split hole). The retained final simplification combines generic naturality,
definitional source restriction, and generic equality assembly. No option or
time limit change is retained. Both private generic helper proofs are complete.
