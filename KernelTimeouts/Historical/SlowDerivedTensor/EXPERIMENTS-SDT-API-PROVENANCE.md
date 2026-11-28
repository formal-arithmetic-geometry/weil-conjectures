# Round 13: derived monoidal API provenance

## Executive summary

**[A1, A2, R1]** The slow consumer declaration is
`AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor`. Its statement
asks for `Etale.derivedTensor A X` to be left derived; its entire value after
`:=` is `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
(Sheaf X.smallEtaleTopology A)`. Checking that value against the declared
type compares `IsLeftDerivedFunctor₂` types whose functor arguments are,
respectively, `curriedTensor D` and `derivedTensor A X`. The latter definition
was compiled as `curriedTensor D` using `MC-D`. The imported `MC-D` bridge was
itself compiled with a `DerivedMonoidal Qh quasiIso` (`D'`) category and
`DerivedMonoidal.instMonoidalCategory` (`MC-D'`) in its generated `_aux_1`.
Thus the generic API is embedded in the compiled specialized provider, not
explicitly written as an equality in the consumer statement. The retained
traces do not establish that the historical consumer check traversed this
provider to compare `MC-D` with `MC-D'` at the archived diagnostic root.

**[A3, R2, O1]** The archived `icd_tensorObj_probe` is a separate diagnostic
lemma. It explicitly states `tensor_D K L = tensor_D' K L` and proves it by
`rfl`. Its saved checked/stored root compares the complete closed type Kernel
infers for that proof with the stored type of *that lemma*. A separate
extraction opens twelve corresponding binders to inspect the `Eq` bodies.
It reproduces the two provider
representations relevant to the consumer, but is not the consumer's original
declaration obligation. Consequently the round-11/12 root events validate a
diagnostic comparison, not a historical event inside the consumer check.

Evidence labels: **A** direct source/declaration audit; **R** direct fresh
elaboration or checking replay; **O** existing original-root evidence from
IDE/IDD/RSR; **C** source/API counterfactual; **I** inference; **U** unknown.
All event IDs below name new probes unless prefixed `O`.

## P1: exact operands and the diagnostic mismatch

**[A1]** Pinned consumer source,
`WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean:69-105`:

```lean
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  curriedTensor _

instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)[A].IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor (Sheaf X.smallEtaleTopology A)
```

The verbatim 109-line module, with an audit command appended, is
`sdtapp/c0-original-source-with-audit.lean`.
The declaration proof has no tactics. **[A2, R1]** Its `ConstantInfo.type` has
ten binders, then `Functor.IsLeftDerivedFunctor₂` with 21 arguments. The
stored functor, argument 10, has head `Etale.derivedTensor/10`; the type
inferred for its stored value by both `Meta.inferType` and `Kernel.check` has
argument 10 headed `MonoidalCategory.curriedTensor/3`, category `D`, and
provider `MC-D`. The value is a ten-argument application of
`DerivedCategory.isLeftDerivedFunctor₂CurriedTensor`. The original
checked/stored types are structurally unequal; a new `Kernel.isDefEq` returns
`true` (`E1-KERNEL`). There is no object-level `Eq` at this boundary. The raw
snapshots were saved before any `whnf` or normalization. `Meta.inferType` and
`Kernel.check` give structurally identical inferred expressions for this
declaration (`app-focused.out`); they are identified separately in the probe.

**[R1]** `E1-BINDER.0-9` opens both original types in a common local context.
All ten binder domains match structurally. No conversion or instantiation was
needed to align domains; each body was instantiated with the same fresh local.
The resulting paths are `root/body^10/arg10` for the functor and
`root/body^10/arg14` for `μNatTrans`. The extraction saved the untouched
raw arguments before making a separate Meta/Kernel DefEq request; the Meta
request returned `true` (`E1-META`), and the Kernel request returned `true`.
The stored `derivedTensor` is an elaborated constant application, while the
checked `curriedTensor D` and its `MC-D` argument come from the imported
adapter signature. No unresolved synthesis metavariable occurs in these
saved expressions.

**[A3, R2, O1]** The exact archived `ide-root.lean` source introduces a *new*
twelve-binder lemma with `K L : D`:

```lean
@tensorObj D _ inferInstance K L =
@tensorObj (DerivedMonoidal DerivedCategory.Qh
  (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
  _ inferInstance K L := by rfl
```

It then calls `Kernel.check` on the lemma value and `Kernel.isDefEq` on the
complete inferred and stored types. The root call itself does not open
binders. `R2` re-elaborates this exact source shape and separately opens the
same twelve domains in one context; all domains match
structurally and are Kernel DefEq without reduction. `root/body^12` is `Eq`.
The inventory below records all six independent positions. `P` abbreviates
the fully elaborated application of the `inferInstance` constant, *not* a
metavariable or a fresh search at extraction time.

| Position | Raw head / category | Category instance | Provider | Path | Source origin |
|---|---|---|---|---|---|
| Checked carrier | `DerivedCategory/4`, D | inside D | none | `root/body^12/arg0` | proof's inferred equality type |
| Checked lhs | `MonoidalCategoryStruct.tensorObj/5`, D | `instCategoryDerivedCategory/4` | `P(MC-D)`, size 1,785 | `root/body^12/arg1` | explicit lhs; compiled `rfl` value |
| Checked rhs | `MonoidalCategoryStruct.tensorObj/5`, D | `instCategoryDerivedCategory/4` | same `P(MC-D)` | `root/body^12/arg2` | `rfl` value's inferred type |
| Stored carrier | `DerivedCategory/4`, D | inside D | none | `root/body^12/arg0` | diagnostic statement |
| Stored lhs | `MonoidalCategoryStruct.tensorObj/5`, D | `instCategoryDerivedCategory/4` | `P(MC-D)`, size 1,785 | `root/body^12/arg1` | explicit diagnostic lhs |
| Stored rhs | `MonoidalCategoryStruct.tensorObj/5`, D' | `instCategoryDerivedMonoidal/6` | `P(MC-D')`, size 11,973 | `root/body^12/arg2` | explicit diagnostic rhs |

**[R2]** Each `tensorObj` spine has five arguments in order: category,
`Category` instance, `MonoidalCategoryStruct` provider, `K`, `L`. The argument
paths are `root/body^12/arg{1|2}/fn^{4-i}/arg` for index `i=0..4`; universe
levels and all five heads are in `app-probe.out`, and the full raw provider
expressions are in `probe-stored-{lhs,rhs}-arg2.raw`. `P(MC-D)` is an
`inferInstance` application whose selected value is the specialized provider;
`P(MC-D')` similarly embeds `DerivedMonoidal.instMonoidalCategory`. The
checked RHS is not the stored RHS: `rfl` has type `tensor_D K L = tensor_D K L`,
and the saved root asks Kernel to compare that type with the declared mixed
equality. The original consumer has no `K`, `L`, or mixed `Eq` proposition.

## P2: category and provider provenance

**[A1, A4, R3]** The source dependency chain for `D/MC-D` is:

1. `Tensor.lean:82-86` writes `DerivedCategory (Sheaf ...)` three times in
   `derivedTensor`'s result type and writes `curriedTensor _` as its value.
   The fresh source replay requests `MonoidalCategory D` at this application
   (`S-D`, `app-trace-d.out:423-644`); candidate lookup includes both the
   underlying derived-category instance and the specialized adapter, selects
   `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`, and
   compiles that argument into `derivedTensor`'s value. An earlier search with
   unresolved `?m.36` was stuck; the successful request has concrete target D.
2. `Tensor.lean:100-105` writes `derivedTensor` in the expected result and
   supplies `DerivedCategory.isLeftDerivedFunctor₂CurriedTensor (Sheaf ...)`.
   The latter's imported stored type at
   `Instances/DerivedCategory.lean:39-42` writes `curriedTensor
   (DerivedCategory C)`. The fresh statement replay also requests
   `MonoidalCategory D` (`S-I`, `app-trace-i.out:854-1065`) and selects the
   specialized adapter. This search belongs to the current statement;
   `MC-D` in the adapter's *imported* signature was fixed when that module
   was compiled. The application instantiates its formal `C` with `Sheaf ...`
   and its other ten formal arguments with the compiled terms listed in
   `app-decls.out`.
3. `Instances/DerivedCategory.lean:34-35` declares the specialized
   `MonoidalCategory (DerivedCategory C)` as `inferInstance`. Its compiled
   value is `inferInstance` applied to
   `DerivedCategory.instMonoidalCategory_weilConjectures` (`app-decls.out`).

**[A4]** The `D'/MC-D'` chain is entirely inside imported declarations at
this consumer site:

1. `FromJoel/CategoryTheory/Monoidal/Derived.lean:30-39` defines
   `DerivedMonoidal L W := D`, where `D` is the target of `L`, and
   `toDerivedMonoidal L W := L`. Its instance at lines 270-271 has formal
   target `MonoidalCategory (DerivedMonoidal L W)` and compiled value headed
   `MonoidalCategory.ofBifunctor`.
2. `FromJoel/Algebra/Homology/DerivedCategory/Monoidal.lean:33-39` declares
   `MonoidalCategory (DerivedCategory C)` with value
   `inferInstanceAs (MonoidalCategory (DerivedMonoidal Qh
   (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))))`. In the compiled
   `DerivedCategory.instMonoidalCategory_weilConjectures._aux_1`, its
   `toMonoidalCategoryStruct/3` spine has category `D'`,
   `instCategoryDerivedMonoidal/6`, and provider
   `DerivedMonoidal.instMonoidalCategory/10` (`app-decls.out`,
   `decl-bridge-aux-value.raw`). This is where both the generic category and
   its provider are first explicitly written/supplied on the audited
   dependency path. Formal `L` and `W` instantiate to `Qh` and `quasiIso`;
   their target is definitionally `D`. This is a compiled provider argument,
   not a fresh consumer-site search for `MC-D'`.
3. The specialized adapter's value points to that bridge; hence its
   expression can expose the generic provider during conversion. The generic
   `Functor.HasDerivedMonoidalCategory` field at
   `Derived.lean:142-145` and the left-derivability bridge at
   `FromJoel/Algebra/Homology/DerivedCategory/Monoidal.lean:45-53` are on the
   imported proof's dependency path, but neither places a top-level `D'`
   category argument in the consumer's stored or inferred functor argument.

**[A5]** `DerivedCategory.hasDerivedMonoidalCategory` at
`CategoryTheory/DerivedCategory/HasMonoidalDerivedCategory.lean:64-76` supplies
the `Qh.HasDerivedMonoidalCategory quasiIso` premise. Its value is `sorry` in
the pinned source; this audit uses its type and compiled application only.
The source `LocalizerMorphism.DerivesMonoidalStructure.hasDerivedMonoidalCategory`
at `FromJoel/CategoryTheory/Localization/DerivabilityStructure/Monoidal.lean:59-74`
constructs the generic class in another route, but no audited edge from the
consumer uses that lemma. It is excluded from the causal chain.

## P3: meeting point and D-level synthesis

**[R4]** C0 is the complete, unchanged consumer module at the original
relative source path in an isolated checkout. Its source SHA-256 equals the
pinned source, and Lean checks it normally with the READY4.2 executable.
`C0`'s new raw `ConstantInfo.type`, value, and Kernel-inferred type are each
byte-identical to the imported pinned declaration snapshots. `E1` then
opens the ten structurally matching binders, records the 21-argument actual
and expected types, and obtains Meta and Kernel DefEq `true`. The concrete
typing requirement is the `:=` value of
`isLeftDerivedFunctor₂_derivedTensor` against its declared type, implemented
by pinned Lean's `elabTermEnsuringType`/`ensureHasType` and `isDefEq`
(`Lean/Elab/MutualDef.lean:552`, `Lean/Elab/Term/TermElabM.lean:1334-1340,1889-1895`).
The source-side term elaboration can instantiate the adapter's `C` from the
explicit `Sheaf ...` argument and match the adapter result against the
expected `IsLeftDerivedFunctor₂` type. The imported adapter fixes the
checked functor to `curriedTensor D`; the expected type fixes the stored
functor to `derivedTensor A X`. Its compiled body fixes `MC-D`.

**[R3]** `S-D` and `S-I` are fresh *source-site* class searches observed by
`trace.Meta.synthInstance` on faithful source copies, using the trace classes
present in pinned `Lean/Meta/SynthInstance.lean:1063-1077`. `S-D`'s concrete
goal is `MonoidalCategory (DerivedCategory (Sheaf ...))`; the candidate list
contains `DerivedCategory.instMonoidalCategory_weilConjectures` and
`DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`, and the
selected result is the latter. `S-I` has the same concrete D-level goal and
result. `S-I` also shows a speculative `MonoidalCategory (DerivedCategory
?m.41)` goal before the category is fixed. There is no source-site
`MonoidalCategory D'` goal in either faithful trace. The separately supplied
`D'` control (`S-DPRIME`, `app-dlevels.out:882-1320`) has candidate list
`SemiCartesianMonoidalCategory.toMonoidalCategory`,
`DerivedMonoidal.instMonoidalCategory`, and a local coefficient instance;
it selects `DerivedMonoidal.instMonoidalCategory`. This is a controlled
search, not a historical consumer event.

**[R5, U1]** An exploratory `trace.Meta.isDefEq.delta` run emitted
`unfoldLeftRight CategoryTheory.DerivedMonoidal` (`e1-delta-excerpt.txt`).
Because that option also traced command elaboration, this event cannot be
assigned uniquely to the original ten-binder type comparison. It is not
evidence that the historical consumer check unfolded D' or compared the two
monoidal providers. No fresh D' class search or
`DerivedMonoidal.instMonoidalCategory` unfold was identified in that run.

**[I, U1]** The earliest source-level meeting point is the consumer's
declaration value against its expected type, not the archived equality
lemma. The current traces establish the operands and source-site searches,
but do not retain an event-ID-level trace from the original
historical declaration elaboration recording every metavariable assignment
at the exact `ensureHasType` call. A small observational hook in that pinned
elaborator call, on the isolated copy, would close this narrower gap. The
delta trace also captured unrelated command elaboration; its
`DerivedMonoidal` reduction cannot be assigned to the target comparison.
No Kernel instrumentation was added.

## P4: source controls

| Control | Source intervention | Ordinary Lean result | Mixed-API endpoint | Evidence / limit |
|---|---|---|---|---|
| C0 | Exact unchanged consumer module | checked; empty diagnostics | Original `derivedTensor`/adapter matching reproduced; imported bridge still contains `D'/MC-D'` | [R4] source and three raw declaration snapshots match pinned bytes |
| C1 | Replace only expected functor `derivedTensor` with `curriedTensor (DerivedCategory (Sheaf ...))` in the instance statement | checked | Top-level expected/inferred functors now both `curriedTensor D` with `MC-D`; the imported `MC-D` bridge still contains `D'/MC-D'` | [C1] This tests the abbreviation/expected-functor head, not a D-to-D' category switch. Other generated arguments re-elaborate, so the full types remain structurally distinct. |
| C2 | In `derivedTensor`'s value replace `curriedTensor _` with `@curriedTensor D _ (DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory (Sheaf ...))` | checked | The same provider is explicitly attached, and the imported `D'/MC-D'` remains | [C2] This removes fresh selection at that source site but does not intervene on the compiled bridge. It is not evidence about why the historical search chose the provider. |
| C3 | Same-representation counterpart to the imported `MC-D` bridge | blocked | None established | [U2] No drop-in counterpart on the audited path preserves the declaration's hypotheses and changes only the bridge's internal `D'/MC-D'` expression. Replacing/recompiling that imported declaration would change more than the consumer API application. |

**[I, U2]** No successful one-factor consumer-source control removes the
generic API from the imported specialized provider. C1 removes the top-level
`derivedTensor` abbreviation boundary, but cannot isolate the internal
`D'/MC-D'` choice. A minimal bridge-source counterfactual would have to be
constructed and checked separately; none is claimed here.

## Decision criteria and limits

**[A1-A4, R1-R5, O1]** Criteria 1-5 are answered at the granularity the
artifacts support: the exact original operands are `IsLeftDerivedFunctor₂`
types, D originates in source and adapter signatures, D' originates in the
imported bridge, `MC-D` is attached by D-level synthesis/compiled adapter,
`MC-D'` is fixed in the bridge, and the consumer declaration's expected-type
check brings the expressions together at the API level. Whether the
historical Kernel comparison reaches the nested generic provider remains
unobserved. The archived `Eq` root is separately
inventoried, not passed off as the original consumer event. **[C1, C2, U2]**
Criterion 6 has only partial intervention evidence: C1 eliminates the
top-level functor-head difference; no valid one-factor source change has been
shown to remove the generic provider nested inside the imported bridge.

There are two distinct comparisons:

```text
Original consumer: value : IsLeftDerivedFunctor₂(curriedTensor D[MC-D], ...)
                   expected IsLeftDerivedFunctor₂(derivedTensor A X, ...)
                   where derivedTensor's compiled body = curriedTensor D[MC-D]
                   and MC-D's compiled bridge contains D'[MC-D'].

Archived probe:     checked Eq D (tensor D[MC-D] K L) (tensor D[MC-D] K L)
                   stored  Eq D (tensor D[MC-D] K L) (tensor D'[MC-D'] K L).
```

This establishes **explicit source choice** of `derivedTensor` and the
adapter, an **imported signature/value** carrying `MC-D` and its embedded
generic bridge, and **D-level synthesis** of the specialized provider at the
current `derivedTensor`/statement sites. It does not establish a historical
fresh D' search at the consumer, or that the diagnostic equality was present
in that source. **[U1, U2]** The exact historical elaborator assignment
sequence and a minimal bridge-source replacement remain unobserved.

## Reproducibility and artifacts

**[R0]** Lean 4.33.1 source revision
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib
`0df444a360eaa60ab8c11cda51a86af692955474`, consumer
`bdab171985a5e6c6e44fc3920386b89fc5627ca3` were verified with Git;
the READY4.2 `lean --version` reports 4.33.1. The isolated consumer was a
Git archive of the pinned checkout plus a private copy of its `.lake`
directory. It was checked with the pinned READY4.2 `lake env` and the
matching `LD_LIBRARY_PATH`, one Lean invocation at a time, each under
`timeout 3600`. Disk use was 85-86%, below 90%. No shared checkout, kernel,
typeclass policy, or `u9w` file was changed; no commit or push was made.
No raw trace exceeded 2 GB.

The reduced directory `sdtapp/` contains exact probe sources, the archived
root source, source-site synthesis traces, declaration/value audits, the
original ten-binder boundary inventory, the diagnostic six-position inventory,
and compact raw application spines. `SHA256SUMS.txt` checks these files.
Full raw `ConstantInfo` snapshots exceeding 5 MB remain in isolated
scratch; only relevant raw subexpressions were copied to the repo. Every
reduced file is below 5 MB. `app-boundary-trace.out` was exploratory; only
its relevant D' reduction excerpt is retained because the broad trace did
not isolate a historical Meta event. The first `app-audit.lean` run failed
on its output
path, and the initial `app-decls.lean` run used two incorrect generated
declaration names; corrected runs succeeded. These failures did not affect
the retained measurements. C3 is blocked as stated above.
