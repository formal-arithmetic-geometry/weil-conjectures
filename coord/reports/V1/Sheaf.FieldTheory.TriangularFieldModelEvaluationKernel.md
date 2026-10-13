## What changed

Replaced the sorry in `FieldTheory.exists_triangularFieldModel_evaluation_kernel`
with a complete Lean proof from two strictly partial statements in new modules:
`Sheaf.FieldTheory.TriangularFieldModelData` and
`Sheaf.FieldTheory.TriangularFieldModelNormalForm`. The first supplies relations,
degrees, evaluation vanishing, and independent bounded products; it asserts no
kernel equality. The second supplies quotient coordinates by monic division; it
requires no independence or algebraicity of the generators. The assigned module
uses linear independence to force zero coordinates, coordinate injectivity to
force zero quotient classes, and generator vanishing for the other inclusion.
Existing declaration signatures are unchanged. The two new Sheaf imports are proof-only. The second reader removed the target's
proof-only public quotient-operations import and reduced the new modules' imports.
All three modules compile with lcompile.py.

## Proved and sorry left

Closed: `FieldTheory.exists_triangularFieldModel_evaluation_kernel`
(node `lem-weil-pbc-triangular-field-model-evaluation-kernel`). This is a
decomposition, not an axiom-free completion: one original hole is replaced by two
strictly partial holes, for net holes closed minus added = -1.

Added and left exactly as named public theorems with `:= by sorry`:

- `FieldTheory.exists_triangularFieldModel_data`
  (`lem-weil-pbc-triangular-field-model-data`).
- `FieldTheory.triangularFieldModel_normal_form`
  (`lem-weil-pbc-triangular-field-model-normal-form`).

There are no sorries in the assigned module and no new definitions.

## No longer needed

Removed the original direct public import
`Mathlib.RingTheory.Ideal.Quotient.Operations` from the target. Quotient-zero
membership is available through the normal-form module's public quotient-basic
import; no separate quotient-operations import is needed. The target's unchanged
sole direct importer `Sheaf.FieldTheory.TriangularFieldModelPresentation` compiles
against the delivered modules.

In the new data module, removed the unnecessary
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` import. In the new normal-form
module, replaced the transcendence-basis import by
`Mathlib.RingTheory.AlgebraicIndependent.Defs`, replaced adjoin-basic by
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, replaced quotient-operations
by `Mathlib.RingTheory.Ideal.Quotient.Basic`, and removed
`Mathlib.LinearAlgebra.LinearIndependent.Defs`.

The old proof dependencies no longer directly used by the target are:
`def-weil-pbc-transcendence-basis`, `def-weil-algebraic-element`,
`lem-weil-pbc-minimal-polynomial-quotient-field-iso`,
`lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-tower-product-basis`,
`def-weil-pbc-mv-polynomial-ring`, `lem-weil-pbc-polynomial-ring-domain`,
`lem-weil-pbc-localization-away-polynomial-quotient`,
`def-weil-ring-localization-away`, and `def-weil-pbc-free-module`.
They remain ingredients of the two split-off nodes. No mathematical ingredient
or globally unreachable library module is claimed pruned. The unit route stays.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed interface was found. The DAG labelled the final
injectivity glue elementary, but it requires a usable normal-form coordinate
interface, now stated explicitly and used in Lean. Earlier proof dependencies
are ingredients, not a ready-made triangular quotient theorem. The local Stacks
checkout is absent; read Tags 07BV and 08JZ online as the existing node did.
Edge cases checked mathematically: m=0 gives a singleton product and localization
alone; d=0 gives k(x)=k; repeated generators have degree one; inseparability does
not change monic division. In the normal-form theorem, any zero degree would
force a monic constant relation one, contradicting its vanishing in K.

## New nodes

`lem-weil-pbc-triangular-field-model-data` constructs the relations and independent
bounded evaluations using steps 1–4 of the original argument. Its module is
`Sheaf.FieldTheory.TriangularFieldModelData`.

`lem-weil-pbc-triangular-field-model-normal-form` constructs injective quotient
coordinates and their evaluation formula using localization and successive monic
quotients (steps 5–6). Its module is `Sheaf.FieldTheory.TriangularFieldModelNormalForm`.
Neither node restates the target. Each has its own complete source-based proof in
words, Mathlib searches, edge-case analysis, and unchanged chapter/unit routing.
Change record: `coord/changes/TriangularFieldModelEvaluationKernel-imports.md`.
No forced adaptations are needed.

## Second reading by V1

1. Compared every delivered module with the repository. Only the assigned module
   already exists; its entire theorem signature is byte-for-byte unchanged.
   No definition or existing declaration visibility changed. The two new modules
   contain only theorem statements. The public-import removal has the change record named above. Verdict: pass.
2. Compiled all three files locally. Scratch copies with `#print axioms` show
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for each of the
   three declarations. The latter is expected from the two explicitly reported
   open lemmas. The target proof has no sorry; each new sorry is precisely the
   body of its named public theorem. No forbidden declarations, attributes or
   hollow definitions occur. All arbitrary witnesses are used inside proofs of
   propositions, never to define data. Verdict: pass as a decomposition.
3. Read both complete proof docstrings and nodes against
   [Stacks 07BV](https://stacks.math.columbia.edu/tag/07BV) and
   [Stacks 08JZ](https://stacks.math.columbia.edu/tag/08JZ).
   The data theorem supplies independent evaluated bounded products, without
   a kernel assertion; normal form supplies coordinates for arbitrary monic
   triangular relations, without requiring independence of their evaluations.
   These are strictly separate parts of the original argument. Empty m gives
   the singleton product and one localization coordinate; d=0 gives k as the
   base field; repetitions have degree one; inseparability changes nothing.
   Degree-zero monic relations equal one and contradict evaluation vanishing.
   As an additional check of normal form, d=0, m=1, h=1, p=Z^2 and b=0 gives
   k[Z]/(Z^2) with two injective coordinates despite noninjective evaluation.
   Fresh leanfinder, loogle and grep searches used different queries, including
   successive extensions and localization presentations, and local searches
   covered Sheaf and upstream FieldTheory. Found power bases, tower bases and
   the localization isomorphism, but no theorem of either combined assertion.
   Neither split-off theorem can be closed in a few minutes: both still require
   the finite tower construction and variable/quotient identifications.
   Verdict: true, useful, strictly partial; two holes remain.
4. Read the reduction from the top. Vanishing gives one ideal inclusion;
   independence kills the coordinates in the other inclusion, and injectivity
   plus quotient-zero membership completes it. No shorter complete replacement
   was found. Trimmed imports as listed above and compiled the unchanged direct
   importer against the new set. The old dependencies are all accounted for in
   `No longer needed`; they are used below the new nodes. Read sk-thm-p1's
   `realized` statement and all four step lists: this reduction changes none
   and bypasses no unit. Verdict: pass after import repair.
5. Checked every node's verbatim Lean statement against its actual declaration,
   and checked that proof_deps equals the union of proof-step uses. The target's
   three steps follow the actual Lean reduction; the split nodes carry their
   source, full argument, searches, created/blueprint/Lean records and original
   chapter/unit. Verdict: pass. Added the independent loogle search to each
   new node.

Second-reading changes: removed the target's public proof-only quotient import;
reduced the two new modules' imports; removed an extra blank line; completed the
old-dependency accounting and recorded independent searches. No theorem statement
or proof body changed. One original hole is closed, two holes are added: this is
an honest decomposition with net -1, not an axiom-free proof of the target.
