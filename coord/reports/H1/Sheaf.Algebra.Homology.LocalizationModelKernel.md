## What changed

The existing declaration `RingTensorCohomology.localizationModelMap_kernel` has
exactly its original signature and docstring. Its proof now computes the
canonical map on an ordinary balanced A-complex, applies the proved ordinary
cohomology localization kernel criterion, and transports the annihilation
equation through an A-linear isomorphism.

Added two new modules:

- `Sheaf.Algebra.Homology.BaseTensorUnitCohomologyModel`: the balanced-complex
  computation and its commuting equation. This statement assumes no localization
  or flatness of Aq and asserts no kernel criterion.
- `Sheaf.Algebra.Homology.ComplexLocalizationUnitKernel`: the fully proved
  denominator criterion for the ordinary cohomology extension unit.

Both are imported privately by the item's module: they are proof dependencies.
The original public imports are retained for its statement. No definition or
existing statement changes, and no change record is needed.

## Proved and sorry left

Original hole closed:
`RingTensorCohomology.localizationModelMap_kernel`
(node `lem-pc-first-localization-cohomology-kernel`).

New hole added and left:
`RingTensorCohomology.exists_baseTensorUnitCohomologyModel`
(node `new-lem-pc-base-tensor-unit-cohomology-model`). It is exactly `:= by sorry`,
has a complete construction/comparison proof in its docstring, and lives in its
own module. The existential witnesses are used only inside the kernel proof;
no data definition chooses a witness of this unproved existence theorem.

New theorem fully proved:
`RingTensorCohomology.complexLocalizationUnit_kernel`
(node `new-lem-pc-complex-localization-unit-kernel`). Mathlib's exact extension
and `ShortComplex.homologyMap_mapNatTrans` conjugate its map to the ordinary
module unit; `IsLocalization.tensorProduct_isLocalizedModule` and
`IsLocalizedModule.exists_of_eq` give the denominator.

This closes one original hole and adds one new hole: net zero, a decomposition,
not a completed proof of the item without assumptions. The ordinary criterion
is genuinely proved and no longer part of the remaining task. The item and
balanced computation have axioms `propext`, `Classical.choice`, `Quot.sound`,
`sorryAx`; the ordinary criterion has only the three permitted standard axioms.

## No longer needed

No original import or reachable module is pruned. The kernel node's old direct
proof dependencies are all replaced by the two new nodes:

- `def-pc-base-derived-tensor-cohomology-model`
- `lem-pc-balanced-derived-tensor-model`
- `lem-pc-derived-tensor-action-naturality`
- `lem-pc-first-localization-cohomology-semilinear`
- `lem-weil-pbc-localization-flat`
- `lem-weil-pbc-localization-module-exact`
- `lem-weil-pbc-localization-tensor-product`

The model definition and map remain statement dependencies. The balanced model
and action naturality remain below the computation node; flatness, exactness,
and tensor localization remain below the ordinary criterion node. Thus these
are changes of direct proof dependencies, not claims of pruning their modules
from the targets' closure.

The first worker's new `LocalizationModelIsLocalized` module and its unlanded
node were removed: that stronger unproved localization theorem retained the
whole kernel problem. The unchanged copy of `LocalizationModelSemilinear` was
removed from the delivery. The spurious proof-environment change record was
removed; local lets do not alter an existing signature.

## Where the brief, the DAG or earlier work was wrong

The earlier helper `localizationModelMap_isLocalized` asserted the full module
localization property, including the kernel claim being addressed and extra
surjectivity/invertibility properties. Applying its equality criterion did not
separate off a strictly smaller part of the argument. The second reading
replaced it with the independent balanced computation, valid even for arbitrary
Aq, and proved the ordinary-complex denominator argument in Lean. The original
DAG route is retained: balanced computation, ordinary localization, then model
transport. Its kernel node now describes the actual two-step proof.

## New nodes

`new-lem-pc-base-tensor-unit-cohomology-model` records the remaining balanced
computation and universal-counit comparison, with source, proof, statement and
proof dependencies, exact Lean signature, searches, creation and blueprint
metadata. Sources checked: [Stacks 064L](https://stacks.math.columbia.edu/tag/064L)
and [Stacks 06Y6](https://stacks.math.columbia.edu/tag/06Y6).

`new-lem-pc-complex-localization-unit-kernel` records the proved ordinary
cohomology criterion and its exact-functor/module-localization proof. Sources
checked: [Stacks 00CS](https://stacks.math.columbia.edu/tag/00CS) and
[Stacks 00DK](https://stacks.math.columbia.edu/tag/00DK).

There are no change records and no forced adaptations.

## Second reading by H1

1. Compared the item's module against the read-only repository with `diff` and
   the declaration parser. Verdict: no existing signature, docstring, definition,
   universe, hypothesis or conclusion changed. The copied semilinearity file
   was identical and is omitted. No other existing module is delivered.
2. Compiled all three delivered modules in import order with `lcompile.py`.
   Verdict: no errors or warnings; one named theorem has `sorry`, exactly as
   listed above. Scanned for forbidden trust declarations and data holes; none
   exist. Compiled scratch copies with `#print axioms` for all three theorems.
   The ordinary-complex theorem has standard axioms only; the remaining helper
   and kernel proof additionally have the declared `sorryAx` dependency.
3. Tested the new statements mathematically at zero complex, zero ring,
   identity extension, S={1}, and 0 in S; the computation also works for
   nonflat Aq (it uses a K-flat resolution of B over R, not of Q over R).
   Verdict: both are true with no extra flatness or boundedness assumptions.
   The only remaining hole is a computation theorem with no S or kernel claim;
   the ordinary kernel step is separate and proved. Its witnesses are not used
   in any data definition. Read the balanced model, universal model definition,
   scalar compatibility and adjacent localization modules. Independent
   LeanFinder, Loogle and grep searches (recorded in searches.jsonl and nodes)
   found component lemmas but no duplicate of the new computation theorem or
   ordinary-complex unit criterion.
4. Inspected the proof from the target downward, used Mathlib's exact-functor
   naturality instead of leaving ordinary cohomology localization unproved, and
   reviewed all imports. Verdict: the original unit route is retained. The unit
   `sk-thm-picard-semicon` has empty realized lists; the item is below that level
   and no unit step is bypassed. Every old direct proof dependency replaced is
   listed under No longer needed, with no false claim of module pruning.
5. Read the original and new nodes against the actual Lean signatures and
   proof. Verdict: the kernel node now points to the computation and ordinary
   criterion; the new nodes record their respective real arguments, sources,
   metadata and searches. Existing node changes are confined to proof,
   proof_deps and proof_origin.

Changes by this second reader: removed the stronger unproved localization
helper, its node, the unchanged semilinearity copy and the unnecessary change
record; introduced the balanced computation and ordinary-complex criterion;
fully proved the latter; rewrote the kernel reduction; synchronized all nodes
and the report. One original hole closed and one new hole left, net zero.

Preflight search repair: attempted LeanSearch separately for both new nodes;
the service returned Internal Server Error. Both unavailable attempts are
recorded without a search verdict. LeanFinder, Loogle and grep supplied the
available independent searches.
