## What changed

Reduced `WeilConjectures.IntegralAugmentedQuotient.augmentedQuotientTowers` to two
strictly smaller ordinary-module theorems. The cokernel theorem is in the new module
`Sheaf.Paper.IntegralConstantQuotientCokernel`. The insertion-unit transport is isolated in `Sheaf.Paper.IntegralCompletedInsertionUnit`.
The item retains every existing public
signature. The theta construction is definitionally the same composite, expressed
through a local generic construction to bound unfolding. Its proof constructs the source comparison from the published
completed/constant pullback comparison, constructs the completed tower comparison using
`stratumModuleReductionIso_exists`, and constructs the constant tower comparison using
`ordinaryReductionPullIso`. It uses the split insertion-unit lemma and proves insertion-linearity,
insertion-naturality, completed tensor-generator, beta-augmentation and theta-augmentation
identities explicitly. The common completed quotient is the constant quotient followed
by the existing beta; no second completed cokernel assertion is assumed.

Only proof imports changed. Some use `import all` to access existing private, proved
normalization helpers without copying their proofs or changing their owning modules.
No source-library module, target signature or consumer changes. The theta construction
change is recorded in `coord/changes/integral-augmented-theta-unfolding.md`.

## Proved and sorry left

The one original hole is closed syntactically:
`WeilConjectures.IntegralAugmentedQuotient.augmentedQuotientTowers`, node
`lem-sfb-integral-augmented-quotient-towers`. All its private proof helpers have complete
proofs. Both new statement modules compiled. The main module initially passed in 55.9 seconds
but timed out in the delivery recheck. After bounding the theta construction, its
profiled compile passed in 34.9 seconds (kernel checking 7.85 seconds and linting
9.86 seconds). The development profiling option was then removed. Two holes are added. First:
`WeilConjectures.IntegralAugmentedQuotient.constantQuotientCokernel`, node
`lem-sfb-integral-constant-quotient-cokernel`, in its own new module. This is a
decomposition (one hole closed, two added; net minus one), not a complete proof of all
underlying mathematics. Second: `WeilConjectures.IntegralAugmentedQuotient.completedInsertionUnit`,
node `lem-sfb-integral-completed-insertion-unit`. It concerns one section of an arbitrary
module and its transport to the canonical adjunction unit, with no quotient, tower,
complex or balancing assertion. Existing imported sorry theorems retain their own nodes.
The cokernel lemma treats one arbitrary constant module at one level; it contains none of
the completed-scalar balancing, pullback comparisons, strict transition construction,
complex quantification or theta equations of the original item.

The cokernel helper was checked mathematically on N=0, a module killed by the uniformizer,
n=0 (positive exponent one), the empty scheme and arbitrary non-flat modules. The
argument is a sheaf cokernel construction and never substitutes an unsupported
sectionwise quotient assertion. The full natural-language proof is in its docstring.

## No longer needed

Removed the proof imports `Sheaf.CategoryTheory.FiniteTypeConstantExact` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` from the item. The first
remains a planned dependency of the new constant-cokernel lemma; the second supplies no
construction used by this ordinary natural-transformation proof. Existing public
imports are retained verbatim.

The item does not need `lem-sfb-integral-coefficient-square-normalization` directly:
the already published original-site comparisons give the normalized module and tower
maps without transporting from the internal-module presentation. It also does not
need `lem-weil-pbc-finite-type-constant-exact`, `def-pur-sheaf-tensor-product`,
`def-pc-sheaf-restrict-scalars` or `def-pc-tensor-complex-sheaves` as separate proof
steps in this module. Constant exactness and tensor construction remain relevant to
the new helper; restriction and complexes remain in the unchanged statement interface.
The temporary proof import `Sheaf.Paper.FiniteQuotientOrdinaryComparison` was also
removed: the completed projection surjectivity helper already exists in
`CompletedPullbackReduction`. No whole module is withdrawn, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan's internal coefficient-square interface is unnecessary for this
proof. The original-site library already states the augmented completed tower
comparison for every morphism, despite the name `stratumModuleReductionIso_exists`;
it has no stratum hypothesis. Its uniqueness-normalized augmentation equation,
together with finite completed projection surjectivity, implies the required full
generator formula. The constant tower comparison and its unit equation also already
exist. The updated DAG records these actual dependencies rather than re-proving them.
The unit route in `sk-lem-int-tensor` is preserved (its realized lists are empty).

The following existing results from other units are used as tools, and need the
maintainer's route review: `lem-weil-pbc-stratum-completion-unit-restriction`
(only its ordinary arbitrary-morphism comparison),
`lem-weil-pbc-strict-tower-exchange-mate-normalization`
(ordinary scalar restriction comparison), `def-sp-constant-reduction-models`
(ordinary tower pullback and unit), and the proved normalization helpers exposed by
`CompletedPullbackReduction` and
`ProEtaleRingSheafChangeAdjunction`. These do not reach this item; no import cycle or
DAG cycle is introduced. Their use avoids new statements for already available facts.
No maintainer `tool_uses` approval is added by this delivery.

The broad existing DAG contains a pre-existing cycle involving
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. A separate traversal of every
new item proof dependency confirms none returns to this item. This packet does not
modify that unrelated cycle.

## New nodes

`lem-sfb-integral-constant-quotient-cokernel` isolates step 2's constant-module
principal quotient with its actual augmentation. Source: current blueprint
`det-lem-int-tensor-pullback`, comparison paragraph; Stacks `sites-modules.tex`,
`lemma-constant-exact` and `section-tensor-product`. The node and docstring give the
local balanced pairing and its inverse, explain lift independence and gluing, and
check the quotient projection normalization. LeanSearch, Loogle, LeanFinder and grep
were run through `msearch.py` and recorded in the sandbox search log. Algebraic
tensor quotient and categorical cokernel lemmas were found, but none states this
prescribed sheaf-module augmentation. Blueprint searches for quotient/tensor
quotient found no duplicate of this smaller normalized assertion. No existing statement or public import changed; the definitionally equal theta
construction is recorded in `coord/changes/integral-augmented-theta-unfolding.md`. Proof-local irreducibility
attributes bound unfolding of existing coefficient and derived-category constructions.

`lem-sfb-integral-completed-insertion-unit` isolates the scalar-insertion transport
calculation. Its statement takes the published functor equality explicitly and
compares its section map with the canonical module adjunction unit. The docstring
explains the object equality comparison, the sheafified tensor-unit formula, and
identity restriction. Zero modules and empty site objects satisfy the same formula.
This was split after several compile-guided attempts found the scalar-extension
transport did not simplify definitionally; it is a separate step rather than an
alternate name for any clause involving the original towers. It has its own
LeanSearch, Loogle and grep records. No definition contains a hole.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
