## What changed

Replaced the sorry in
`WeilConjectures.IntegralFiniteExtension.u_existsUnique` by a complete Lean proof
from two strictly smaller statements. Form the finite morphism by composing quotient,
the extended source reduction, the counit-defined finiteU, and the inverse target
reduction. The coherence lemma makes this a compatible family. The already published
`sfIntegralScalarExtension_constructible` puts its source in the constructible category.
Apply morphism reconstruction, then cancel the target reduction isomorphisms to obtain
both the required squares and their uniqueness. No hypotheses or conclusions changed.

Moved the prerequisites from the item into the new
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels`, publicly re-exported by the item.
This prevents an import cycle: the new finite coherence theorem needs the fixed maps,
but the proof of u_existsUnique needs that theorem. Every original public declaration
keeps its qualified name, visibility and signature; every moved definition and structure
keeps its body. The three already proved completeness/existence theorems move verbatim
with their private helpers. No adopted WeilConjectures module changes.

New proof imports: `Sheaf.Paper.IntegralConstructibleReductionHom`,
`Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence`, and
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`.
The two new theorem modules have one named public theorem each. Their docstrings give
the source, proof in words and edge cases; neither chooses new data.

Remote lcompile of all four delivered modules succeeded with exit code 0. All 24 original
parsed declaration signatures agree with the delivered pair of item/models files;
all bodies other than u_existsUnique agree modulo trailing whitespace. The direct
consumers GeneralHomComparisonCocycles, VerdierHomChainComposition and
CoefDualFormulaScalarTranspose compiled unchanged against these sandbox outputs.
RationalVerdier hit the 60-second limit; profiling identifies its existing completionChain
proof term as expensive (kernel checking about 41 seconds). A separate baseline-only
compile, outside the sandbox Lean root, also hit the limit. RationalVerdier is held by B6;
no change is forced by our unchanged interface, so no unrelated adaptation is delivered.
RationalScalarTransposeCompatibility also compiled unchanged. CoefQbarVerdier hit the
60-second limit without an elaboration error. VerdierCoefficientRealization compiled
unchanged; CoefVerdierWeilEquivariance also hit the 60-second limit without an elaboration
error. SfPackageExceptionalCoherenceRealization compiled unchanged, completing six
successful consumer checks out of nine. The normal deliver3 compiler/probe provides
the final delivery validation. Diagnostic copies of consumers are not part of the delivery.

## Proved and sorry left

Original holes at the start of this session: 2.

Closed upper hole by decomposition:
`WeilConjectures.IntegralFiniteExtension.u_existsUnique`
(node `lem-coef-integral-finite-extension`). Its proof combines the named lower
statements with actual scalar constructibility and isomorphism cancellation.

Added holes: 2, both strictly simpler than that unique-map statement:

- `WeilConjectures.IntegralFiniteExtension.finiteDualizing_reduction_coherent`
  (node `lem-sf-integral-finite-dualizing-coherence`): only the finite transition square;
  it asserts no existence or uniqueness of an integral map.
- `WeilConjectures.integralConstructibleReductionHom`
  (node `lem-sf-integral-constructible-reduction-hom`): the general mapping-limit
  reconstruction step; it mentions no scalar field extension, dualizing object,
  finiteU, or counit-defined dualizing comparison.

Unchanged original hole:
`WeilConjectures.coef_integral_finite_extension`
(node `lem-coef-integral-finite-extension`).

Actual delivered textual sorry count: 3 (1 in the item, 2 in new modules, 0 in the
models module). This is one upper-hole decomposition into two lower holes, not a
claim of net proof progress; net holes closed minus added is -1. The earlier proofs
of completion_isIso, extension_complete and dualizingDatum_nonempty remain intact.

## No longer needed

No mathematical node or module is pruned. In particular no adopted upstream declaration
is removed. All dependencies of the untouched final theorem remain in its DAG plan.
The proof-dependency addition for u_existsUnique uses only the two new lemmas and the
existing scalar constructibility theorem. NormalizedDVRTowerEvaluation_full is not
imported: its statement gives lifting, with no uniqueness, so it cannot justify the
unique-map assertion here. IntegralSystemReductionFullyFaithful is not imported:
faithfulness there concerns coherent system maps rather than their separate evaluations.

The original four public imports and two private proof imports are located in the
models module and remain available with the same visibility through the public re-export.
They are not pruned dependencies. No unused proof import was added to the final proof.

## Where the brief, the DAG or earlier work was wrong

No statement error established. The live source already contained the earlier group's
three completed proofs; the historical five-hole review record was not the starting
hole count for this session. Separate finite reductions do not generally detect equality
of arbitrary derived tower maps: the new reconstruction statement retains constructible
finite-type hypotheses and its proof explicitly uses finiteness/Mittag-Leffler to remove
the Milnor kernel. The final theorem and its full blueprint route are left unchanged.
No new statement is merely u_existsUnique under a different name.

The unit record sk-prop-sf-biduality-general has no realized statement or step bindings
that this change bypasses. The new dependencies have no return path to their own nodes;
read-only dependency traversal checked all statement/proof dependencies. The supplied
brief overrides the standing page's second-reader requirement for dispatched workers;
no second reader was started or claimed.

## New nodes

`def-sf-integral-finite-extension-models` owns the relocated tensor, Hom, completion,
finite quotient and finite dualizing comparison prerequisites. It introduces no new
mathematical construction. The existing coherent DualizingDatum definition node is
repointed to its identical declaration in that module. The original theorem node
retains the declarations still in the item and gains the explicit reduction proof step.

`lem-sf-integral-finite-dualizing-coherence` is the finite counit square of blueprint
paragraphs 3-4, at every target level including intervening ramified levels. Its proof
uses quotient balancing, coherent dualizing reductions and the finite comparison's
counit/composition laws, without assuming the desired integral lift.

`lem-sf-integral-constructible-reduction-hom` is the mapping-limit argument needed for
existence and uniqueness. Its proof identifies normalized finite maps with compatible
sections of the mapping tower, kills the H-minus-one lim-one term using finite groups,
and obtains the asserted bijection. This isolates the exact missing uniqueness input.
The zero objects, empty scheme, first positive exponent, identity extension and equal
transition indices satisfy the statements without extra nonzero assumptions.

Change record: `coord/changes/Y7-integral-finite-extension-models.md` lists every transitive
consumer and holder. No consumer adaptation is necessary. Searches used launcher
LeanSearch, LeanFinder, Loogle, Mathlib grep, project rg and blueprint search; no existing
statement supplied either precise lower step.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
