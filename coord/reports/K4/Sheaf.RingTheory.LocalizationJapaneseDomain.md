## What changed

Proved `localization_isN1_isN2` in
`lean/Sheaf/RingTheory/LocalizationJapaneseDomain.lean`, with its original signature,
universes, visibility, and public imports unchanged. Added proof-only imports of
`Mathlib.RingTheory.Localization.Integral`,
`Mathlib.RingTheory.Localization.Finiteness`, and
`Mathlib.RingTheory.Localization.LocalizationLocalization`.

The canonical algebra structure is explicitly constructed with
`IsLocalization.localizationAlgebraOfSubmonoidLe`. Mathlib supplies the domain,
scalar tower, unchanged fraction field, and injectivity. The fraction formula follows
from `IsLocalization.mk'_spec` and the nonzero denominator.

The fully proved private helper `finite_integralClosure_localization` handles steps
2 and 3 of the node: the inclusion of integral closures uses `IsIntegral.tower_top`;
`IsLocalization.of_le_isUnit` identifies the extension field with its localization;
`IsLocalization.integralClosure` (the node's Mathlib leaf) identifies the localized
integral closure; `Module.Finite.of_isLocalization` transports finite generation.
The helper is applied to `K` for N-1 and to an arbitrary finite extension `L/K` for
N-2. In the latter case, the `R`-algebra on `L` is explicitly the composite through
`K`, and the scalar tower through `Localization S` is proved from the two towers.
No data is selected from an unproved existence theorem.

The original four-step DAG plan and all five proof dependencies are retained.
There is no route change, new node, or statement/definition change.
The unit record `dag/units/sk-thm-p1.json` is unchanged; this node is below the
unit's realized statement and steps.

The local source TeX is absent on this machine, so the cited sources were read at
[Stacks Tag 032G](https://stacks.math.columbia.edu/tag/032G) and
[Stacks Tag 0307](https://stacks.math.columbia.edu/tag/0307).
Short-route searches used `msearch.py` LeanFinder, Loogle, and grep, plus `rg` of the
project and pinned Mathlib. No N-1/N-2 theorem was found; the required localization,
integral-closure, and finite-module ingredients are proved in Mathlib.
The file compiles cleanly with `lcompile.py`; every line is at most 100 characters.

## Proved and sorry left

Closed: `localization_isN1_isN2`
(node `lem-weil-pbc-localization-n2-domain`), the only original hole.
The private helper `finite_integralClosure_localization` is also completely proved.
Remaining holes in the item: none. Added holes: none. Split-off statements: none.
This is a full proof from Mathlib, not a decomposition into unproved statements.

## No longer needed

None. No original import or proof-dependency node was removed.
The proof still uses the notions from `def-weil-finitely-generated-module`,
`def-weil-pbc-integral-closure`, `def-weil-pbc-japanese-domain`, and
`def-weil-pbc-module-localization`, and the Mathlib leaf
`lem-weil-pbc-integral-closure-commutes-localization`.
All three added proof-only imports supply declarations used in the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or unusable statement was found.
The DAG plan is directly expressible with Mathlib's existing interfaces.
No forced adaptations or interface changes were needed.

## Second reading by K4

1. PASS: Compared the delivered module with the repository using `diff` and checked
   the existing theorem signature byte for byte. Its universes, hypotheses, conclusion,
   visibility, docstring, and original public import are unchanged. No definition or
   existing statement changed; no change record is needed.
2. PASS: Independently compiled the module with `lcompile.py`, without errors or
   warnings. Searched for forbidden declarations and holes: none. A scratch copy with
   `#print axioms` for both `localization_isN1_isN2` and the private helper
   `finite_integralClosure_localization` reports exactly `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`. The algebra structures are explicit canonical
   constructions; no arbitrary witness is selected from an unproved theorem.
3. PASS: No split-off statements or new holes. Reviewed the proved private helper:
   integrality ascends along the base-ring map, the denominators already act by units,
   integral closure commutes with localization, and finite generation localizes.
   The trivial multiplicative set `{1}`, localization at all nonzero elements, and
   the case where the original ring is already a field all satisfy this argument.
   There is no extra Noetherian, separability, or finite-extension requirement in the
   helper. The N-2 application uses precisely the finite extensions in its definition.
4. PASS: Read `JapaneseDomain.lean`, searched the project with `rg`, and independently
   searched with `msearch.py grep` using the query
   `integralClosure localization finite module`. Read Mathlib's
   `IsLocalization.integralClosure`, `Module.Finite.of_isLocalization`, and
   `IsFractionRing.isFractionRing_of_isLocalization`. No shorter existing Japanese-domain
   theorem was found. Each added plain import provides declarations directly used by
   the proof; the original public import supplies the signature's definitions.
   All five old proof dependencies remain used, so `## No longer needed` is complete.
   The unit `sk-thm-p1` and its realized route are preserved.
5. PASS: Checked the item's node, all five dependency records, the Mathlib leaf, and
   the unit's `realized` fields. The unchanged four-step proof, `proof_deps`, and
   document `proof_origin` agree with the Lean proof: canonical fraction map and
   fraction field; localization of integral closure in the unchanged extension field;
   finite generation; the N-1 and N-2 applications. No node changes are necessary.

Changes by the second reader: appended this review only. No Lean repair was needed.
