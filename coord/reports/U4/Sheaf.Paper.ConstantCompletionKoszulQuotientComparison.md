## What changed

Replaced the body of `CategoryTheory.ConstantCompletion.koszulQuotientComparison`
with a resolving-class comparison and a complete unit-normalization argument.
The existing signature and public import of `ConstantCompletionCore` are preserved.
The proof compares the two total right-derived limits by their universal property,
compares their computations on flat-term K-flat complexes, extends the comparison
using the existing proved resolving-class lemmas, and transports the unit equation
from those models to all complexes and then all derived objects. Three proved
private helpers establish naturality of the strict tensor unit, its ordinary-limit
map, and the resulting `unitOnComplex`. A fourth proved private helper performs
the resolving comparison in abstract categories, avoiding repeated kernel
unfolding of the concrete sheaf and chosen-localization definitions.

Added two modules, one for the natural normalized strict augmentation and one for
its invertibility after total derived inverse limit. The first also defines the
explicit normalization predicate `KoszulQuotientAugmentationLaws`. It contains
only equations, with no chosen data or proof hole. Both new theorems are statements
of strict-complex steps and do not involve the supplied Koszul presentation or the
chosen derived quotient presentation. The augmentation theorem does not assume
Noetherianity; the invertibility theorem does. The original DAG node now records
this proof route.

The proof imports `ConstantKoszulQuotientAugmentationIsIso`, the private proved API
of `ConstantCompletionCore` via `import all`, and `CochainTensorUniverses` for the
existing total-tensor monoidal structure and colimit instances. No other existing
module or node is changed. All work and compilation use the assigned sandbox and
`lcompile.py`. The final import-order compile passed without warnings:
augmentation 6.2 s, invertibility 3.0 s, assigned comparison 36.4 s.
The modified dependency closure has no DAG cycle.

The proof uses `lem-sc-nattrans-from-resolving-class` as a general categorical
tool, through the existing proved `resolving_comparison_iso` helper in Core.
It extends transformations from resolving models; it does not replace any
proper-base-change unit step. The unit has no separate statement providing
this generic natural-transformation extension. No maintainer tool approval
field is added or changed.

## Proved and sorry left

Closed the original body hole in
`CategoryTheory.ConstantCompletion.koszulQuotientComparison` by decomposition.
The assigned module has zero remaining `sorry`s. All four private helpers have
complete proofs.

Added exactly two named theorem holes:

- `CategoryTheory.ConstantCompletion.koszulQuotientAugmentation`, in
  `Sheaf.Paper.ConstantKoszulQuotientAugmentation`, node
  `lem-u4-constant-koszul-quotient-augmentation`.
- `CategoryTheory.ConstantCompletion.koszulQuotientAugmentation_isIso`, in
  `Sheaf.Paper.ConstantKoszulQuotientAugmentationIsIso`, node
  `lem-u4-constant-koszul-quotient-augmentation-is-iso`.

Thus one upper hole is closed and two lower holes are added: this is a
decomposition, with net hole count -1, not a claim of a completed mathematical
proof. Every new hole is exactly a public named theorem with its source, full
proof in words, and its own module and node. No definitions contain holes.

The first obligation constructs a natural map on strict complexes and proves its
coordinate and strict unit formulas. The second proves invertibility of its
localized strict-limit map on a single flat-term K-flat model. The completed
assembly proves the natural comparison for arbitrary presentations and every
derived object from these strictly smaller steps.

Checked edge cases in the statements and proof plans: the empty generating list
forces I=0; its augmentation is the coefficient quotient of the empty tensor,
and its cones are acyclic. For the zero ring all module terms vanish. Neither
statement assumes exact countable products, finite quotient perfection,
completeness, or a bound on P.

## No longer needed

No original import was removed, and no module is withdrawn or globally pruned.
The original public import of `ConstantCompletionCore` supplies all objects in
the signature and remains necessary.

The assigned module no longer directly uses the planned
`lem-pur-left-derived-from-kflat-class`: the chosen quotient presentation already
exists, and the existing resolving-comparison API directly extends the comparison
on models. The parent DAG proof dependency on that theorem is removed. This is
not a claim that its source module can be deleted: `ConstantCompletionCore` still
imports it for other constructions.

The Noetherian augmentation, constant section properties, sectionwise adic limit,
flat-constant tensor/cone theorem, and strict-limit theorem remain necessary in the
new invertibility node. Their dependencies have moved there, not been pruned.
The strict ringed Koszul system remains necessary in the augmentation node.

The inspected scheme-specific `KoszulQuotientTensorAugmentation`,
`KoszulQuotientConeIsIso`, and `CompletedKoszul*` comparisons do not replace these
arbitrary-site statements. They are not imported; no claim is made that their
other consumers no longer need them.

## Where the brief, the DAG or earlier work was wrong

The current server queue identifies this as a one-hole proof task, not a returned
zero-hole repair, and supplies no build-error file for it. There is no assigned
interface defect to repair.

The original plan correctly identifies the argument but does not provide the
natural strict augmentation in the actual dual tensor model, nor a theorem
matching its normalized map with the flat-constant cone comparison. The existing
augmentation theorem concerns exterior complexes of ordinary modules; the
scheme-specific wrappers have different coefficient categories and cannot be
specialized to an arbitrary small site. These two missing strict-complex steps
are now stated explicitly. All presentation/descent and unit glue is written in
Lean, rather than replacing the original theorem with an equivalent existential
comparison under a new name.

## New nodes

`lem-u4-constant-koszul-quotient-augmentation` states the normalized natural strict
augmentation. It has weaker hypotheses than the parent and concludes strict
chain-map and summand identities, with no derived-completion isomorphism. Its
source is Stacks 099M and the ordered tensor description of Koszul complexes.

`lem-u4-constant-koszul-quotient-augmentation-is-iso` states invertibility of the
strict derived-limit map on a flat-term K-flat model, for a supplied normalized
augmentation. Its source is Stacks 099M and 093M and the existing Noetherian
pro-zero augmentation theorem. Neither new theorem contains any of the arbitrary
presentation comparison or resolving-class descent which the assigned proof
now performs. Three kinds of recorded Mathlib searches were performed for each.
No change record is required: no existing interface is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionKoszulQuotientComparison": "a98b9f41b6b39169b3d323a0856f3eb048867305", "Sheaf.Paper.ConstantKoszulQuotientAugmentation": "9f3ab8bdd18b1bfec54a487af397d68f571d7aef", "Sheaf.Paper.ConstantKoszulQuotientAugmentationIsIso": "baca0f4d7705f42e1ccfa1f30d594e49ce4b257b"}, "results": {"Sheaf.Paper.ConstantCompletionKoszulReflector": {"hash": "33649291f4ba29ee7e2bdf939165f63e6176f36e", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T10:35:17+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
