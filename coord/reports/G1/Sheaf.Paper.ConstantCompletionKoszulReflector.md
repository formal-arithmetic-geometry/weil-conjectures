## What changed

Implemented `CategoryTheory.ConstantCompletion.koszul_quotient_reflector` with its original
signature. The proof identifies the kernels of the constant and completed residue maps
with the given finite generator ideal, constructs generating sections on every slice,
and applies `ringedKoszulCompletionReflector`. It then transports output completeness,
the Hom bijection, and the unit-isomorphism criterion through a unit-preserving natural
isomorphism. Private helpers reuse the already proved ideal-section constructions from
`ConstantCompletionCore`; no existing definition or statement was changed.

Added `Sheaf.Paper.ConstantCompletionKoszulQuotientComparison`, containing one smaller
comparison statement for an arbitrary supplied Koszul presentation. It asserts only the
natural isomorphism and its unit equation; it assumes neither reflector properties nor
existence of the presentation. The original theorem constructs its presentation using
the existing ringed reflector and proves all its remaining clauses in Lean. Updated
Steps 6 and 7 of the original umbrella node to match this reduction; its other components
and statement are unchanged.

The new statement was checked mathematically for the empty generator list (I=0, both
towers constant), I=top (both derived limits zero), the zero ring, empty site, and arbitrary
unbounded inputs. It imposes no product-exactness or finite-quotient perfection hypothesis.
The comparison is Stacks Tag 099M applied to the two coefficient sheaves; Tag 093M gives
the flat completed extension. Its complete proof plan and ownership node accompany it.

Validation: both delivery modules compile individually in import order through
`lcompile.py`; the comparison compiled in 2.7 seconds and the reflector in 6.4 seconds, with no warnings.
Final validation is performed by `deliver3.py`.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.ConstantCompletion.koszul_quotient_reflector`
(node `lem-weil-pbc-constant-completion-equivalence`) by decomposition. Its proof body is
complete and the item now has zero `sorry`s. The finite-kernel generator calculation,
completeness transport, both directions of the Hom bijection, and the unit criterion
are proved without additional holes.

Added one hole:
`CategoryTheory.ConstantCompletion.koszulQuotientComparison`, in the new module
`Sheaf.Paper.ConstantCompletionKoszulQuotientComparison`, node
`lem-weil-pbc-constant-koszul-quotient-comparison`. This is precisely the strict
Koszul/quotient model comparison, excluding the presentation existence and all
reflector clauses of the original item.

Counts: one original hole closed by decomposition, one strictly smaller hole added;
zero holes left in the item, one in the delivered packet. Net hole change is zero;
this is a decomposition, not a claim of a net hole closed.

## No longer needed

Removed these inherited proof imports from the item:

- `WeilConjectures.CategoryTheory.NatTransFromResolvingClass`
- `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `Mathlib.RingTheory.Ideal.Span`
- `Mathlib.RingTheory.Finiteness.Defs`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`
- `all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Mathlib.CategoryTheory.Adjunction.Whiskering`
- `Mathlib.CategoryTheory.Adjunction.Additive`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`

Their modules are not needed directly by the reflector transport proof. Some remain
transitive dependencies of `ConstantCompletionCore` or of the future comparison proof;
no claim is made that they can be withdrawn globally. All original public imports are
preserved, including the public Core import. The original node's direct proof edges to
`lem-weil-pbc-noetherian-koszul-augmentation-pro-zero` and
`lem-weil-pbc-flat-constant-tensor-pro-zero-cones` now pass through the comparison node;
these two mathematical dependencies remain needed. No module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The maintainer split the umbrella module into files, but its node still attaches the
whole declaration list to `ConstantCompletionCore`; the assigned theorem appears in
that list rather than in a node whose primary `lean.module` is the item. This delivery
preserves that attachment and updates only the corresponding proof steps.

The available pro-zero statements are at the strict complex/tensor level. Neither
provides the natural comparison between the chosen quotient presentation and an
arbitrary Koszul presentation, so the missing descent and normalization step is made
explicit as the smaller comparison theorem. Nearby `KoszulQuotientLimit` and completed
comparison statements concern schemes and different presentations; in particular
`CompletedConstantPresentationTransport` already reaches this item, so importing it
would close a cycle. None supplies an independent theorem on an arbitrary small site.
No mathematical defect in the assigned statement was found.

## New nodes

`lem-weil-pbc-constant-koszul-quotient-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-koszul-quotient-comparison.json`,
records the natural, unit-preserving comparison for any supplied Koszul presentation.
Its source is Stacks proetale.tex, Tag 099M, proof, together with sites-modules.tex,
Tag 093M. Its proof uses the existing Noetherian augmentation, flat constant tensor
pro-zero, strict derived-limit and resolving-class localization declarations. Actual
LeanFinder, Loogle, LeanSearch and Mathlib grep searches found ordinary adic-completion
results rather than this comparison. The blueprint search for "Koszul quotient
completion" had no exact match; the nearby scheme-specific nodes listed above were
read and do not have the required generality or independent import direction.
No change record is needed: existing signatures, definitions and public imports stay
unchanged, and no other existing Lean module is edited.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionKoszulQuotientComparison": "94311d5a89e8db8bab8d4ab4645d02790b9f5139", "Sheaf.Paper.ConstantCompletionKoszulReflector": "33649291f4ba29ee7e2bdf939165f63e6176f36e"}, "results": {"Sheaf.Paper.ConstantCompletionRestriction": {"hash": "e62ece3eab3637090570df090bafa5761b0a5ef5", "status": "OK"}}, "seconds": 215, "time": "2026-10-27T23:35:14+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
