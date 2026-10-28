## What changed

Marked `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_resolution`
`STATEMENT-DISPUTED`. Its signature and existing proof hole are unchanged. The module now
also proves `native_weil_tensor_ringed_kflat_resolution_obstruction`: on every nonempty X,
the exact conjunction asserted by the assigned theorem is false, for every T in its scope.
This is a refutation delivery, not a purported proof of the false statement.

Added `Sheaf.Algebra.Homology.QuasiIsoFractionObstruction`, proving
`CochainComplex.acyclic_of_quasiIso_hasRightCalculusOfFractions` for every abelian category.
Its proof uses the degreewise split monomorphism K → Cone(id_K), the acyclicity of that
cone, and only the strict right-cancellation axiom. A zero quasi-isomorphism into K
would result, forcing every homology object of K to vanish. The native specialization
applies this to the constant coefficient sheaf in degree zero. The existing nonzero
constant-sheaf theorem supplies the contradiction when X is nonempty.

Added only proved theorems, their two node records, and the change record
`coord/changes/Q2-native-weil-kflat-fraction-obstruction.md`. No existing module besides
the assigned item is changed. The unit route is untouched.

Validation: the generic obstruction compiled in 2.9 s and the final item in 4.7 s,
with no warnings. The sole direct importer compiled unchanged against these files in 5.8 s. Its temporary
sandbox source copy was then removed, so no stale importer is delivered.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.

Proved:

- `CochainComplex.acyclic_of_quasiIso_hasRightCalculusOfFractions`
  (`lem-sf-cochain-quasiiso-fraction-obstruction`).
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_resolution_obstruction`
  (`lem-sf-native-weil-tensor-ringed-kflat-resolution-obstruction`).

The sole remaining `sorry` is the original, now disputed declaration
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_resolution`
(`lem-sf-native-weil-tensor-ringed-kflat-resolution`). It is not moved or weakened.
The refutation never invokes that declaration or assumes its statement.

## No longer needed

Removed three redundant private imports from the item:
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Mathlib.CategoryTheory.Localization.Construction`, and
`Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.
The existing public bridge import and the new proof imports provide the required API.

No nodes or modules are withdrawn or claimed pruned. In particular the item's parent
still cites it. The strict complex-level fraction-calculus step is mathematically
impossible; further splitting of that step would only propagate a false obligation.
The ringed K-flat replacement part remains a legitimate separate problem for the
actual normalized tensor. This delivery adds no such replacement obligation.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the first conjunct asks for a strict right calculus of fractions on
complexes themselves. Given a complex K, put C = Cone(id_K) and let i : K → C be its
canonical inclusion. C is acyclic and i is monic. The zero endomorphism of C is a
quasi-isomorphism and equalizes i and zero. Right fraction cancellation would therefore
produce a quasi-isomorphism t : Z → K with t ≫ i = 0. Monicity gives t = 0, so all
homology objects of K vanish. Taking K to be the native constant sheaf in degree zero
contradicts the nonzero constant coefficient sheaf on any nonempty X. Empty schemes
are explicitly excluded only from the refutation; the general cone obstruction also
covers zero categories and acyclic K without asserting a contradiction there.

The node's proposed transport of Ore/cancellation witnesses from the homotopy quotient
to complexes is invalid: equality of homotopy classes cannot supply strict cancellation.
Mathlib's actual instance in `DerivedCategory/Fractions.lean:38` is for
`HomotopyCategory.quasiIso`, as all three required searches confirmed. The caller
`NativeWeilTensorRingedKFlatLocalizationEquivalence` currently takes `.1` of the disputed
package and feeds it to `rightFractionDenseSubcategory`; that proof route consequently
needs repair at the homotopy-category level. Merely removing the conjunct would not
repair the caller, so this packet preserves the existing signature and delivers the
formal obstruction for the independent reader rather than an incompatible replacement.

[Stacks 014D](https://stacks.math.columbia.edu/tag/014D) gives the cone construction and
its termwise split inclusion; [Stacks 04VC](https://stacks.math.columbia.edu/tag/04VC)
gives the cancellation axiom used here. [Stacks 06YS](https://stacks.math.columbia.edu/tag/06YS)
proves K-flat replacement for the tensor on a ringed site; it does not assert the false
strict calculus or a K-flat replacement theorem for an arbitrary additive bifunctor T.
The present statement also lacks the native bridge and adjunction needed to identify
T with the ringed tensor. This is a separate missing justification, not needed for the
refutation.

## New nodes

`lem-sf-cochain-quasiiso-fraction-obstruction` records the fully proved generic cone
obstruction, using the existing closed source lemma `lem-pur-quasi-iso-cone-acyclic`.
It introduces no proof hole and is used by the native refutation.

`lem-sf-native-weil-tensor-ringed-kflat-resolution-obstruction` records the fully proved
negation of the assigned conjunction on nonempty schemes. The argument uses the native
constant sheaf, its single-complex homology, and the existing nonzero ordinary constant
sheaf. It introduces no proof hole and certifies the dispute in the item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.QuasiIsoFractionObstruction": "4b1d73889efe2fa337a105986124e54782d8a2b4", "Sheaf.Paper.NativeWeilTensorRingedKFlatResolution": "a58ee74f693b5181b487b7f8bce1fac038fb4e10"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence": {"hash": "5da2d5deaba61149d3da85b2d85badfca92ba76a", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:32:07+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
