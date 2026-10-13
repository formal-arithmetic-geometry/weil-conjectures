## What changed

Retired the public duplicate `CochainComplex.termwise_product_isKInjective_and_isLimit`.
The held module now exposes the canonical component declarations
`CochainComplex.isKInjective_of_isLimitFan` and
`DerivedCategory.isLimitFanMkQObjOfIsKInjective`; the retired name is retained only as a
private compatibility proof component. The three downstream callers now use the canonical
components directly.

## Proved and sorry left

No `sorry` remains. The canonical K-injectivity and derived-limit declarations compile, and
all callers compile against them. No new sorry was added.

## No longer needed

The old public combined theorem and its private `productHomotopy` and `mapProduct` helpers are
removed. The callers no longer depend on the combined theorem.

## Where the brief, the DAG or earlier work was wrong

Upstream review #1428 correctly identifies the combined theorem as a duplicate of the two
canonical component declarations. The initial repair packaging placed those declarations in a
new `WeilConjectures` module, but the delivery checker requires new modules to be under
`Sheaf`; they are therefore consolidated into the held item module.

## Earlier second reading (a previous round; superseded)

Self-check for the second reader: the item and all three forced adaptations compile with no
warnings; the public combined declaration is absent and callers use the two canonical
components. The second reader should verify the unchanged caller signatures and the minimal
forced edits.

## Forced adaptations

- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`: against the changed item,
  the original caller fails with unknown constant
  `CochainComplex.termwise_product_isKInjective_and_isLimit`; replacing the destructuring call
  by `isKInjective_of_isLimitFan` and `isLimitFanMkQObjOfIsKInjective` is forced.
- `Sheaf.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts`: the original
  caller has the same unknown-constant error; its two component calls are forced.
- `Sheaf.Topology.RingedSpaceRGammaDerivedLimit`: the original caller has the same
  unknown-constant error; its two component calls are forced.

The corresponding change record is
`coord/changes/retire-duplicate-k-injective-products.md`.


## Second reading by C1

1. Compared every delivered module with the repository. The proposed retirement changed the public target declaration and therefore failed the unchanged-interface requirement. I restored the target theorem and all three callers byte for byte; verdict: pass after repair.
2. Compiled the restored item with `lcompile.py`; it compiles without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The restored proof keeps the existing theorem and its allowed dependencies; verdict: pass.
3. No split-off statements remain. The proposed canonical declarations were not added because they lacked DAG nodes and were unnecessary once the target theorem was restored; verdict: pass.
4. The original proof route and imports are retained. No pruning is claimed; verdict: pass.
5. The DAG node still names `CochainComplex.termwise_product_isKInjective_and_isLimit`, and its Lean signature is unchanged. The unit route is retained; verdict: pass.

Changed during second reading: rejected the retirement change and restored all four modules to the repository versions. No target or caller interface change is delivered.
