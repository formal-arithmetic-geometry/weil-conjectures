# SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions

## Reason

Repair return C-8a024: replace clause relabelling by the actual Tag 093U proof.
Add eight proved supporting results for the precise ringed-module interfaces used by it.
No existing statement or definition is changed. The public clause placeholders in the
returned, unlanded delivery are withdrawn; the actual clause proofs are private.

## Old

```lean
theorem finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    (∀ (F G : CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) (f : F ⟶ G),
      IsFiniteTypeLocallyConstant J B F → IsFiniteTypeLocallyConstant J B G →
        IsFiniteTypeLocallyConstant J B (kernel f) ∧
        IsFiniteTypeLocallyConstant J B (cokernel f)) ∧
    (∀ S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))),
      S.ShortExact → IsFiniteTypeLocallyConstant J B S.X₁ →
        IsFiniteTypeLocallyConstant J B S.X₃ → IsFiniteTypeLocallyConstant J B S.X₂)
```

The original proof was `by sorry`. The returned delivery instead had two public clause
placeholders and proved the displayed conjunction by pairing them.

## New

```lean
theorem finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    (∀ (F G : CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) (f : F ⟶ G),
      IsFiniteTypeLocallyConstant J B F → IsFiniteTypeLocallyConstant J B G →
        IsFiniteTypeLocallyConstant J B (kernel f) ∧
        IsFiniteTypeLocallyConstant J B (cokernel f)) ∧
    (∀ S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))),
      S.ShortExact → IsFiniteTypeLocallyConstant J B S.X₁ →
        IsFiniteTypeLocallyConstant J B S.X₃ → IsFiniteTypeLocallyConstant J B S.X₂)
```

The signature is byte-for-byte unchanged. Both clauses now have complete private proofs.
The eight supporting modules and their nodes are listed in report.md; all are proved.
Their addition and all new proof imports leave the item's original public imports intact.
No target meaning or definition changes, and no new axiom or sorry is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre | G1 | Original theorem proved; signature unchanged. |
| Sheaf.Paper.NilpotentReductionLissity | not queried; no adaptation | Only downstream importer; unchanged statements, definitions, and imports. |

`tools/downstream.py Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre --uses
finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions` reports precisely
one downstream module, `Sheaf.Paper.NilpotentReductionLissity`, and no consumer invocation
of the theorem outside the item. There are no consumers of the two unlanded clause
placeholders in the shared library. No consumer adaptation is required.

## Status

landed 20261018T092904-L-3441075 2026-10-18 (merge of deliver/G1/Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre)
