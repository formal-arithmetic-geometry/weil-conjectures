# WeilConjectures.PurScalarProjection.native_scalar_identification

## Reason

Prune an unused auxiliary theorem from the Sheaf item module. This theorem is the
module's only remaining sorry. Its whole-quotient-diagram scalar equation is not
used by the current proof of any required statement.

This is not based solely on zero Lean importers. The actual replacement argument
is already present and proved:

- CompactSupportScalarGammaIdentification.gamma_identification identifies the
  specified completedArrow with the actual ordinary proper/open scalar mate by
  finite counit equations, comparison_reduction, comparison_factorization and the
  constructible Milnor injection. It does not use native_scalar_identification.
- compactSupportScalarProjectionIdentification conjugates ordinaryCompletedSquare
  by the uniquely normalized realizations and uses gamma_identification. Its proof
  is retained verbatim.
- diagram_projection applies SFY.reduction to the existing ordinary coefficient
  projection equality and postcomposes with nativeRealization. Its proof is
  retained verbatim. The definition nativeRealization remains.
- properProjection_existsUnique, openProjection_existsUnique, projection_unit and
  the scalar completion normalizations remain with their existing proofs.

The only DAG parent is lem-pur-compact-support-integral-coefficient-comparison.
Its Step 5 cites this node for the finite and integral projection squares, supplied
by the unchanged declarations above. It does not require the withdrawn auxiliary.
No unit statement or realized unit step singles out native_scalar_identification.
The item node's Step 7 now records the replacement route, and its Lean attachment
no longer lists the withdrawn declaration. The node statement is unchanged.

The entire lean/ tree and all DAG nodes were searched by declaration name. The
only occurrences are the theorem being removed and its own node attachment.
There are no direct importers of the item module in the current Lean source tree,
no item quarantine/rework row, and no repair entry requiring this auxiliary.
No adopted WeilConjectures source file is changed.

## Old

```lean
include D hl in
/-- The whole-diagram realization carries the reduced ordinary scalar mate to
exactly the specified strict scalar mate, before any evaluation or total limit.
Source: Stacks 0E48, 0B56, 0941;
(blueprint: lem-pur-compact-support-scalar-projection-identification), Steps 3--4 and 7.
Proof: the nativeRealization adjunct is the strict quotient augmentation.
Perfect-quotient exchange identifies the proper transpose with the quotient of
the actual proper counit. Open scalar balancing is the same pure-tensor map on
every extension-by-zero summand. Paste the two adjunction identities. The
whole-diagram reductionBalancing counits fix both ramified endpoint comparisons,
so the two strict diagram maps agree without testing their evaluations. -/
theorem native_scalar_identification
    (SEX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SEY : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SFX : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SFY : CoefficientDerivedSystemCalculus.{u, u} l F Y)
    (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ∃ hCM : finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M),
      (PurStrictScalar.T l E F i Y).map
          ((PurStrictScalar.systemU l E Y).map
            (nativeRealization l E D hl f c SEX SEY M hM)) ≫
          (PurStrictScalar.arrow l E F i c SEX SFX e he hepos).app M =
        (PurStrictScalar.reductionBalancing l E F i Y SEY SFY e he hepos).hom.app
            ((image (completed l E) c).obj M) ≫
          (PurStrictScalar.subsequence l F Y e).map
            ((PurStrictScalar.systemU l F Y).map
              (SFY.reduction.map ((comparison (completedChange l E F i) c).app M) ≫
                nativeRealization l F D hl f c SFX SFY
                  ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) hCM)) := by
  sorry

```

## New

The unused auxiliary declaration is removed. Every other declaration, definition,
proof, import, attribute and setting in the module is retained verbatim. The item
node records the existing replacement argument, drops the unused Lean attachment,
and updates the direct proof dependencies to that route.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | E4 | Own unused auxiliary removed; all used declarations and proofs retained. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | D8 | DAG parent Step 5 still uses the unchanged main and finite projection theorems; no Lean edit or statement change. |

There are no direct Lean importers of the item module. The only DAG parent's
statement and proof dependencies remain valid; no parent edit is needed because
its dependency is on the retained node statement, not the withdrawn auxiliary.

## Status

landed 20261027T034632-L-3667948 2026-10-27 (merge of deliver/E4/Sheaf.Paper.CompactSupportScalarProjectionIdentification)
