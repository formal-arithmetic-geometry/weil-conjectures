## What changed

Reduced `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_formula`
to a Lean induction, universally quantifying the coefficient input at each rank.
The induction applies `ordinary_counit_zero` and `ordinary_counit_successor`.
These are separate mathematical steps: the first is only rank zero; the second
assumes the preceding-rank formula and proves the next-rank formula.

Moved the construction prefix, from `pullback_plus` through
`OrdinaryCounitEquation`, verbatim into `Sheaf.Paper.AffineOrderedCounitData`.
The original module publicly reexports it. The twelve existing public declarations
keep exactly the same names, signatures, visibility, attributes and bodies.
The final six-conjunct transpose theorem and all existing proved bodies are retained.
No source-library file is edited. The existing rework quarantine is preserved;
the current restored source was used, and its baseline compiled in 32.6 seconds.

Change record: `coord/changes/H7-affine-ordered-counit-data.md`.

Validation: `lcompile.py --all` accepted all four changed modules and the four
unchanged direct importers: `ChartTargetOpenDescent`, `ModelAffineIntegrationOrientation`,
`ProjectionTensorIntegration`, and `VectorIntegrationUnitTranspose` (exit code 0).
The consumer copies were byte-identical and removed after this check. The compiler
printed only existing unused-simp warnings in the dependency `SfP1ChartExchange`;
none came from this delivery. The new induction proof elaborated successfully.

## Proved and sorry left

Original holes: 2. One original hole is closed by decomposition:
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_formula`.
Its induction proof is complete; its statement and canonical maps are unchanged.
This is a decomposition, not a completed proof of the coefficient-counit formula.

The original hole retained is
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.pro_coordinate_projection_composition`
(node `lem-pur-affine-ordered-integration-transposes`).

Two new holes:
- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_zero`,
  node `lem-pur-affine-ordered-counit-zero`, in `AffineOrderedCounitZero`.
- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_successor`,
  node `lem-pur-affine-ordered-counit-successor`, in `AffineOrderedCounitSuccessor`.

All three remaining holes are whole proofs of named public theorems with source,
proof in words, and nodes. The new data module contains zero holes. No data is
chosen from a new existence theorem. Delivery total: 3 holes, net 1 hole added.

## No longer needed

No existing import, node, module or public declaration is pruned. The original
public import closure is retained to preserve consumers. The composite-counit
and trace-contraction dependencies remain needed by the successor step; they
have not been declared globally unnecessary. The data module omits the suffix's
private comparison-naturality, coordinate-line-adjunction and coordinate-section
proof imports, which none of its relocated declarations uses. These imports
remain in the original module where their proofs still use them.

## Where the brief, the DAG or earlier work was wrong

The rework row records quarantine after the SfP1ChartExchange dependency failure.
At session start the item had already been restored in the current source and
compiled successfully. Its Lean attachment, archive and dependencies are retained.
There was no current H7 return entry naming this item in the local snapshot.

A further library search found `ordinaryAffineCounit_tensor_normalization`. It uses
`OrdinaryAffineCounitTensorNormalization.reassociation`, the tower Tate object and
`affineDualizingTowerComparison`; the assigned formula uses `ordinarySourceIso`,
`affineLinearBaseCoefficient` and `ordinaryCompactComparison`. Their canonical
normalizations must still be identified, so applying it does not immediately close
the assigned equation. The induction decomposition retains these calculations.

The parent node already describes the ordinary-counit induction. Its former
single Lean hole had not performed that induction. This delivery formalizes the
combination and records the two missing normalization calculations independently.

The zero case includes empty bases and the zero ring: all identities remain
canonical and do not require a generator. The successor step at d=0 still needs
the preceding-rank hypothesis. Neither lemma alone states the original theorem;
the proof combining them is induction. No divisibility condition is added.

## New nodes

`def-pur-affine-ordered-counit-data` records the unchanged canonical ordinary source
and counit constructions, now in their own module to avoid a circular import.

`lem-pur-affine-ordered-counit-zero` states exactly the identity-adjunction base
case of the original induction, with its canonical source, trace and projection.

`lem-pur-affine-ordered-counit-successor` states only the conditional one-coordinate
step. Its proof follows the normalized affine-line counit, the preceding-rank
hypothesis, projection composition and composite-integration counit contraction.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
