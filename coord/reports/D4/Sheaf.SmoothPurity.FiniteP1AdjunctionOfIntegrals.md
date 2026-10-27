## What changed

Replaced the hole in
`AlgebraicGeometry.Etale.nonempty_finiteP1AdjunctionOfIntegrals` by an explicit
adjunction construction. The proof obtains standard-coordinate trace-diagonal
data, proves the base finite line is lisse of rank one using the primitive-root
cover, applies the existing `SfDiagonalKernel.triangles` to its two integral
identities, and fills the unit, counit and both component-triangle fields of
`Adjunction` in a proved private generic helper. This keeps the later functor
transports from unfolding the full kernel implementation. It transports the left
functor through the canonical proper forget-supports isomorphism and the right
functor through tensor symmetry and `derivedTensorRightShiftIso`. The original
statement and public imports are unchanged.

Added `Sheaf.SmoothPurity.FiniteP1CoordinateKernel`, a strictly smaller geometric
comparison: the trace, supported diagonal, coefficient pullback and two integrals
in the general triangle theorem's conventions. It asserts neither an adjunction
nor triangle identities on arbitrary complexes. The combining adjunction proof
is complete Lean in the assigned module.

The parent privately imports the new comparison, the local-line theorem and the
proper forget-supports module. Its node follows the resulting proof. Two further
new definition nodes attach existing source-library natural isomorphisms; no
source-library file is modified. No other existing Lean module is delivered.

## Proved and sorry left

Closed the item's one original textual hole:

- `AlgebraicGeometry.Etale.nonempty_finiteP1AdjunctionOfIntegrals`
  (`lem-sp-finite-p1-adjunction-of-integrals`).

Added one named hole, in its own module:

- `AlgebraicGeometry.Etale.finiteP1CoordinateKernel`
  (`lem-sp-finite-p1-coordinate-kernel`).

There are zero holes left in the item. This is a decomposition with one new
coordinate/support-comparison obligation, not a complete axiom-free proof of
projective-line duality. The imported `SfDiagonalKernel.triangles` is an existing
named obligation, not a hole added or closed by this delivery. One old textual
hole is closed and one is added. No positive target-closure ledger net is claimed.

Validation: `lcompile.py --all` compiled both delivered Lean files on the server
with exit code 0: FiniteP1CoordinateKernel 37.2 s and
FiniteP1AdjunctionOfIntegrals 51.7 s. Profiling options are removed. Both files
have lines at most 100 characters. The private generic constructor and local
irreducibility of the kernel maps keep concrete adjunction checking within the
limit. Existing theorem signatures and public imports are preserved.

## No longer needed

No public import was removed, and no module was withdrawn. No target-closure
module is claimed globally pruned.

- `def-weil-pbc-composite-adjunction` is no longer a direct proof dependency:
  the proof constructs one adjunction from its maps and component triangles,
  then transports it; it does not compose two adjunctions.
- `lem-asd-etale-finite-twist-pullback` is not invoked to obtain another
  transport system. The given t supplies its line comparison. Lisse rank one
  is proved directly from `lem-asd-finite-etale-tate-local-line`.
- `lem-sfb-etale-coordinate-trace-contractions`, `lem-kun-0f0g`,
  `lem-kun-proper-base-change-torsion-ring` and supported Kummer theory remain
  needed through the existing general triangle theorem and the new comparison.
  Their modules are not pruned.
- `lem-sp-tower-p1-arbitrary-base-integrals` remains the type of the supplied
  hypotheses. The item does not choose a fresh splitting or reprove its integrals.
- `def-nagata-projective-space-base-change` and `lem-kun-tensor-sym` remain used
  for properness and the final canonical symmetry.

There is no removed private import in the delivered existing file.

## Where the brief, the DAG or earlier work was wrong

The original plan describes the unit and both triangle computations without
naming the existing general `SfDiagonalKernel.triangles` interface. That theorem
supplies precisely the two component equations for the explicit Adjunction
constructor. It uses the coordinate contractions named by the plan. Applying it
is shorter than repeating its coherence computations here.

The existing `sfP1CoordinateIntegrals` assumes an affine base and cannot be applied
to the arbitrary S of this item. Its module is held by D6 at the delivery-time
claim check and is not included or adapted in this packet. The new comparison
uses the already supplied family and requires no affine, Noetherian, boundedness,
constructibility, field-coefficient or Tor-amplitude restriction. It isolates
only the coordinate and support conventions. No forced adaptations are needed.

The bounded-below proper-coincidence statement is not used for an unbounded
comparison. The proof uses the existing unbounded source construction
`rightDerivedLowerShriekIsoRightDerivedLowerStar`, explicitly attached by a new
definition node. The tensor-shift comparison is also an existing construction.
Both definition nodes describe their ModuleCat specialization.

The new comparison needs no positivity assumption on N: its transport,
splittings and integrals are already inputs. The parent uses its original
positivity hypothesis for the lisse-line theorem. For N=0, an N-invertible base
is empty. For N=1 the coefficient ring is zero; the same formulas still apply.
Empty schemes cause no exception. No freeness over Z/N, reduced-base or nonzero
coefficient assumption is used. The even shift in the triangle theorem is 2*1.
Both categories remain unbounded. No definition selects arbitrary witnesses:
all elimination of existential kernel data is inside theorem proofs.

The item's unit `sk-prop-sf-cbc` has empty realized.statement and realized.steps.
No unit or chapter route is changed. The general triangle theorem is a generic
tool from its existing unit, not a bypass of a required projective-line geometric
step. The new comparison follows the same supported-diagonal source passage.

A raw scan of the old DAG encountered a cycle at
`lemma-weil-pbc-derived-exchange-replacement` and missing old records including
`def-weil-pbc-ideal-module-product-stalk`. These are outside the changed records.
No dependency path returns to any delivered node, and their direct dependencies
exist in the overlay. No unrelated DAG repair is attempted.

## New nodes

`lem-sp-finite-p1-coordinate-kernel` owns
`Sheaf.SmoothPurity.FiniteP1CoordinateKernel`, the only new sorry statement.
Its proof in words specifies the variable bijection, Proj and self-product
isomorphisms, proper-support and coefficient comparisons, the trace equation
from hbc, and transport of each alpha/integral equation. This is the geometric
coefficient/kernel step; the adjunction combination is written in Lean.

`def-sp-unbounded-proper-shriek-star-comparison` attaches the existing proved
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`.
It introduces no Lean declaration or hole.

`def-sp-derived-right-tensor-shift-comparison` attaches the existing proved
`AlgebraicGeometry.Etale.derivedTensorRightShiftIso`.
It introduces no Lean declaration or hole.

Change record: `coord/changes/D4-finite-p1-coordinate-kernel.md`. Searches were
run through msearch (LeanSearch, LeanFinder/Loogle, Mathlib grep), rg on both
library roots and the DAG, and the current blueprint. Generic adjunction
transport and shift operations were found; no supported-integral comparison
applicable to the supplied family over arbitrary S was found.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
