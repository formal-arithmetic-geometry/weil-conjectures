## What changed

Closed `AlgebraicGeometry.Scheme.Modules.coefficientTarget_scalar_span` without changing its
signature or definitions. Added the proved theorem
`AlgebraicGeometry.coefficientIntersection_scalar_decomposition` in the new module
`Sheaf.AlgebraicGeometry.CoefficientIntersectionScalarDecomposition`. It expresses every
intersection-ring scalar as a finite sum of products from the two affine factors.

The new theorem applies Mathlib's `isIso_pushoutSection_of_isAffineOpen` to the original
cartesian square with the affine opens U, the image V of Z, and B. It compares that ring
pushout with `CommRingCat.isPushout_tensorProduct`, proves both inclusion formulas, and
uses `TensorProduct.exists_sum_tmul_eq`. The target proof establishes pullback-unit
semilinearity, inverse support scalar transport, and membership of each product term in
the target-ring span, then combines them by finite summation. Every construction is
explicit or determined by a proved universal property.

Read the source affine calculation in Stacks Project, Tag 02KG, Lemma 30.5.1
(https://stacks.math.columbia.edu/tag/02KG). The unit's affine coefficient computation is
kept; no unit or chapter statement or step changes. The local literature tree does not
contain the downloaded blueprint or Stacks source, so the unit was read through its
verbatim record `dag/units/sk-thm-picard-coherence.json`, and Tag 02KG online.

Searches used LeanFinder, Loogle, LeanSearch, and source grep. LeanSearch returned an
internal server error; Loogle and grep found the affine pushout theorem and finite tensor
expansion. Also inspected `aux-pc-coefficient-intersection-ring-pushout`: its algebra
coordinates differ and it states the pushout, rather than the finite-product formula.
The direct Mathlib proof supplies the required formula without that additional interface.

Both delivered modules compile cleanly through `lcompile.py --all`. No consumer module is
adapted, and no existing declaration signature, public import, or definition changes.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.coefficientTarget_scalar_span`
(node `lem-pc-coefficient-target-scalar-span`).

Added one fully proved theorem:
`AlgebraicGeometry.coefficientIntersection_scalar_decomposition`
(node `lem-pc-coefficient-intersection-scalar-decomposition`).

No `sorry` remains in either delivered module. Holes closed: 1. Holes added: 0.
This is a proof, not a decomposition into remaining obligations. The scalar proof also
covers a=0, s=0, zero section modules, empty Z or B, and empty intersections; the affine
pushout and tensor expansion require no nonemptiness or nonzero ring assumption.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange`.
The target proof no longer uses node
`lem-pc-finite-affine-cech-intersection-base-change` or its theorem
`AlgebraicGeometry.finiteAffineCech_intersection_baseChange`. In particular, proving that
both intersection morphisms are affine is unnecessary here: Mathlib's affine-open section
pushout theorem computes the ring directly.

Kept the public import `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap`
because the statement and proof use its concrete generator and support isomorphism. The
coefficient comparison existential theorem, its generator-normalization theorem, and its
face-naturalness theorem are not invoked by this proof; their modules remain transitively
imported by the required definition module and are not claimed globally pruned.
The new proof-only decomposition import and both new module imports are used. No other
node or module from the item's planned dependencies is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated the missing explicit affine tensor decomposition as an
obstacle. Mathlib already provides the underlying affine-open section pushout theorem;
its comparison with the tensor-product pushout gives the required decomposition. No new
unproved intermediate theorem is necessary.

The node's scalar argument is correct. The separate affine-intersection-morphism theorem
is an unnecessary detour below the unit level. Using Gamma(X,V) for V=the image of Z
avoids transporting the ring action through GammaSpecIso: the restricted section carrier
is identified by `F.restrictAppIso`, and its inverse sends d times s to an actual source
section. Restriction of scalars changes only the A-action, not that carrier.

## New nodes

`lem-pc-coefficient-intersection-scalar-decomposition` records the proved finite-product
ring formula in `Sheaf.AlgebraicGeometry.CoefficientIntersectionScalarDecomposition`.
It has no module-sheaf parameter or span conclusion and is strictly the affine ring step
of the target argument. Its complete proof uses Mathlib only. The parent node's `proof`,
`proof_deps`, and `proof_origin` now describe the finite-product decomposition followed
by the two proved scalar transport formulas and the span summation. No change record is
needed: all existing interfaces stay identical.

## Second reading by C1

1. Compared the delivered target module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only the proof
   and its proof-only import changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and the
   proof constructs are explicit universal-property and tensor-product constructions.
   Verdict: pass.
3. Checked the new decomposition statement against the affine tensor-product formula
   and searched the library for duplicates. It is true for zero and empty cases, has no
   unnecessary hypotheses or weakened conclusion, and is not already present. Verdict:
   pass.
4. The proof follows the affine pushout route, retains the unit's affine coefficient
   computation, and removes only the unused affine-intersection base-change detour.
   The proof-only imports are minimal for the delivered files. Verdict: pass.
5. Compared both DAG nodes with the Lean declarations and proof dependencies. The new
   node records the finite-product step, and the parent node records its use followed by
   scalar transport and span closure. Verdict: pass.

I changed only this report section after the initial delivery attempt; no Lean source or
DAG content was altered during second reading.
