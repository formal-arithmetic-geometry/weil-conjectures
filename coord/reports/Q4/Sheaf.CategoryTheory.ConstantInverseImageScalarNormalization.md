## What changed

Proved `CategoryTheory.ConstantCompletion.constantInverseImageScalarNormalization`
without changing its signature. The proof constructs, for every source object,
the ring homomorphism obtained by evaluating the scalar adjunct on constant
sections. Constant endomorphisms and adjunction-unit naturality let the given
algebraic graph equations prove its four ring laws directly. Ring naturality and
naturality of `F.constants` give naturality in the coefficient ring.

Added the proved theorem `CategoryTheory.ConstantCompletion.constantRingSectionRigidity`
in `Sheaf.CategoryTheory.ConstantRingSectionRigidity`, privately imported by the
item. Its universal-polynomial argument identifies that natural ring homomorphism
with the sheafification unit. Sheafification uniqueness and the geometric
adjunction finish the original equality.

Validation: both modules compiled through `lcompile.py` (rigidity: 9.0 s;
scalar normalization: 12.4 s). The two line-length warnings from the latter
were corrected before delivery.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.ConstantCompletion.constantInverseImageScalarNormalization`
(node `lem-sf-constant-inverse-image-scalar-normalization`).

The new theorem `CategoryTheory.ConstantCompletion.constantRingSectionRigidity`
(node `lem-sf-constant-ring-section-rigidity`) has a complete proof.
No holes added; no `sorry` remains in either delivered module.

## No longer needed

No existing imports removed and no modules or declared dependencies pruned.
All three original dependency nodes remain needed for the data and definitions.
The former plan's construction of a canonical constant-ring comparison,
comparison with its inverse, and construction of a natural automorphism are
unnecessary: apply polynomial rigidity directly to the scalar adjunct.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned theorem is unchanged and the polynomial argument handles empty
covering sieves, zero rings and empty topoi. The DAG's initial comparison
construction was more machinery than needed. Ring graph equations on constant
endomorphisms suffice to obtain the ring-homomorphic family directly.
The rigidity proof uses `ULift ℤ` so the universal integer and polynomial rings
are in the same universe as the arbitrary coefficient rings.

The three searches used LeanSearch, LeanFinder and the remote Mathlib grep;
none found an existing rigidity theorem. A whole-blueprint search for
`constant ring` found related coefficient results but no duplicate.

## New nodes

`lem-sf-constant-ring-section-rigidity` records the proved, site-independent
rigidity step. A natural family of ring homomorphisms from each ring to the
sections of its constant sheaf at one object equals the canonical unit.
Initiality determines integers, local surjectivity represents the image of X
by a polynomial, integer evaluations and local injectivity handle every
nonidentity polynomial, and evaluation X to a determines arbitrary rings.
This is strictly part of the normalization argument and introduces no new hole.
No shared interfaces or other existing modules changed; no change record needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
