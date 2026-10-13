## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.tensorDegreeZeroMateSquare`
with a reduction using the pinned tensor counits, affine projective sections,
flat-module pullback comparison, single-homology naturality, and source inverse
cancellation. The existing theorem's signature is byte-for-byte unchanged.
All original public imports and definitions are unchanged; added imports are
proof-only.

Added the proved helper
`AlgebraicGeometry.Scheme.Modules.tensorSingleBaseChangeSquare` in its own module.
It follows from the existing `canonicalSingleBaseChangeComparison`: transport
ordinary pullback to the specified tensor pullback by the adjunction-preserving
isomorphisms, prove naturality of the canonical direct-image unit, and cancel
those isomorphisms. No derived comparison or base-change map is cancelled.
The helper's public imports supply its signature; its ordinary-comparison import
is proof-only. Its scoped heartbeat budget accommodates unfolding the localized
single-complex comparisons during naturality, within the single-file time limit.

## Proved and sorry left

Closed the original item hole:
`AlgebraicGeometry.Scheme.Modules.tensorDegreeZeroMateSquare`
(node `lem-sc-picard-tensor-degree-zero-mate-square`).

Also proved the proposed split-off statement:
`AlgebraicGeometry.Scheme.Modules.tensorSingleBaseChangeSquare`
(node `lem-sc-picard-tensor-single-base-change-square`).

No holes are added. Neither delivered module contains `sorry`. This closes one
original hole without decomposition into new holes. Existing imported open
statements, including `canonicalSingleBaseChangeComparison`, are not claimed
proved. Axiom checks allow `sorryAx` only through those existing dependencies;
they are not an unconditional completion of the target's import closure.

The constructions work for zero modules, rank zero, and empty schemes. The
source direct image is finite locally free, hence quasi-coherent with projective
affine sections, giving the required intrinsic flatness. The target tensor
comparison, derived exchange, and ordinary exchange need not be invertible.
No definition or arbitrary witness of an unproved mere existence theorem is added.

## No longer needed

No original imports removed; no original dependency module is claimed pruned.
The parent no longer directly uses the old proof dependency
`lem-pc-derived-base-change-unit-compatibility`: its exchange step uses the proved
tensor-square helper, which uses the existing ordinary single comparison. The
old unit-compatibility module remains needed transitively. Direct parent edges
to `lem-pc-canonical-single-direct-image-comparison` and
`lem-weil-pbc-module-base-change-map-open-restriction` are retained because the
parent proof uses their maps.

The helper needs `SchemeDerivedBaseChangeMap`, not the broader
`DerivedModuleBaseChangeMap` predicate module. Its first worker's proof-plan
import of `DerivedBaseChangeUnitCompatibility` is replaced by the proof-only
`CanonicalSingleBaseChangeComparison` import. The redundant new parent import
of `Mathlib.AlgebraicGeometry.Morphisms.Flat` is removed: the retained
flat-module comparison publicly supplies it through direct-image Basic.
The canonical degree-zero mate module still supplies `canonicalDirectImageH0Iso`.

## Where the brief, the DAG or earlier work was wrong

The first worker left the generic tensor single-square theorem open and treated
the ordinary-pullback comparison as insufficient. The second reading found that
naturality and cancellation of the adjunction-preserving tensor-to-ordinary
isomorphisms prove precisely this tensor square. No mathematical statement or
unit route needs changing. Mathlib searches provide comparison and naturality
ingredients; the sufficient scheme comparison already exists in the library.

## New nodes

`lem-sc-picard-tensor-single-base-change-square` records the proved exchange step
before taking H0, with an arbitrary commutative square and no flatness or
invertibility assumption on derived comparisons. Its proof dependencies now
record the ordinary single comparison, canonical single maps, and the tensor
pullback adjunction. The parent then proves flatness, constructs its isomorphism
and base-change map, takes H0, and cancels the source comparison.
No change record is needed: existing statements and definitions are unchanged.

## Second reading by F2

1. Compared every delivered module with the repository: the sole existing
   theorem's signature is byte-for-byte identical, all its original public
   imports remain, and no definition changes. The helper is genuinely new.
   Verdict: unchanged existing interface.
2. Compiled both modules in import order through `lcompile.py`; checked for
   forbidden declarations and direct holes. Neither file contains `sorry`,
   axioms, unsafe/opaque declarations, external implementations, or hollow data.
   Checked declaration axioms with `#print axioms` in a scratch copy; only the
   standard axioms and `sorryAx` from existing open dependencies are permitted.
   Verdict: a valid reduction, with no new holes.
3. Read the proposed split-off statement and its proof in words, checked zero
   modules, empty schemes, and arbitrary noncartesian commutative squares, and
   searched independently with LeanFinder, qualified Loogle, Mathlib grep and
   library rg. The existing ordinary-pullback single comparison suffices after
   transport. Proved the proposed split-off statement instead of leaving it
   open. Verdict: true, needed, and proved from existing library statements.
4. Reviewed the proof from the target downward and retained its construction,
   flatness, and H0 argument. Removed the redundant added flat-morphism import
   and narrowed the new helper's signature imports. Every old direct dependency
   removed is identified above, with its remaining transitive use. Read
   `dag/units/sk-prop-av-cube.json`: its existing realized lists are empty; this
   auxiliary exchange refinement changes none of the unit's recorded steps.
   Verdict: shorter route found; no unit bypass and no module pruning claimed.
5. Checked the parent and new node against the actual declarations, exact new
   signature, sources, chapter/unit, created/blueprint records, searches, and
   union of proof-step uses. Corrected the parent's two still-direct dependency
   edges and replaced the helper's proof plan with its actual transport proof.
   Verdict: records match the delivered Lean.

Second reading changed: closed the new tensor exchange hole using the existing
ordinary single comparison; repaired dependency records and report; narrowed
new imports; removed a redundant proof import; restored exact signature spacing.
