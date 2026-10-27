## What changed

Simplified the proved private `explicitPullbackLimit` in
`Sheaf.AlgebraicGeometry.PresheafPullbackEtalePointLifting`: evaluate the cone at
an arbitrary scheme, identify it with `Types.pullbackCone` using identity
isomorphisms, use `Types.pullbackLimitCone.isLimit`, and apply
`evaluationJointlyReflectsLimits`. This replaces the handwritten natural
transformation, naturality, factorization and uniqueness proofs. The public
theorem, all definitions, all imports, and both projection equations are unchanged.
Updated the item's first DAG proof step and proof origin to describe this route.

Both the original and revised module compiled cleanly through lcompile.py against
the published library (4.9 and 4.2 seconds respectively). Delivery preflight also
checks the axioms. Change record:
`coord/changes/S7-presheaf-pullback-pointwise-limit.md`.

## Proved and sorry left

The live module already has zero holes: W4's completed proof landed as
20261023T132216-L-2233373 before this work. Holes closed in this delivery: zero.
Holes added: zero. Holes split off: zero. No sorry remains in
`AlgebraicGeometry.AlgebraicSpace.presheafPullback_etale_point_lifting`,
`explicitPullbackLimit`, or `explicitPullbackSquare`.
The private limit helper is re-proved using Mathlib; the main theorem retains
its full existing proof. No arbitrary witness is chosen from an unproved theorem.

## No longer needed

No imports, nodes or modules are removed. All three stated project proof
dependencies remain relevant, with their existing imports. Only the private
handwritten universal lift and its naturality/uniqueness implementation are
replaced by Mathlib's pointwise limit API. The quarantine archive is preserved.
The unit sk-i-curve-zero has no realized entry for this node; its route is kept.

Searches through msearch.py: LeanFinder and Loogle both found
`CategoryTheory.Limits.evaluationJointlyReflectsLimits`; grep found its
implementation and `Types.pullbackLimitCone`. Their source implementations were
read before the proof was written. Direct Lean/DAG searches checked the existing
pullback construction, representable-etale definition and field-extension
joint-surjectivity definition. No new project dependency is introduced.

## Where the brief, the DAG or earlier work was wrong

The rework row records a historical bad import of SheafPullbackCone, but its
separate C3 repair has landed and W4 has already restored and proved the entire
item. This delivery therefore claims no restoration and no newly closed hole.
Its concrete change is a shorter complete proof of the same universal property.
The original proof has no reproduced compile failure. No mathematical statement
or definition correction is needed.

Sources read: spaces-topologies.tex lemma-etale (041F), part (3), whose proof is
omitted, and spaces-properties.tex definition-points (03BU) and
lemma-points-cartesian (03H4), including the common-extension argument.
The revised helper is valid for arbitrary presheaves, including empty section
types, and needs no nonemptiness hypothesis. The main proof still handles the
empty index type by extracting an impossible index; empty base schemes and
identity maps need no exceptions. Public signature text is unchanged. Existing
public consumers need no adaptation, and the private helper cannot be imported
by another module.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
