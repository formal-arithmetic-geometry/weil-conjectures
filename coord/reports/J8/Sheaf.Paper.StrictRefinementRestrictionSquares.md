## What changed

Replaced the proof of `WeilConjectures.PurStrictScalar.strictRefinementRestrictionSquares`
with explicit pasting in the derived category of strict towers. The existing signature,
public imports, definitions and docstring are unchanged. The proof factors the specified
`compositionC` into its local identity-left proper/open seed and its final proper
compositor, including transport along `r.hom_g`. It moves the open comparison through
the proper compositor by naturality, substitutes the proper-composition restriction
identity, applies the last proper-image functor to the seed identity, and uses
naturality of the final proper restriction comparison. The arithmetic equation uses
the same calculation in the opposite restriction direction.

Added two proof imports and two new statement modules, each with a matching DAG node
and complete proof in words. Neither changes an existing interface. The item node now
records the actual pasting proof. The new obligations are component identities, not
copies of either compactification comparison: the seed has no further proper image,
while the proper-composition identity has no open immersions or refinement maps.

## Proved and sorry left

This delivery is a decomposition, not a net proof gain: one original hole is closed
and two smaller holes are added.

Closed: `WeilConjectures.PurStrictScalar.strictRefinementRestrictionSquares`.
There are no remaining holes in the item module.

Added and left:

- `WeilConjectures.PurStrictScalar.strictRefinementSeedRestriction`
  (`lem-pur-strict-refinement-seed-restriction`), in
  `Sheaf.Paper.StrictRefinementSeedRestriction`.
- `WeilConjectures.PurStrictScalar.strictProperCompositionRestriction`
  (`lem-pur-strict-proper-composition-restriction`), in
  `Sheaf.Paper.StrictProperCompositionRestriction`.

The new equations were checked for source and target types, order of all comparison
maps, identity refinements, identity proper maps, the zero tower, and e = 1. They
assert commutation, not invertibility of a proper/open map, so arbitrary tower
objects require no torsion, boundedness or etale-origin hypothesis. The positive
restriction hypothesis is retained wherever preservation of K-injectives is needed.

## No longer needed

No existing import or module is withdrawn. Both existing public imports are retained.
The original direct proof dependencies
`lem-cbc-strict-tower-proper-open-calculus`,
`lem-sf-open-tensor-normalization`, `lem-weil-pbc-mate-pasting`, and
`lem-pur-compact-support-strict-scalar-mate` are not applied directly by the combining
proof. Their role is either in the definitions already imported or in the smaller
normalization arguments. This does not make their modules globally unnecessary.
The item directly uses only the two new component nodes. No unit route is bypassed,
and no source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The supplied proof plan describes the right mathematical route but does not expose
whole-tower Lean declarations for its two restriction components.
`MateEvaluationScalars.scalar_gamma` is a comparison on the derived category of
single-level modules, not on the ordinary derived category of strict towers.
It cannot simply be applied to tower objects. Equality is not detected here by
separate finite derived evaluations. The missing components are stated explicitly
and the remaining pasting is implemented in Lean.

The rework row refers to a quarantined item with an unavailable
`SfP1ChartExchange` dependency. The current shared source exists and was preserved;
the compiler supplied its unpublished dependencies in the private overlay. No
quarantine file is deleted or replaced by an empty module.

## New nodes

`lem-pur-strict-refinement-seed-restriction`:
`Sheaf.Paper.StrictRefinementSeedRestriction`, declaration
`WeilConjectures.PurStrictScalar.strictRefinementSeedRestriction`.
Source: Stacks 0F7B, open case, and 07A6, with the parent's explicit strict-diagram
restriction refinement. It compares the local seed before any final proper image.

`lem-pur-strict-proper-composition-restriction`:
`Sheaf.Paper.StrictProperCompositionRestriction`, declaration
`WeilConjectures.PurStrictScalar.strictProperCompositionRestriction`.
Source: Stacks 0D6E, 03DA and 0940, with the parent's whole-diagram normalization.
It compares only proper compositors and equality transport, for arbitrary scheme maps.

Searches ran through the launcher using LeanFinder, LeanSearch, Loogle and grep.
The blueprint-wide searches for proper restriction and refinement restriction found
no matching named blueprint result. Existing generic naturality and module
restriction lemmas do not state either specialized component equation.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
