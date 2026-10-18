## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleClassicalSheavesUnit` with its signature
unchanged. The final two clauses of `proEtaleComparisonPullbackSections` identify
the actual comparison unit, after two bijective maps, with a bijection on etale
sections. Cancel those injective maps to obtain bijectivity of each unit component.
Mathlib's componentwise isomorphism theorem and reflection by `sheafToPresheaf`
give invertibility of each sheaf unit. Finally
`Adjunction.fullyFaithfulLOfIsIsoUnit.map_bijective` proves the Hom-set clause.

The unit's blueprint route is preserved: evaluation on etale objects followed by
the adjunction argument. Updated the existing node's proof and direct dependencies
and its docstring to match this implementation. No definitions, signatures,
public imports, or consumers changed. No new declarations or nodes.

Validation: the final module compiled through `lcompile.py` in 4.0 seconds without
warnings. The proof applies to every scheme and every etale object, including the
empty scheme, without a ring, quasi-compactness, or nonemptiness hypothesis.
Searched the source library and Mathlib, including the generic adjunction theorem;
the source-library comparison theorem assumes Grothendieck abelian coefficients
and does not directly apply to sheaves of sets. Read Stacks `proetale.tex`,
lemmas `describe-pullback-from-etale` and `fully-faithful`, and the current
blueprint's unit statement and proof.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.proEtaleClassicalSheavesUnit`
(node `det-pe-classical-sheaves-unit`). Both clauses are proved from the existing
section theorem and Mathlib's categorical API. Zero `sorry` remain in the item;
zero holes added; zero split-offs. This is a proof from existing dependencies,
not a decomposition into new obligations.

## No longer needed

Removed these unused proof imports:

- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`;
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

Removed `lem-weil-pbc-sets-etale-inverse-image-restriction` from this node's direct
`proof_deps`, the first proof step's `uses`, and the top-level `tool_uses`.
Its conclusion is already included in the section theorem's bijectivity clause.
It remains needed internally by the section theorem; this delivery does not claim
that its module is globally unreachable. No blueprint unit or statement is bypassed.
No other nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The plan unnecessarily reapplied the etale restriction result: the current
`proEtaleComparisonPullbackSections` statement already includes that bijectivity
as well as normalization of the actual comparison unit. This is a redundant
proof dependency, not a false statement. No interface repairs were needed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
