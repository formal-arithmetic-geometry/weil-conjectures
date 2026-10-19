## What changed

Replaced the proof hole in
`Sheaf.FieldTheory.FiniteDVRResidueNormalAction.IsDiscreteValuationRing.residue_normal_action`.
The existing statements, definitions, visibility and imports are unchanged.

The proof follows Stacks Tag 09ED, assertions (1)-(2), and the node's existing five-step
plan. For the canonical action on `integralClosure A L`, it constructs the
`Algebra.IsInvariant` instance: a fixed integral element lies in K by
`IsGalois.mem_range_algebraMap_iff_fixed`, remains integral over A by injectivity of
K → L, and therefore belongs to A by `IsIntegrallyClosed.algebraMap_eq_of_integral`.
The existing DVR/PID instances supply integral closedness. The module's existing
maximal-ideal contraction instance supplies lying over. Finally
`Ideal.Quotient.normal` and `Ideal.Quotient.stabilizerHom_surjective` give the two
conclusions for precisely the original canonical action and residue homomorphism.

## Proved and sorry left

Closed: `IsDiscreteValuationRing.residue_normal_action`
(node `lem-exc-dvr-residue-normal-action`), the module's only original sorry.
Added: none. Remaining: none. This is a proof of 1 of 1 holes, with 0 split-offs.

## No longer needed

None. No imports, nodes or modules were removed or bypassed. All the existing
proof-dependency nodes remain relevant: DVR/PID integral closedness, finite Galois
fixed-field theory, the canonical integral closure action, maximal-ideal contraction
for integral extensions, and invariant quotient normality and stabilizer surjectivity.
These dependencies are already Mathlib leaves. No new Sheaf proof import is needed.

## Where the brief, the DAG or earlier work was wrong

None. Read Stacks `more-algebra.tex`, `lemma-galois-galois` (09ED) and
`lemma-one-orbit-geometric` (0BRJ). Their hypotheses agree with the existing statement;
residue separability is neither assumed nor needed. The unit
`sk-prop-a1-kummer` has no realized statement or steps assigned to this node, and its
route is unchanged. No new node or statement/definition change was necessary.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
