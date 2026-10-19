## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_tensorPullback_dual_toModules_iso`
in `Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback`, without changing its signature,
the existing comparison definition, visibility, or public imports.

Five private, proved helpers retain the inclusion equation in the source library's
local-generator proof of the ideal-pullback isomorphism, identify the two structure-sheaf
comparisons through the adjunction, transport the ideal isomorphism to tensor pullback,
and establish naturality of the transported tensor and dual comparisons. The final
isomorphism is the canonical dual comparison followed by the dual of the inverse ideal
isomorphism. Its canonical-section equality follows by cancellation and contravariant
functoriality. All data are constructed; no choice from an unproved existence theorem occurs.

Updated the existing node's proof and dependencies to this route. Its unit has no realized
statement or proof-step node that this local argument bypasses. The two Picard comparison
nodes used as categorical tools already have complete Lean proofs and are already imported
by the item's original public interface.

The source read was Stacks divisors.tex, definition-invertible-sheaf-effective-Cartier-divisor
and lemma-pullback-effective-Cartier-divisors (Tag 0C4U), together with the actual source
EffectiveCartier local-generator proof. The proof requires no flatness. Empty schemes,
the empty divisor, zero section rings and a non-flat Cartier-preserving base morphism
are covered: cancellation uses nonzerodivisor regularity rather than a nonzero-ring assumption.

Single-file server compilation passed against the current library with no warnings in
28.0 seconds. A separate scratch compilation of the identical module with `#print axioms`
reported exactly `propext`, `Classical.choice`, and `Quot.sound` for the target theorem
(28.2 seconds). The resumed delivery dry run also passed compilation and preflight.
The scratch file under `scratchpad/` is not part of the delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_tensorPullback_dual_toModules_iso`
(node `lem-asd-supported-kummer-cartier-pullback`).

Original holes: 1. Proved: 1. Added holes: 0. Remaining holes: 0. No split-offs.
All five private helpers have complete proofs.

## No longer needed

Kept all three original public imports unchanged. Compared with the live repository,
removed five proof imports that the maintainer added after the sandbox copy was made:

- `Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`: the global kernel
  factorization and affine ideal formula replace this ideal-image theorem.
- `Sheaf.Topology.GlueSheavesOfModules`: the global kernel map and local isomorphism
  criterion replace explicit gluing.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: no separate section-normalized
  adjunction is needed; the original adjunction and its uniqueness comparison suffice.
  Its node `def-pc-module-pullback` remains a conceptual dependency; the actual tensor
  pullback functor and chosen adjunction are obtained through the existing public imports.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`: redundant, since
  the unchanged public Sheaf wrapper re-exports this exact source module.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`: redundant, since
  the unchanged public EffectiveCartier import already exports it.

The proof does not need `lem-pc-closed-subscheme-base-change-ideal-image` or its module
`Sheaf.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`: the source's kernel
factorization and affine `ideal_comap_appLE` formula supply the needed ideal identification.
It does not need `lem-weil-pbc-glue-sheaves-of-modules` or its module
`Sheaf.Topology.GlueSheavesOfModules`: the kernel factorization is already a global map,
and the source's local-generator isomorphism criterion applies directly. Removed these
two obsolete entries from the node's top-level `tool_uses` and from `proof_deps`.
No claim is made that these modules are globally unreachable from other parents.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but explicit gluing of dual local bases is
unnecessary given the source library's global ideal factorization and local-generator API.
The existing theorem `nonempty_pullback_toModules_iso` exposes only an arbitrary isomorphism,
not its inclusion equation, so applying that theorem alone cannot prove the section clause.
The private helper repeats its proved local calculation while retaining the kernel equation.
No statement or definition repair was necessary. There are no new nodes.

The resumed dry run requested an interface change record for the namespace-opening
commands. Added `coord/changes/m3-supported-kummer-cartier-pullback-proof-context.md`,
recording the unchanged public signatures and the complete downstream-module audit.
No downstream file needs adaptation.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
