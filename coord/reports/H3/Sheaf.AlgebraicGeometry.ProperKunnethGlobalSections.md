## What changed

Proved `AlgebraicGeometry.Etale.isIso_kunnethGlobalSectionsMap_of_isProper`
without changing its signature or any definition. The already declared cyclic-coefficient
compatibility theorem yields invertibility of the canonical sheaf-valued `kunnethMap`.
Unfolding `kunnethGlobalSectionsMap` then transports this through its tensor and Leray
isomorphisms. The resulting composition is invertible by the standard categorical instances.
Updated the theorem docstring and `lem-kun-0f14b`'s proof route to match this proof.

The final module compiled cleanly through `lcompile.py` in 4.7 seconds on resumption,
after import pruning and aligning the proof documentation. The preceding proof with the original imports compiled in 25.9 seconds.
No dependency statements, definitions, visibility, or consumers were changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_kunnethGlobalSectionsMap_of_isProper`
(node `lem-kun-0f14b`). Added 0 holes; split off 0 statements; 0 holes remain in
the delivered module. This is a proof from existing declared dependencies, including
`AlgebraicGeometry.Etale.kunnethMap_agrees_with_leray_projection_formula_modN`,
whose pre-existing `sorry` is unchanged. It does not claim the complete target closure
is free of `sorryAx`.

## No longer needed

Retained the two original public imports and the private proof import
`Sheaf.AlgebraicGeometry.KunnethMapAgrees`. Removed these unused direct proof imports:

- `Sheaf.EtaleCohomology.KunnethOneProper`
- `Sheaf.AlgebraicGeometry.ProperStability`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `Mathlib.GroupTheory.Torsion`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN`
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`
- `Mathlib.FieldTheory.IsSepClosed`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.EtaleCohomology.SepClosedFieldVanishing`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`

The following nodes are no longer direct proof dependencies of `lem-kun-0f14b`:

- `lem-kun-proper-stability`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-kun-0ezp`
- `def-kun-constant-sheaf`
- `def-kun-rgamma-unbounded`
- `def-kun-derived-tensor`
- `lem-kun-0f0c`
- `lem-kun-pullback-constant`
- `lem-kun-0f0g`
- `def-weil-size-convention`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-kun-0f10`
- `lem-kun-0f12`
- `lem-kun-tensor-sym`

Removed the obsolete direct `tool_uses` entry
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`; the canonical transport
already encapsulates this comparison.

Their geometric, projection-formula, base-change, and point-equivalence work is already
encapsulated in the existing compatibility theorem and in the canonical global-sections
transport. They may still be required transitively by those declarations; no global
unreachability or module withdrawal is claimed. The integral bounded-below theorem
`lem-kun-0f14a` and its module `Sheaf.EtaleCohomology.KunnethOneProper` are not used.
The unit has no recorded realized steps, and its one-proper-factor statement is preserved.

## Where the brief, the DAG or earlier work was wrong

The longer factorwise plan is unnecessary in this module because clause (b) of the
existing compatibility theorem already includes the `IsIso` conclusion. The proof
uses that recorded dependency directly and proves the canonical transport explicitly.
No mathematical statement was found false or changed.

On resumption the sandbox held only `.brief2` through `.brief5` and `.budget`, with no
saved Lean packet or report. The repository's old dry-run log recorded a refused split,
not a delivery. The existing dispatcher metadata and clock were left untouched; the
proof above was reconstructed against the current library without retaining that split.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
