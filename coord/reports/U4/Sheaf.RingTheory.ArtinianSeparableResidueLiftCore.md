## What changed

Added the proof-only import `Sheaf.RingTheory.ArtinianSeparableResidueLiftCapture`.
The core theorem is now proved by applying the capture construction and deriving
`IsArtinianRing D'` with `IsArtinianRing.of_finite`.
The capture construction is stated in a new module with its proof intentionally
left as a named intermediate theorem.

## Proved and sorry left

Proved `Algebra.exists_finiteEtale_artinian_residue_lift_core`.
The new theorem `Algebra.exists_finiteEtale_artinian_residue_lift_capture` remains
`sorry`; it is the construction of all required data except the derived Artinian
instance. Its node is
`lem-weil-pbc-artinian-separable-residue-lift-capture`.

## No longer needed

Removed the unused proof-only imports `Sheaf.RingTheory.HenselianEtaleRetraction`,
`Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`,
`Sheaf.RingTheory.LocalDimensionZeroHenselian`, and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`. Added the proof-only
`Mathlib.RingTheory.Artinian.Module` import for `IsArtinianRing.of_finite`. The
capture module remains needed by the proof. No original nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt split off a residue-element theorem that did not connect the
chosen element to the map and was false. This delivery instead leaves a sound,
strictly simpler construction theorem as the sole intermediate hole and combines
it with the standard finite-over-Artinian result.

## New nodes

`lem-weil-pbc-artinian-separable-residue-lift-capture` records the intermediate
construction theorem and its source in Tag 07FI.

## Earlier second reading (a previous round; superseded)

The intermediate statement is strictly weaker than the core theorem because it omits
only the Artinian instance on the lifted ring; the core proof derives that instance
from `Module.Finite` and the Artinian base via `IsArtinianRing.of_finite`.

## Second reading by U4

1. Compared the delivered core module against the repository version: the theorem signature and all existing declarations are byte-for-byte unchanged; only a proof-only import and the proof body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors. The core theorem has no local `sorry`; the capture theorem is the single named split theorem and its node and docstring are present. Verdict: pass.
3. Checked the capture statement against its Lean declaration and the Stacks Tag 07FI source; it is a strictly simpler construction statement, omitting only the derived Artinian conclusion, and does not duplicate an existing declaration. Verdict: pass.
4. Re-read the proof from the target downward. The core proof uses the capture theorem and `IsArtinianRing.of_finite`; the four old Sheaf/Weil proof imports were unused and were removed. The node proof and `proof_deps` now match this route. Verdict: pass.
5. Checked the unit metadata and route: the existing unit and target statements are unchanged, and the new capture node records the same unit and chapter. Verdict: pass.

Changed the core module by pruning four unused proof imports, synchronized the core node's proof metadata with the actual short proof, and recorded this second reading.
