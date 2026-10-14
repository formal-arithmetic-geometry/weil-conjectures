## What changed

Proved `AlgebraicGeometry.standardSingleFlatCounit_localization_pair` by importing
`Sheaf.Algebra.Homology.BaseDerivedExtensionResolution`. After unfolding the theorem's
local ring and derived-category bindings, the proof installs the algebra structure induced
by `g.stalkMap a` and applies `ModuleCat.exists_baseDerivedExtension_resolution`. This
provides the required derived scalar-extension functor, counit, and left-derived property;
the universally quantified input complex is introduced but does not affect the universal
pair. Updated the node proof and proof dependency to
`lem-pc-base-derived-extension-resolution`.

## Proved and sorry left

Closed `AlgebraicGeometry.standardSingleFlatCounit_localization_pair`.
No `sorry` remains in the delivered module and no new holes were added.

## No longer needed

None: the repository module had only the presentation import, and the old node's
`proof_deps` was empty. No existing import, node dependency, or module was pruned.
The first worker's attempted import of `StandardSingleFlatCounitLocalization` was
never in the repository baseline and is not counted as pruning. The presentation
import remains public because the signature uses `StandardSingleFlatCounitOnOpen`;
the added resolution import is private because only the proof uses it.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a bespoke stalk-localization construction, but the target only asks for
existence of a universal scalar-extension pair and universally quantifies an otherwise
unused complex. The general base derived-extension resolution theorem already proves this
existence for any ring map, so the localization and completion route is unnecessary and
would create an import cycle.

## Second reading by A3

1. Compared every delivered Lean module and node with the repository using `diff`.
   Restored the declaration signature's indentation; it is now byte for byte identical.
   There are no definition, statement, visibility, or public-import changes, and no
   new declarations or change records. Verdict: pass.
2. Read the proof from the stalk ring map through the `toAlgebra` instance to the
   existing resolution theorem. Its `algebraMap` is definitionally the required
   stalk ring homomorphism, and projection retains exactly the universal pair.
   No data is defined or chosen from an open existence theorem. Checked the module
   for forbidden declarations and holes; there are none. Compiled the module and an
   independent scratch copy with `#print axioms` for both the delivered theorem and
   the generic resolution theorem: only `propext`, `Classical.choice`, `Quot.sound`.
   Verdict: pass.
3. No statements were split off and no new holes or nodes were added. The reused
   result is a stronger general theorem already proved in the library, rather than
   a restatement under a new name. Its construction requires neither ring-map
   flatness nor a nonzero complex: zero complexes, identity ring maps, and zero
   rings introduce no additional hypotheses. Verdict: pass.
4. Searched existing scalar-extension and left-derived declarations in Mathlib and
   `lean/Sheaf`, and queried Loogle for `ModuleCat.extendScalars`; ordinary extension
   adjunctions do not themselves supply this unbounded derived universal pair. The
   proved general resolution theorem is the direct tool for the required conclusion.
   Both imports are needed, with proof-only resolution imported privately. Corrected
   the pruning report: old `proof_deps` was empty and no baseline imports were removed.
   Read `dag/units/sk-thm-picard-coherence.json`, including its `realized` field: this
   auxiliary pair is not a realization of a unit step; using a general proved tool
   here preserves the unit's geometric route. Verdict: pass.
5. The node's single proof step, `proof_deps`, and `proof_origin` match the application
   of `lem-pc-base-derived-extension-resolution`. Preserved all other node fields and
   restored its original verbatim Lean signature serialization. Verdict: pass.

Changes made: restored exact signature whitespace and node serialization; replaced
proof-local `letI` with `let` to resolve style warnings; explicitly retained the two
unused hypothesis terms without changing the interface; corrected the proof docstring
(the proof retains a universal pair, not a bounded-flat counit computation); and
corrected the pruning accounting above. The original proof route is retained.

Holes closed: `AlgebraicGeometry.standardSingleFlatCounit_localization_pair` (one).
Holes added: none. This closes a hole using a proved theorem, not a decomposition.
