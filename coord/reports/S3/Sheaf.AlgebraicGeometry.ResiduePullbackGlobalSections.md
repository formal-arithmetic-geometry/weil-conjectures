## What changed

Proved `AlgebraicGeometry.Scheme.nonempty_residuePullback_globalSections_iso` in
`Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections`, with its signature unchanged.
The proof composes the existing tensor-pullback stalk isomorphism with a proved global-germ
isomorphism and scalar transport. Three private helpers are fully proved in the same module.
Mathlib's `SpecToEquivOfLocalRing.apply_symm_apply` identifies the point and residue ring map
simultaneously, avoiding separate dependent transports. Updated the node's proof and proof origin
and the theorem's proof docstring to describe the Lean argument. No public imports changed.

Searches: Lean Finder returned the global/stalk ring comparison lemmas in Mathlib's
AlgebraicGeometry.Stalk; Loogle returned restriction-of-scalars and ring-equivalence APIs;
local ripgrep searches checked module stalks, change of rings, and residue-point morphisms.
The existing `Modules.exists_tensorPullback_stalk_iso` was the required comparison.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.nonempty_residuePullback_globalSections_iso`
(node `lem-sc-residue-pullback-global-sections`). The module has no remaining `sorry`.
Added zero holes, zero new public declarations, and zero new modules.
The private global-germ bijectivity, natural isomorphism, and scalar-transport helpers all compile
without holes. The existing tensor-pullback comparison remains a used dependency; this delivery
makes no claim to close holes reachable through its imports.

The file compiled cleanly with lcompile.py. The delivery dry run additionally checks the axiom
probe and preflight. No quasi-coherence, flatness, nonzero-module, or finite-generation assumptions
were added. The global-germ helper actually works on any local-ring spectrum at its closed point;
zero module sheaves are included. The unit's realization lists are empty, and its route is kept.

## No longer needed

None. All original imports are retained for the statements or the tensor-pullback stalk proof.
The sole planned proof dependency, `lem-weil-pbc-module-stalk-pullback` in
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`, remains necessary. No DAG nodes or modules
are pruned, and no alternative theory was imported.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable planned dependency was found. The plan's scalar and point
identifications are supplied together by the inverse identity of Mathlib's classification of
maps from local-ring spectra. This is a concrete implementation of the planned residue-map step.
No statement, definition, target, or other group's module was changed.

## Second reading by S3

1. Compared the complete delivered module with the repository version. The sole existing
   theorem signature is byte-for-byte unchanged, and all imports and visibility are unchanged.
   The three additions are private, fully proved helpers. No existing definition or statement
   changed, so no change record or forced adaptation is required. Verdict: pass.
2. Independently compiled the module with lcompile.py, without errors or warnings. A scratch
   copy with #print axioms for all three helpers and the main theorem reports exactly propext,
   Classical.choice and Quot.sound for each; not even sorryAx is present. Scanned the delivered
   Lean for sorry and forbidden declarations: none. Both private isomorphism definitions are
   real constructions from proved bijectivity or proved adjunctions; no arbitrary witness from
   an unproved existence statement is used to define data. Verdict: pass.
3. There are no split-off statements, new public statements, or added holes. Checked the local
   ring closed-point neighborhood argument, including arbitrary module sheaves and the zero
   sheaf; injectivity uses identity restrictions and surjectivity uses germ representatives.
   Empty schemes have no point x, so give no exceptional instance of the theorem. Verdict: pass.
4. Read the argument from the target down: global germ comparison, the planned tensor-pullback
   stalk comparison, scalar transport by uniqueness of left adjoints, and the local-ring Spec
   equivalence identify precisely the required functors. Independent Loogle search for
   "ModuleCat.extendScalars, ModuleCat.restrictScalars" found the adjunction already used;
   Mathlib grep for germ bijectivity and module evaluation/stalk comparisons found no direct
   replacement. Local library searches found no shorter exact comparison. Every public import
   supplies signature vocabulary (including moduleRings from DerivedHomMayerVietoris), and the
   plain tensor-stalk import supplies the sole planned dependency. No old proof dependency is
   unused. The unit sk-prop-av-cube has empty realization lists and its route is preserved.
   Verdict: pass; no pruning is justified.
5. Compared the node files: only proof and proof_origin differ. The revised four-step proof
   matches the Lean construction; proof_deps equals the union of the steps' uses and retains
   lem-weil-pbc-module-stalk-pullback. Lean metadata and statement are unchanged; there are no
   new nodes to audit. Verdict: pass.

Second reading changed only this report, adding the independent review and verification evidence.
No proof repair was necessary. One original hole closed, zero holes added, zero split off.
