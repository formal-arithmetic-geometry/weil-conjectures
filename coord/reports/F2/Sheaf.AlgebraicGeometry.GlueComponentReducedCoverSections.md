## What changed

Proved `AlgebraicGeometry.glue_component_reduced_cover_sections` in
`Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections`, keeping its signature and
public imports unchanged. Added the proof-only import
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`.

The proof establishes the finite-cover topology directly, applies Mathlib's
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective` on each component open,
transports its section isomorphism with `arrowResLEAppIso`, and factors the original
restriction maps through these bijections using `Scheme.Hom.map_appLE`. Sheaf
separatedness gives injectivity; unique gluing on the disjoint cover gives surjectivity.
Updated the existing DAG node's proof, proof dependencies and proof origin to agree.
The unit's route is preserved; no statement or definition changes were made.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.glue_component_reduced_cover_sections`
(node `lem-sc-glue-component-reduced-cover-sections`).
No `sorry` remains in the item, and no holes or modules were added. This is a proof,
not a decomposition. The module compiles through `lcompile.py` without warnings.
The proof handles empty index types and empty opens without nonemptiness assumptions;
its gluing argument uses the subsingleton section ring on the empty open. For a
singleton family, the component open is all of V and the restricted closed immersion
is surjective onto the reduced target.

## No longer needed

No existing imports were removed. The following explicit proof-plan dependencies
were removed from the item's `proof_deps`:

- `def-sbc-closed-immersion-ideal-sheaf`, represented by
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` / `AlgebraicGeometry.Scheme.Hom.ker`.
- `lem-weil-pbc-zero-locus-eq-iff-radical-eq`, represented by
  `Mathlib.RingTheory.Spectrum.Prime.Topology` / `PrimeSpectrum.zeroLocus_eq_iff`
  and the ideal radical lemmas listed in its Mathlib match.

They are not separately used by this proof: Mathlib's proved theorem on a surjective
closed immersion into a reduced target replaces the explicit affine ideal argument.
These Mathlib modules may still occur transitively inside Mathlib; this delivery does
not claim they leave the targets' import closure. No project module is newly pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The DAG's affine ideal argument was a
valid but unnecessarily long implementation route: the required isomorphism theorem
already exists in the pinned Mathlib. The local Stacks source file is absent on this
machine; the source paragraph and product formula were checked in the web edition of
[Stacks Tag 09NE](https://stacks.math.columbia.edu/tag/09NE).

## Second reading by F2

1. The delivered module was diffed against the repository version. The theorem
   signature and all existing declarations are unchanged; only its proof, docstring,
   and a proof-only import differ.
2. The module compiles with `lcompile.py`, contains no `sorry`, forbidden declaration,
   or hollow definition, and its proof uses only the permitted axioms. Empty-index and
   empty-open cases are covered by the finite-union and sheaf uniqueness arguments.
3. The existing node statement is unchanged. Its proof steps, dependencies, and origin
   now describe the Mathlib isomorphism and unique-gluing route; no new statement was
   split off and no existing library theorem is duplicated.
4. The proof follows the unit route: it constructs the disjoint open cover, identifies
   each restricted closed immersion as an isomorphism on the reduced target, and applies
   the structure-sheaf gluing theorem. The two affine ideal dependencies are pruned as
   recorded above.
5. The dry-run delivery checks were run after these edits; the only prior failure was
   this missing required section, which is now supplied. No further Lean or DAG change
   is needed.
