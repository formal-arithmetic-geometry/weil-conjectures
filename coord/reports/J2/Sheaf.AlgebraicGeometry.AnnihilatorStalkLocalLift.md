## What changed

Proved `AlgebraicGeometry.annihilator_stalk_local_lift` with its existing signature,
docstring and public imports unchanged. Added proof-only imports of
`AnnihilatorAffineCriterion`, `ClosedImmersion`, and
`import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
The last import makes the existing proved private theorem
`AlgebraicGeometry.Scheme.Modules.finite_sections_of_finiteType` available; it
supplies finite generation directly, without duplicating a restriction helper.
No definition, public visibility or module interface changed.

Represent the germ on an affine neighborhood. The finite-type ideal has finitely
many spanning sections there. Each generator kills the germ, so germ equality
supplies a neighborhood on which it kills the representative. Shrink to an affine
neighborhood inside their finite intersection. The ideal extension formula along
affine restrictions gives annihilation by the entire ideal there; the proved affine
annihilation criterion extends this to every subopen. Updated the DAG route accordingly.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.annihilator_stalk_local_lift`
(node `lem-weil-pbc-annihilator-stalk-local-lift`). Added zero holes and zero new
nodes. No `sorry` remains in the delivered module. This is a complete proof, not
a decomposition. Both the delivered theorem and the imported finite-sections
helper have only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

## No longer needed

No original public import was removed. All five unused original proof dependencies
are removed from this node's `proof_deps`:

- `lem-weil-pbc-affine-tilde-gamma-adjunction`;
- `lem-weil-pbc-spec-tilde-stalk-localization`;
- `lem-weil-pbc-affine-open-stalk-localization`;
- `def-weil-pbc-module-localization`;
- `lem-weil-pbc-spec-module-tilde-sections`.

These are direct dependency prunings, not a claim that their modules are globally
unreachable. Some associated Mathlib modules remain transitively imported.
The affine annihilation criterion remains a used dependency.

The second reader additionally removed the first worker's proof-only
`FiniteTypeModuleSupportClosed` import and the corresponding
`lem-weil-pbc-finite-type-module-support-closed` dependency. Its private
`isFiniteType_over` helper is unnecessary because the existing finite-sections
helper applies directly. The earlier copied restriction helper is not delivered.
The direct `QuasicoherentKernel` import is unnecessary because `ClosedImmersion`
publicly imports it. No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original localization route is valid but finite intersections of germ-vanishing
neighborhoods give a shorter argument. The final affine-cover argument is supplied
by the already proved `annihilator_affine_criterion`.
`SectionsAnnihilatedByIdeal` imports this item and cannot be used as a shortcut.

The earlier delivery was returned for copying a finite-type restriction helper.
The worker's repair reused the existing private helper with `import all`.
This second reading found a still shorter existing helper in the already required
affine finite-type module, eliminating the restriction step and the support import.
No existing module needs adaptation and no change record is needed.

The generic closed-immersion quasi-coherence theorem is recorded among the
declarations of `lem-pc-closed-immersion-coherent-cohomology`. Its actual signature
requires no Noetherian or finite-presentation assumption. This proof uses that
proved quasi-coherence tool, not the stronger coherent/cohomological conclusion
of the node. The quasi-coherent kernel theorem is also proved.

## Second reading by J2

1. Compared the sole delivered module with the repository version using `diff`,
   and compared the complete theorem signature byte for byte. Verdict: identical
   universes, binders, hypotheses, conclusion, visibility, public imports and
   existing docstring; no data definitions or interfaces changed. Read
   [Stacks Tag 01PO](https://stacks.math.columbia.edu/tag/01PO), particularly (3)
   and its omitted argument. `Scheme.IdealSheafData` supplies the quasi-coherent
   ideal, its module is assumed finite type, and `F` is assumed quasi-coherent.
   The annihilation hypothesis applies to every ideal-section germ at `x`;
   the conclusion is the local representative needed for (3), including
   annihilation on every subopen. No extra hypothesis was introduced.
2. Compiled the worker's module and the repaired module with `lcompile.py`, with
   no errors or warnings. Scratch copies with `#print axioms` showed exactly
   `propext`, `Classical.choice`, `Quot.sound` for the delivered theorem and for
   the imported private finite-sections helper; the former restriction helper
   was checked too before removal. Scanned the delivered module: no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Verdict: a complete
   kernel-checked proof, with no hollow definition or arbitrary witness chosen
   from an unproved existence theorem. The neighborhood and generator witnesses
   all come from proved results.
3. No statement is split off; no new declaration or node is delivered. Checked
   the argument for zero ideal (empty finite intersection is top), unit ideal
   (the germ is zero), zero module and zero germ. The point already excludes an
   empty scheme, without an added hypothesis. Verdict: sound in these cases.
   Repeated searches with different wording through msearch: grep
   `exists.*germ.*zero|germ_eq.*zero|finite_sections_of_finiteType|IsFiniteType.*over`
   returned ringed-space germ APIs; Loogle `TopCat.Presheaf.germ_eq` returned the
   exact neighborhood-equality theorem; LeanFinder's query about local annihilation
   of a module-sheaf germ returned germ and local-generator APIs, with no complete
   lifting theorem. Repository/upstream searches for annihilation, germ vanishing,
   and finite-section helpers found no complete upstream replacement, but found
   the existing private `finite_sections_of_finiteType` used in the repair.
4. Read the proof top downward. Germ representation and restriction preserve `s`.
   Closed-immersion pushforward and the kernel theorem give quasi-coherence of
   `J.toModules`, so the finite-sections helper applies with exactly its existing
   finite-type hypothesis. Mapping a finite span through the ideal inclusion
   gives generators of `J(U)`. Each generator lies in the ideal and hence has
   zero product germ by `hs`; `germ_eq` and `map_smul` give local vanishing.
   The finite intersection contains `x`; choosing an affine open inside it does
   not assume intersections of affine opens are affine. Restriction kills all
   generators, and `J.map_ideal` plus the map/comap adjunction places all of `J(Z)`
   in the kernel ideal. The affine criterion gives precisely all-subopen
   annihilation, and germ restriction gives the original germ. Verdict: correct.
   Removed the separate finite-type restriction step and its support-module
   import, reusing the proved finite-sections helper by proof-only `import all`.
   Each remaining import supplies a signature type or a theorem used in this
   proof. Compared the old dependency list with No longer needed: all five
   discarded dependencies are listed. Read `dag/units/sk-thm-p1.json` and its
   `realized` statement and steps: this node realizes none of them, so the shorter
   argument changes only this auxiliary node's route.
5. Compared the node JSON with the repository: only `proof`, `proof_deps`, and
   `proof_origin` differ. The dependency list equals the union of step `uses`.
   Read the kernel and closed-immersion quasi-coherence theorem signatures,
   `finite_sections_of_finiteType` and its proof, and the affine annihilation
   criterion. Verdict: these proved declarations give exactly the facts the
   Lean proof takes; no unsupported Noetherian or coherence assumption enters.
   Updated step 1 and the dependency list to remove the support-module helper
   and describe direct finite generation; updated proof origin. No new node
   fields or change records are required.

Second reading changed the finite-generation reduction, its proof-only imports,
the matching DAG route, and this report. The remaining proof was retained.
Closed one original hole and added zero holes.
