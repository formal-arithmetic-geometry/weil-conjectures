## What changed

The assigned theorem `resolutionSectionClass_map_smulHom` is reduced without changing
its signature. Its proof uses two new proof-only imports:
`Sheaf.AlgebraicGeometry.ResolutionScalarAction` and
`Sheaf.AlgebraicGeometry.ResolutionSectionsHomologyScalar`.
The first proves the action of multiplication on module-valued derived global sections.
The second isolates the semilinearity of the pinned restricted section homology comparison.
The original theorem composes these with the linear module-valued resolution comparison,
`sectionCohomologyTheta`, and the inverse higher-direct-image resolution comparison.
All existing public imports remain necessary to the original signature.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_map_smulHom`
(node `lem-pc-resolution-section-scalar-map`). This is a decomposition, not a net hole reduction.

Also proved without sorry:
`AlgebraicGeometry.Scheme.Modules.moduleCohomology_map_smulHom`
(node `lem-pc-resolution-scalar-action`). Its proof constructs the termwise multiplication
endomorphism, applies `isoRightDerivedObj_hom_naturality`, computes its homology using
`ShortComplex.homologyMap_smul`, and cancels the linear resolution isomorphism.

Added hole:
`AlgebraicGeometry.Scheme.Modules.resolutionSectionsHomology_scalar`
(node `lem-pc-resolution-sections-homology-scalar`). This concerns only the three middle
section-homology arrows, before theta, with arbitrary resolution-homology input.
Its docstring specifies the complete degreewise semilinearity argument and passage to homology.
No sorry remains in the assigned module. No definitions or existing signatures changed. Elaboration options are scoped to the assigned theorem.

## No longer needed

No import removed from the assigned module: both original public imports are used in its
theorem signature. In the new ResolutionScalarAction module, removed the unnecessarily
broad public FlatBaseChangeOpenChoices import. Its signature needs only
RingedSpaceModuleCohomology and Cohomology.Defs; SchemeModulesEnoughInjectives is
a proof-only import. No existing reachable module is thereby pruned.
The original proof's comparison of two lifts by homotopy and its use of
`R.augmentation` are no longer needed. Multiplication acts directly on module-valued
cohomology. `def-sp-injective-resolutions` and `lem-sp-derived-well-defined` remain
needed transitively for this directly proved scalar action, so neither entire module
nor node is claimed pruned. The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned homotopy argument is unnecessary. Module-valued derived global sections
allow a direct calculation of the scalar endomorphism, while the difficult step is
semilinearity of the degreewise pinned section identification on homology.
The final composition uses explicit local names and identifies the forgotten additive
composite once before rewriting its four scalar identities, to avoid repeatedly
unfolding sheafification.
Small cases of the new statements: degree zero is ordinary scalar compatibility;
empty opens and zero modules give the same identity on zero objects. No affineness,
quasi-coherence, finiteness, or vanishing hypothesis enters either new statement.
Sources read: [Stacks Tag 01E4](https://stacks.math.columbia.edu/tag/01E4), identifying higher direct images with sheafified section cohomology, and [Tag 01E5](https://stacks.math.columbia.edu/tag/01E5), computing restriction using the restricted resolution. The scalar arguments are explicit consequences of the module maps in these constructions.

LeanFinder, Loogle, and grep searches were run and logged; LeanSearch returned HTTP 500,
recorded as unavailable. There was no exact existing normalized section transport result.

## New nodes

`lem-pc-resolution-scalar-action`, module `ResolutionScalarAction`, records the proved
scalar endomorphism computation on derived global sections.

`lem-pc-resolution-sections-homology-scalar`, module `ResolutionSectionsHomologyScalar`,
records the remaining semilinearity of the three middle section homology arrows.
It is strictly part of the argument and makes no assertion about the final class map.
The assigned node's proof, proof dependencies, and proof origin now follow the Lean proof.
No change record is necessary because no existing statement or definition changed.

## Second reading by Q3

1. Compared all delivered modules with the repository using diff and the declaration
   parser. The assigned theorem signature is byte for byte unchanged; the other two
   modules are new. No existing definition, public import, or target changed. Verdict: pass.
2. Compiled the three modules locally in import order. The only sorry is the named
   resolutionSectionsHomology_scalar. No forbidden declaration or hollow definition
   occurs. A scratch #print axioms check showed only propext, Classical.choice and
   Quot.sound for moduleCohomology_map_smulHom; the target and the split lemma also
   use sorryAx, as reported. Verdict: valid decomposition, not a completed target proof.
3. Read R.components and the definition of resolutionSectionClass. The split lemma
   asserts semilinearity only of the middle three homology arrows, without theta,
   derived cohomology, or the higher-direct-image comparison. Its degreewise maps
   preserve the pulled-back scalar; passing to cycles and their quotient preserves
   this identity. Degree zero, empty opens, zero modules, and scalars zero and one
   introduce no exception. The docstring gives this complete argument with sources.
   Read Stacks 01E4 and 01E5. Independent LeanFinder, Loogle and grep searches on
   restriction of scalars and homology comparisons found general naturality lemmas,
   but no existing normalized section transport theorem. Upstream affine and Ext
   comparisons have different objects or additional hypotheses. Verdict: true,
   strictly intermediate, and needed; not a restatement. Closing it requires the
   degreewise ring-map normalization and transport through forgetful homology,
   beyond a short application of the searched general lemmas.
4. Read the derived scalar action proof and the target's four-step composition.
   Both use the direct route rather than comparing two resolution lifts. Pruned
   the broad import of FlatBaseChangeOpenChoices from the new scalar-action module,
   retaining the two signature imports and making enough injectives proof-only.
   The old def-sp-injective-resolutions and lem-sp-derived-well-defined dependencies
   cease to be direct dependencies of the target but remain used transitively by
   scalar action. No entire old dependency node is claimed pruned. sk-thm-p1's
   realized statement and steps are unchanged and none is bypassed. Verdict: pass.
5. Checked all three DAG signatures against Lean and the required fields of the new
   nodes. Corrected the scalar-action node to cite ringed-space module cohomology,
   resolution naturality, and scheme-module enough injectives, rather than the
   unrelated open-choice definition. Removed resolution independence from the
   homology-transport node's proof dependencies: its degreewise argument needs
   only the pinned open-choice data and elementary homology functoriality.
   The assigned node follows the actual composition. Verdict: pass after repair.

Changed import scope, the two new nodes' dependency records, and this report.
After the submission compile exceeded 60 seconds, simplified the target proof by
identifying its composite once and rewriting the four scalar identities directly;
removed the redundant forgotten-map aliases and unused hqx. The repaired proof
compiled in 36.5 seconds without changing its signature or dependencies.
One original hole closed, one lower hole added; net hole reduction zero. The new
scalar-action theorem is independently proved with standard axioms only.
