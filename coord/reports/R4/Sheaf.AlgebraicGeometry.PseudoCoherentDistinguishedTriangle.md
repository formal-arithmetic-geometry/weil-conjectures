## What changed

Proved `AlgebraicGeometry.Scheme.isPseudoCoherent_of_distinguished_triangle` with its
signature and public imports unchanged. The proof follows the affine route of Tag 08CD:
common affine neighbourhood, restriction of the two models, explicit termwise sections
models, K-projective lifting of the inverse-rotated arrow, triangle comparison and the
finite-free mapping cone. Four private helpers are proved completely in the item's module:
`restrict_finiteFree_model`, `finiteFree_mappingCone`, `affine_finiteFree_module_model`, and
`affine_finiteFree_map_representative`.

Used the existing full affine derived sheafification interface from
`Sheaf.AlgebraicGeometry.AffineLocalizedDerivedSheafification`, the existing K-projective
chain-map representative lemma, the module-projectivity API, and the existing
`Modules.overEquivFunctorObjUnitIso`. All added imports are proof-only.
The DAG proof and dependencies now describe these actual constructions.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.isPseudoCoherent_of_distinguished_triangle`
(node `lem-pc-pseudo-coherent-distinguished-triangle`).
Added 0 holes. No declaration in the delivered module contains `sorry`.
This is a proof from existing library interfaces; the imported affine derived
sheafification interface continues to carry its existing proof dependencies.
No definitions or statements were changed.

The common-neighbourhood proof uses no assumption that the intersection itself is affine.
The cone degree calculation covers unbounded-below complexes, zero ranks, empty affine
opens, and independent upper bounds. The sections complex is built termwise by an actual
functor. No arbitrary existence witness is used as data of a definition.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
The full theorem `AlgebraicGeometry.exists_affineQCohDerivedEquivalence` and its node
`lem-pc-affine-qcoh-derived-equivalence` are no longer direct dependencies of this proof.
The smaller existing `lem-pc-affine-localized-derived-sheafification` interface supplies
fullness and the natural comparison required here, via the affine equivalence core.
Consequently the full equivalence's extra shift-object comparison is not needed here.
The K-projective and triangulated-category dependencies of the planned argument remain.
No blueprint-unit statement or step is bypassed: this unit's `realized` lists are empty.

## Where the brief, the DAG or earlier work was wrong

The plan correctly identifies the mathematical route, but the finite-free affine model
and chain-map lifting steps require actual constructions and comparison naturality.
They are now supplied by the proved private helpers. The existing perfect-model helper
has a lower-bound hypothesis, so it cannot be applied directly to pseudo-coherent models.
Its termwise affine sections argument extends to bounded-above finite-free complexes;
only an upper bound is needed for K-projectivity, and this proof writes that extension.

The local Stacks TeX file named by the node is absent on this machine. The source was read
at https://stacks.math.columbia.edu/tag/08CD; the existing library's affine sections-model
and derived-sheafification declarations were read in full. No source or tool was changed.

## Second reading by R4

1. Compared the entire delivered module with the repository version and checked the
   existing theorem signature byte for byte. It is identical; the only public import
   remains `PseudoCoherentComplex`. No definition or existing declaration visibility
   changed, and there are no change records or adapted modules. Verdict: pass.
2. Compiled the module locally with `lcompile.py`: clean, without warnings. Scanned
   the source for `sorry`, axioms, unsafe/opaque declarations and implementation escapes:
   none occur. The scratch-copy `#print axioms` check of the target reports only
   `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`; thus the local
   hole is closed, while existing imported proof obligations remain. The restriction,
   cone, and sections-model helpers use only the three standard axioms; inherited
   sorryAx first appears in the affine chain-map representative helper. The module model
   is the actual termwise sections construction, not data chosen from an unproved
   existence theorem. The full functor's existential witness is used only inside a
   theorem proof. Verdict: pass.
3. No statements were split off and no holes were added. Read all four completely
   proved private helpers. Restriction preserves the original bound; the shifted
   complex has bound N+1; the cone has terms C[i] plus A[i], so its bound is the
   maximum of their independent bounds. Finite-basis reindexing also covers rank
   zero, and no argument needs a lower bound or a nonempty affine open. Verdict: pass.
4. Read the proof top down, the affine model and representative APIs, and the unit
   record. Repeated LeanFinder with “bounded above finite free sheaf complexes on an
   affine scheme closed under distinguished triangles”, and searched the library and
   Mathlib by pseudo-coherence, cone, and representative terminology. No shorter
   scheme-level replacement was found; the existing perfect-model API imposes a
   lower bound. Counterfactual compiles without the projectivity import and without
   the upstream sheaf import fail at their used declarations, confirming they are
   needed. The other proof imports supply full affine sheafification and chain-map
   representatives. The sole old dependency removed is fully listed under
   “No longer needed”. The unit's realized statement and step lists are empty; the
   affine/K-projective/cone route is retained. Checked the mathematical sources at
   https://stacks.math.columbia.edu/tag/08CD and
   https://stacks.math.columbia.edu/tag/06Z0. Verdict: pass.
5. Compared the node against the original: only proof, proof_deps and proof_origin
   differ. Its five steps describe the actual constructions and their dependencies;
   the representative helper uses the upstream proved exists_Q_map_eq consequence
   of the recorded Qh_map_bijective Mathlib leaf. No new node is needed for an open
   statement, because there are no new open statements. Verdict: pass.

Second-reading changes: removed two whitespace-only blank lines in the private
affine module-model proof and added this review record. No mathematical repair was
necessary. The blueprint unit's source markdown is absent on this machine; its
complete statement and steps were read from dag/units/sk-thm-picard-duality.json.
