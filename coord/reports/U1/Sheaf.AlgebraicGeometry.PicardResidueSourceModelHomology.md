## What changed

Closed AlgebraicGeometry.Scheme.picard_residue_source_model_homology using the actual
terminal section complex. Sections take the finite free retractions to projective
modules, hence flat modules; the support bound makes this complex K-flat. A proved
private affine reconstruction helper uses affine_perfect_module_model and the
existing private chart-section isomorphism. The affine K-flat residue model and
scalar transport then compute the derived fibre. Exact sections over the field
spectrum and the tilde/sections unit supply the final linear homology equivalence.

The chart/slice equivalence is a concrete private definition with forward and
inverse equations. This avoids repeating its large unit/counit expression in
complex comparisons. Composed functors use explicit complex-composition
isomorphisms. Existing theorem signatures are unchanged. The unused public quotient import
is removed with a change record covering all 171 downstream users. The node's proof route,
proof dependencies and proof origin now describe this Lean argument.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.picard_residue_source_model_homology
(node new-picard-residue-source-model-homology), one of one original holes.

Added holes: none. Split off: none. No sorry remains in the delivered module.
All new private lemmas are proved and the chart equivalence has actual constructed
data. Imported theorem dependencies remain the project's existing obligations;
this delivery makes no claim that their transitive axiom closure is already closed.

## No longer needed

Removed public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology, unused
by this statement and proof. Its direct importer already publicly imports the
quotient API, so no downstream adaptation is needed. The change record is
coord/changes/picard-residue-source-model-homology-imports.md.

No new intermediate statement or module is needed. The bounded finite free
cohomology/derived-model theorems are not imported: the strictly perfect hypothesis
permits nonfree projective retracts and the proof handles them directly. In
particular AffineFreeResidueSectionsCohomology and
AffineFreeResidueSectionsDerivedModel are not dependencies of this proof.

The explicit quotient construction AffineResidueCycleHomology and its two nodes
lem-sc-affine-residue-cycle-class-quotient and lem-sc-affine-residue-cycle-homology-map
are not used by the model-homology proof; they remain needed by the separate quotient
comparison above this item. No claim is made that these modules leave the target
closure.

## Where the brief, the DAG or earlier work was wrong

The original node had one non-elementary prose step with an empty proof-dependency
list. The updated proof supplies the actual affine K-flat model and scalar-transport
dependencies and spells out the reconstruction and exact-homology comparisons.
The existing finite free residue-section comparison is not directly applicable:
strictly perfect terms are finite free retracts, not necessarily free modules.

The unit sk-prop-av-cube has no realized node entries for this item; its cube theorem
route is unchanged. The affine perfect-module model from sk-thm-picard-duality is
used as a tool only for its essential-image assertion, not to replace the cube
unit's route. The chart-sections private helper in
AffineFreeTerminalSectionsReconstruction is reused through a proof-only import all.

Sources read: Stacks Project Tags 01IB, 064K, 06YJ, 0098 and 010V (web pages,
local literature is absent on this machine). Search: leanfinder on the geometric
residue comparison returned ordinary residue/fibre lemmas, no exact comparison;
Loogle on CategoryTheory.Retract returned generic retract APIs; msearch grep on
affinePerfectSheafification and terminalSections_reconstruction returned no hits.
Repository rg found and the worker read the existing affine free comparison,
affine perfect module model, affine K-flat residue model and scalar-transport files.
LeanSearch was unavailable (Internal Server Error), recorded by msearch.

Edge cases: zero complex and rank-zero retracts use the same zero-object and
projectivity arguments. Nonfree projective terms are retained; no local free frame
is assumed. No differential is assumed zero. The empty open has no point satisfying
hwU, so no extra inhabitedness assumption is introduced.

Validation: the complete delivered module compiled without errors or warnings
in 57.3 seconds using lcompile.py; the delivery dry run checks it again with
the axiom and direct-hole probe. No global build was run by this worker.

## Second reading by U1

1. PASS: Compared the sole delivered module and its node with the read-only
repository using diff. The existing theorem signature is byte for byte identical,
including universes, both derived-category instance families, hK, hE, and the
terminal-section/scalar-extension conclusion. No existing definition is altered.
The only public-import removal has its change record. Repository-wide rg confirms
that the sole direct importer is PicardResidueHomologySourceResidueComparison,
which itself publicly imports AffineResidueCycleHomology. Downstream signatures
and available quotient declarations therefore retain their meanings.

2. PASS: Independently compiled the complete module with lcompile.py (49.8 seconds,
no errors or warnings). There is no sorry, axiom, unsafe, opaque, implemented_by,
extern, or kernel-check bypass in the delivered source. Read both new equivalence
constructions: all functors and unit/counit maps are explicit. The existential
model P is eliminated only inside a theorem proof to prove counit invertibility;
the section complex P₀ is constructed directly by evaluation of K. No arbitrary
witness from an open existence theorem becomes definition data. A scratch copy
printed axioms of the main theorem and every new private declaration (47.8 seconds,
clean): each depends only on propext, Classical.choice, and Quot.sound. In
particular the main theorem has no transitive sorryAx in the compiled baseline.

3. PASS: No statements are split off and no holes are added. Read the proved
private reconstruction and the imported affine perfect model, chart-section
comparison, K-flat residue model, and scalar transport statements/proofs.
Evaluation preserves retractions and zero terms; finite free sections are free,
so retract section terms are projective and flat. The upper support bound is
sufficient for K-flatness. The counit is invertible on each term in the left
adjoint's essential image, and naturality supplies the complex isomorphism.
Zero complexes, rank-zero terms, nonfree projective retracts, and nonzero
differentials satisfy the same argument. Empty U supplies no point hwU.

4. PASS: Repeated repository searches using terminal-section reconstruction,
residue model homology, and strictly perfect complexes, and an independent
LeanFinder query on derived pullback homology of projective affine complexes.
The returned generic pullback/projective APIs do not prove this comparison.
The existing affine free cohomology/derived-model theorems require actual free
terms, a stronger hypothesis than the retract condition here. The proof uses the
existing K-flat model and scalar transport without new intermediate obligations.
Proof-only imports are ordinary import (the private helper uses import all).
The removed quotient import is fully listed above. The original proof_deps was
empty, so there are no omitted old dependency nodes to prune. Read
sk-prop-av-cube.json: its realized statement and step lists are empty and this
local comparison does not replace its cube-theorem step. The affine perfect
module model is a generic reconstruction tool.

5. PASS: The changed node fields are restricted to proof, proof_deps, and
proof_origin; its Lean signature and statement are unchanged. The dependency
list is the union of the proof steps' uses and matches the Lean route, including
the private chart-section helper from the free reconstruction module. No new
node or change of a unit record is required.

Changes by the second reader: restored the existing theorem's original docstring
verbatim, preserving its API documentation; the worker's proof explanation
remains in this report and the node. No proof or statement repair was needed.
