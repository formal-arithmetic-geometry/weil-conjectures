## What changed

Reduced AlgebraicGeometry.Etale.restrictedOverAbelianCocone_complex_data to one
strictly smaller coherence theorem in the new module
Sheaf.AlgebraicGeometry.RestrictedOverSingleCoherence. Its explicit definitions
construct the actual pullback diagram and cone, the degree-zero single complexes,
the transition isomorphisms, the constant apex diagram, and the inverse cone-leg
comparisons. No data are selected from an unproved existence theorem. The second reader
exposed the transition hom explicitly and uses asIso with a proved IsIso instance
for its unique inverse, avoiding expensive repeated kernel normalization.

The main proof establishes the limiting pullback cone, compactness,
quasi-separatedness, affine transitions, the zero lower bound, the constant
coefficient colimit, and the canonical derived-pullback formula. It assembles the
stage and apex cohomology equations from the supplied he and he₀.
Existing signatures, definitions, and public imports are unchanged.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.restrictedOverAbelianCocone_complex_data
(lem-sbc-restricted-over-abelian-complex-data).
Added and left: AlgebraicGeometry.Etale.restrictedOverSingle_coherence
(lem-sbc-restricted-over-single-coherence). This asserts only identity,
composition, and constant-diagram compatibility for explicit single-complex maps;
it has no cohomology, limit, qcqs, affineness, or continuity conclusion.
This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero holes. All constructions and the combining proof are complete.

## No longer needed

No module or existing import is pruned. The second reader removed three redundant
proof-only imports that the first draft added: Mathlib.CategoryTheory.Limits.Connected,
Mathlib.CategoryTheory.Filtered.Connected, and Mathlib.AlgebraicGeometry.Morphisms.Affine.
Their declarations and affine base-change instance are already available transitively. The old direct proof dependency
lem-weil-pbc-inverse-image-composition is replaced by
lem-sbc-restricted-over-single-coherence; inverse-image composition remains a
transitive dependency below that new node. The small etale site and connected
constant colimit dependencies remain used. No affine-preorder
coefficient-system modules are imported: their preorder interface does not apply
to an arbitrary cofiltered category. No continuity or module/abelian comparison
module is used by this construction.

## Where the brief, the DAG or earlier work was wrong

The existing affine coefficient helpers require a directed preorder and
nonnegative cohomology degree, whereas this item allows any small cofiltered
category and integer degree. They cannot be applied without additional reindexing.
The new construction works directly with the stated category and degree.
The coherence theorem uses equality/HEq parameters for the explicit constructions
so the constructor can use local abstract names without repeatedly unfolding
large inverse-image functors. With these parameters the constructor compiles
within the file time limit.

Edge cases: zero sheaves and empty test schemes preserve all functorial coherence
identities. The bound proof covers every negative term independently of q,
so negative cohomology degrees require no separate continuity assertion.
A cofiltered category is nonempty, ensuring the constant cocone is colimiting.
The unit record sk-lem-failure-field has no realized node for this item; no unit
statement or proof step was bypassed or modified.

## New nodes

lem-sbc-restricted-over-single-coherence records the explicit fixed-coefficient
single-complex coherence, sourced to the geometric construction in Stacks Tags
09Z1 and 0EZM. It provides real construction definitions and one open public
coherence theorem in Sheaf.AlgebraicGeometry.RestrictedOverSingleCoherence.
LeanFinder, Loogle, and grep searches found supporting comparisons but no complete
match; LeanSearch was unavailable (HTTP internal server error). Blueprint searches
for fixed sheaf and inverse-image composition found no matching blueprint node.
No change record is needed because existing public interfaces are unchanged.

## Second reading by V2

1. Compared the delivered item to the repository with diff and checked its theorem
   signature and all preceding declarations verbatim. Existing signatures,
   definitions, docstrings, and public imports are unchanged. The only additional
   module is the new coherence module. Verdict: pass; no interface change record
   is required.
2. Compiled both delivered modules locally with lcompile.py against the shared
   baseline and this delivery's helper. The revised helper compiled in 46.4 s and
   the item in 42.9 s, without errors or warnings. A scratch #print axioms check
   of the upper theorem and all seven declarations of the new module found only
   propext, Classical.choice and
   Quot.sound, with sorryAx only for restrictedOverSingle_coherence and the upper
   theorem depending on it. The six construction definitions have no sorryAx.
   No axiom, unsafe, opaque, implemented_by, extern, or definition hole occurs.
   Verdict: pass as a decomposition, not an unconditional proof.
3. Read the coherence theorem clause by clause against its construction and
   docstring. Its HEq parameters identify fixed explicit data rather than weaken
   a conclusion. Unit and associativity laws for upperStarComp, naturality, and
   the degree-zero single-functor comparison give the three equations. The cone
   equation cancels a cone-leg comparison with its inverse. Checked identity
   arrows, successive arrows, empty indexing categories, empty schemes and zero
   sheaves; no extra nonemptiness assumption is needed for coherence. The upper
   construction uses cofiltered nonemptiness only for the constant colimit.
   Fresh LeanFinder, Loogle and grep searches, and inspection of the upstream
   Coherence module and the restricted affine transition/cone modules, found
   supporting laws but no complete match for arbitrary category I. The affine
   variants require a preorder. This split omits the upper theorem's geometry,
   bounds, cohomology and colimit conclusions, and is strictly smaller.
   Verdict: pass. Search evidence is recorded in the new node.
4. Read the proof downward: its actual geometry, zero bound, connected constant
   colimit and cohomology square assembly are proved; only fixed-coefficient
   coherence remains open. No shorter existing applicable theorem was found.
   The new helper import is proof-only in the item. The helper's public import
   is needed by its definitions and signatures. Removed redundant newly added
   Mathlib imports. The removed direct inverse-image composition dependency is
   now listed explicitly above; it remains needed below the coherence node.
   The unit sk-lem-failure-field has empty realized statement/step lists, and
   no unit or chapter record or route was changed. Verdict: pass.
5. Compared both node files with the Lean. Each proof_deps is exactly the union
   of its proof steps' uses. The existing node changes only proof, proof_deps and
   proof_origin. The new node records the complete statement, source, docstring
   argument, searches, creation, blueprint origin, unit, chapter and Lean record.
   Its one named open theorem is exactly the one listed in this report.
   Verdict: pass.

Changes made in this second reading: exposed restrictedOverSingleIso's canonical
hom field explicitly and proved it is an isomorphism using the original explicit
comparison, then used asIso for its unique inverse. This is the same isomorphism,
with no unproved existence choice; it avoids repeated kernel normalization that
made the initial item exceed 60 s. Removed stale sandbox build artifacts for
EtaleComplexCohomologyPresentationData (not a delivered source), so all checks use
the shared baseline version of that module. Removed three redundant proof imports,
corrected the direct-dependency pruning report, and added fresh search evidence.
One upper hole is closed and one strictly smaller hole is added; net zero holes,
no modules pruned.
