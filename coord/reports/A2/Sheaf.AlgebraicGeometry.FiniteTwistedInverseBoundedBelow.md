## What changed

Proved `AlgebraicGeometry.finiteTwistedInverse_boundedBelow` in
`Sheaf.AlgebraicGeometry.FiniteTwistedInverseBoundedBelow`, with its signature unchanged.
Finite morphisms are affine, so the existing theorem
`schemeDerivedDirectImage_tExact_and_conservative_of_affine` supplies amplitude zero.
The proof constructs the quasi-coherent truncation A at n-1, transports its upper bound
through comparison, and uses adjunction and orthogonality to kill the truncation map.
Injectivity of composition with that map makes A zero; the truncation criterion gives
`(a.obj K).obj.IsGE n`, with the same witness n supplied by hK.

Two fully proved private helpers supply quasi-coherence of zero sheaves and preservation
of quasi-coherent cohomology by truncLE. No new public statement, definition, or module
was added. All original public imports remain. Proof-only imports now include affine
t-exactness, Adjunction.Additive, and the source-library right-derived
additivity instance. The node copy updates only proof, proof_deps, and proof_origin.

The sources were checked on the published Stacks pages:
[0A9I](https://stacks.math.columbia.edu/tag/0A9I),
[0AVW](https://stacks.math.columbia.edu/tag/0AVW), and
[08I8](https://stacks.math.columbia.edu/tag/08I8).
The unit record has empty realized statement/step lists. Its Serre-duality route is
unchanged: this proof only replaces the amplitude input inside this finite-case node.
LeanFinder, Loogle, and Mathlib grep found no direct right-adjoint boundedness theorem;
repository search found the usable affine theorem. Both new proof imports from the
project pass import_direction.py.

Local single-file compilation passes without warnings. The second reader runs the
required deliver3.py dry run and delivery after the review below.

## Proved and sorry left

Proved the module's only sorry:
`AlgebraicGeometry.finiteTwistedInverse_boundedBelow`
(lem-sc-finite-twisted-inverse-bounded-below).

No sorry remains in the item's module, and no sorry is added elsewhere.
The private helpers qcOfZero and qcTruncLE are completely proved.
The proof uses existing declarations and their recorded dependencies; it does not
claim that all transitive dependencies are already sorry-free.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound`.
The second reading also removed the redundant proof import
`Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`; the remaining imports
already provide the truncation API.
Node `lem-pc-derived-direct-image-uniform-truncation-bound` is no longer a dependency of
this proof. Its shifted bound, positive N, and stabilization clause are unnecessary here,
because f is affine. This is pruning from this item's proof only; other users may retain
that node and module. No other existing import or original proof dependency is removed:
`lem-pc-derived-tstructure-orthogonality` remains used through Mathlib's theorem.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable signature was found. The old DAG's general qcqs bound
was sufficient but unnecessarily broad for a finite morphism. The existing declaration
docstring retains that valid general proof plan; the updated node and actual Lean proof
specialize it to amplitude zero. The local clone does not contain the cited literature
source files or blueprint unit source file, so the Stacks argument was read from its
published pages and the unit from dag/units/sk-thm-picard-duality.json.


## Second reading by A2

1. Compared the entire delivered module and node with the repository versions.
   The existing theorem signature and docstring are byte for byte unchanged;
   no public definition, statement, or public import changed. The two new helpers
   are private, fully proved lemmas. Verdict: pass.
2. Read the proof top down and compiled the single file without errors or warnings.
   The truncation has quasi-coherent cohomology by the homology sequence; affine
   pushforward preserves its upper bound; additive adjunction and orthogonality
   kill the truncation map, and the truncation universal property kills its identity.
   The argument works also for zero objects, negative bounds, and n=0: it uses
   only n-1<n. There is no sorry or prohibited declaration in the delivered file.
   A scratch #print axioms of finiteTwistedInverse_boundedBelow reports exactly
   propext, Classical.choice, Quot.sound, and sorryAx (existing open dependencies).
   Verdict: pass; one module hole closed, zero holes added, not a decomposition.
3. No statements were split off, so no new holed statements or new nodes require
   truth, source, or duplicate checks. Reviewed both private helpers: the zero
   presentation is exact, and the two homology vanishings are in degrees i-1 and i,
   precisely those needed for the truncation cohomology isomorphism. Verdict: pass.
4. Repository searches and the recorded LeanFinder, Loogle, and Mathlib searches
   reveal no shorter existing boundedness theorem for this right adjoint. The
   affine amplitude-zero specialization is the shorter route here. Tested removal
   of every added proof import: TruncLEGT is redundant and was removed; the affine
   theorem, additive adjunction, and right-derived additivity imports are necessary.
   Original public imports supply the statement's data and bounds. The old uniform
   bound dependency is the only old proof dependency removed and is reported above;
   orthogonality remains used through Mathlib. The unit has empty realized lists;
   its Serre-duality statement and route are unchanged. Verdict: pass after pruning.
5. The only changed node fields are proof, proof_deps, and proof_origin. Read every
   updated step against the Lean argument; their uses have exactly the recorded
   proof_deps union. The affine theorem's first component supplies the bound used;
   its conservativity component is not needed. No new node or change record is
   necessary. Verdict: pass.

Second reading changed only the redundant TruncLEGT proof import and this report.
The mathematical proof was retained.
