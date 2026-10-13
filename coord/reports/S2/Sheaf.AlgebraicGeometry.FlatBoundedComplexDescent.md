## What changed

Removed the duplicate `flatOver_of_iso` helper from the item. Its single existing proof
in the new `PullbackModelFlatnessComparison` module is now public, and the item imports
that module privately and applies its theorem at both call sites. This repairs the
import-pruning return by reusing one declaration rather than repeating its proof.
The item node now records this direct proof dependency.

The existing `AlgebraicGeometry.flat_bounded_complex_descent` proof remains a complete Lean
assembly without changing its signature or existing documentation. The proof applies
finite-presentation complex descent, obtains eventual flatness thresholds for the fixed
terms, chooses a common stage over the finite interval by directedness, handles zero
terms outside the interval, and composes the termwise comparison isomorphisms using
naturality. Four new modules make the missing interface glue explicit; all four are
proved, with no added sorry.

## Proved and sorry left

Closed: `AlgebraicGeometry.flat_bounded_complex_descent` (one original hole).
Also proved: `AlgebraicGeometry.exists_bounded_complex_baseChange_enlargement` and
`AlgebraicGeometry.exists_eventually_isFlatOver_staged_module`.

Also proved: `AlgebraicGeometry.isFlatOver_tensorPullback_iff_of_isPullback` and
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorPullback`.

Added holes: none. No sorry remains in any delivered module or definition.
This closes one original hole with no lower holes added. The existing
finite-presentation complex descent and flat module descent remain needed and holed;
no claim of an axiom-free target proof is made. The new proofs cover zero modules,
empty schemes, and degenerate bounded intervals. Every delivered module compiles
with lcompile.py; the delivery dry run checks the declarations and DAG mechanically.

## No longer needed

Removed the item's duplicate `flatOver_of_iso` helper and its proof. Both uses now
refer to the imported theorem in `PullbackModelFlatnessComparison`.

Removed the item's direct proof import `Sheaf.AlgebraicGeometry.FlatModuleDescent`.
Its theorem and node `lem-pc-flat-module-descent` remain needed through
`StagedModuleEventualFlatness`; this is an import relocation, not closure pruning.
The old direct dependency `lem-pc-flat-module-descent` is replaced in the item node
by `lem-pc-staged-module-eventual-flatness`, but remains a transitive dependency.
No original proof-dependency node or module is pruned. All other original imports are
retained; the new proof imports are used. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned common-stage argument is mathematically correct. The original interfaces
omit explicit glue for comparing an iterated pullback with the chosen direct pullback
and preserving finite presentation under tensor pullback. These are now proved in separate reusable
modules rather than reselecting descended modules, which would lose the shared differentials.
The Stacks source files are not populated on this machine. The relevant official
statements and proofs were read at https://stacks.math.columbia.edu/tag/05LY,
https://stacks.math.columbia.edu/tag/01BQ, https://stacks.math.columbia.edu/tag/01JX
and https://stacks.math.columbia.edu/tag/0097. Existing signatures are unchanged.

## New nodes

`lem-pc-tensor-pullback-finite-presentation`, module `TensorPullbackFinitePresentation`:
proved finite-presentation preservation by transfer from the upstream pullback instance; a single module and arbitrary scheme
morphism, with no complex or limit involved.

`lem-pc-pullback-model-flatness-comparison`, module `PullbackModelFlatnessComparison`:
proved relative flatness comparison for two fixed cartesian models, with no descent assertion.

`lem-pc-bounded-complex-base-change-enlargement`, module
`BoundedComplexBaseChangeEnlargement`: proved functorial transport of a fixed complex
along specified maps, with no flatness or stage selection.

`lem-pc-staged-module-eventual-flatness`, module `StagedModuleEventualFlatness`:
proved from the existing eventual-flatness descent and the cartesian-model comparison,
with a fixed module and every stage beyond the threshold.

No change record is needed: the visibility adjustment is in a new delivered module;
no existing library definition, statement, or visibility changes.
The second reading simplified the new finite-presentation proof to the upstream
`isFinitePresentation_pullback` instance transported through uniqueness of left adjoints.
It removed three proof imports (PullbackFree, Preserves.Shapes.Over, Sites.Spaces)
from that new module and added a plain proof import of Modules.FiniteDescent.
In the new comparison module it replaced public BaseChangeConventions with public
TensorPullback, which is what the signature uses.


## Earlier second reading (a previous round; superseded)

1. Compared every delivered file with the repository baseline. Only the item module
   existed there. Its theorem signature and documentation are byte-for-byte unchanged;
   the edits are its proof, private proved helpers, and plain proof imports. The four
   other modules are new proved lemmas. No definition, target statement, or existing
   visibility changed, so no change record or forced adaptation is required. Verdict: pass.
2. Independently compiled all five modules through lcompile.py with no warnings or
   errors. Scanned the delivered Lean for sorry and forbidden declarations: none.
   Read the explicit construction of the enlarged complex via mapHomologicalComplex;
   it uses no arbitrary data chosen from an unproved existence theorem. New private
   definitions in the initial finite-presentation proof were concrete constructions;
   the shorter final proof removes them. Scratch #print axioms checks and the delivery
   axiom probe verify the permitted axioms, allowing sorryAx only for imported open
   results. Verdict: pass; imported descent holes remain, as reported above.
3. Read all four new statements, proofs, docstrings, and full nodes. They are strictly
   narrower ingredients, not restatements: one module under arbitrary pullback, flatness
   for two fixed cartesian models, transport of a fixed complex, and eventual flatness
   of a fixed staged module. Zero modules, empty schemes, j=i, and an empty bounded
   interval introduce no extra hypothesis or lost conclusion. No new hole is split off.
   Repeated searches with inverse-image/extension-of-scalars wording, Module.Flat.equiv_iff,
   and repository rg found the proved upstream isFinitePresentation_pullback instance.
   Used it with Adjunction.leftAdjointUniq and isFinitePresentation_of_iso to shorten
   the new tensor-pullback finite-presentation proof. Verdict: pass after simplification.
4. Read top-down: finite-presentation descent fixes H and its differentials; flat module
   descent gives thresholds for those fixed terms; finite directedness chooses k;
   zero-object preservation handles degrees outside Icc a b; enlargement constructs K;
   naturality composes the differential comparisons. No reselected descended module
   loses its differential. Every remaining proof import has a use; no proof-only public
   import remains in the new modules. The unit sk-thm-picard-semicon has empty realized
   slots, and none is altered or bypassed. Both original dependency nodes remain used
   transitively, so no original closure module is pruned. Verdict: pass.
5. Checked all five node records against the final Lean signatures, named theorem uses,
   proof steps, dependencies, source, creation records, searches, chapter and unit.
   Updated the finite-presentation node's proof to the upstream-instance transfer.
   The item depends directly on finite-presentation complex descent, staged eventual
   flatness, and complex enlargement, matching the final proof. The staged lemma retains
   flat module descent. Verdict: pass.

Changed in second reading: shortened TensorPullbackFinitePresentation by replacing
its slice-site construction with the proved upstream pullback preservation instance;
updated its DAG proof; replaced the new comparison module's unnecessary public
BaseChangeConventions import by TensorPullback; clarified the report. No signatures
changed and no holes were added.


## Second reading by S2

1. Interface comparison: diffed the existing item against the repository and checked
   its complete theorem signature byte for byte. It is unchanged, including all
   hypotheses and the differential-compatibility conclusion. All four other modules
   are new; no existing definition or visibility is changed. The existing node differs
   only in proof, proof_deps and proof_origin. Verdict: pass.
2. Proof checking: independently compiled all five modules with lcompile.py, without
   errors or warnings, and scanned every delivered source for sorry and forbidden
   declarations. None occurs. Scratch copies with #print axioms show only propext,
   Classical.choice and Quot.sound for finite-presentation preservation, complex
   enlargement, module-isomorphism flatness transfer and cartesian-model comparison.
   The main theorem and staged-flatness lemma additionally use sorryAx from imported
   open descent theorems. K is explicitly constructed by mapHomologicalComplex; no
   definition chooses arbitrary data from a holed existence theorem. Verdict: pass.
3. New statements: read each signature, proof, docstring and full node. No new sorry
   is split off. The four proved ingredients concern arbitrary tensor pullback, two
   fixed cartesian models, one fixed complex and one fixed staged module respectively;
   none restates the item. Checked zero modules, empty schemes, identity stage maps,
   and a>b: an empty Icc gives k=j and every term is handled by the zero branch.
   Repeated leanfinder searches with module/source-isomorphism wording, loogle search
   for adjoint uniqueness, and grep/rg searches for IsFlatOver and complex mapping.
   The upstream isFinitePresentation_pullback proof is already reused. Existing
   flatness-transfer helpers in FlatOverAffineOpenRestriction are private and cannot
   replace the public reusable transfer here. Verdict: pass.
4. Route and pruning: read the two imported descent statements. Finite-presentation
   descent fixes H and its differentials; eventual flatness at j applies to those
   same terms, not replacement models. The common finite upper bound and zero terms
   give flatness of the concrete pullback complex. Cone compatibility and naturality
   give the required equation for every differential. Read official Stacks Tags
   [05LY](https://stacks.math.columbia.edu/tag/05LY),
   [01BQ](https://stacks.math.columbia.edu/tag/01BQ),
   [01JX](https://stacks.math.columbia.edu/tag/01JX) and
   [0097](https://stacks.math.columbia.edu/tag/0097): they support the cited descent,
   finite-presentation preservation, base-change convention and composition arguments.
   All new proof imports are plain imports; public imports supply signature notions.
   Both old proof dependencies remain in the closure, with flat module descent now
   reached through StagedModuleEventualFlatness. No module is pruned. The unchanged
   unit record has empty realized slots; its route is neither replaced nor bypassed.
   Verdict: pass.
5. DAG consistency: verified each new node's Lean signature verbatim, creation fields,
   source, searches, chapter and unit, and compared the proof steps with the code.
   The item now directly uses four nodes: finite-presentation complex descent,
   staged-module eventual flatness, bounded-complex enlargement and cartesian-model
   flatness comparison (the latter also supplies flatOver_of_iso). The staged lemma
   keeps flat module descent as a dependency. Verdict: pass.

Changed in this reading: appended this independent review and clarified the complete
four-node direct dependency list. No Lean repair was needed, no signatures changed,
no holes were added, and no additional pruning is claimed. Closed one of one original
item holes; four new supporting nodes are proved, not new open split-off holes.
