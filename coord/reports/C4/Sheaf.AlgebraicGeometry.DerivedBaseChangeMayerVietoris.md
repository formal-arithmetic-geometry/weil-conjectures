## What changed

Repair of reviewer X-00326, H4: `DerivedBaseChangeMayerVietorisMaps` now publicly imports
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` and defines
`mvDerivedPullbackAdjunction` as an abbreviation of the existing
`canonicalPullbackAdjunction`. This removes the duplicate adjunction construction while
preserving the same canonical data. The component node adds
`def-pc-affine-global-hom-base-change-map` to `stmt_deps`. The new change record is
`coord/changes/mvDerivedPullbackAdjunctionReuse.md`. No theorem signature, proof obligation,
or target changes in this repair. The previous second-reading section is retained as history.
The four-module compile and dry-run results for this repair are recorded below.

The main theorem is proved by assembling the two lower decomposition theorems into a `TriangleMorphism` and checking its two biproduct projections. The explicit open comparison used by the component maps is now constructed from the pinned derived pullback adjunctions, open restriction adjunctions, and derived pullback composition comparisons. Its unit and counit identities use `Adjunction.leftAdjointUniq`, so no arbitrary witness is selected from a bare `Nonempty` statement. The lower modules now use fixed canonical open adjunctions; the boundary obligation is stated directly for the canonical maps and does not infer its connecting square from the first two squares. They remain separate named intermediate obligations.

The main module retains the public Mayer--Vietoris triangle and base-change map imports, adds the canonical component module publicly because its statement needs the constructed comparison, and imports the two delivered lower modules and right-derived additivity for the proof. The old public affine pullback/tensor module is removed. The helper module additionally imports the existing canonical pullback adjunction and the derived adjunction and adjunction uniqueness interfaces required by the open comparison construction.

## Proved and sorry left

H4 repair validation: `lcompile.py --all` compiled all four modules successfully:
Maps 64.7s, Boundary 6.6s, Squares 7.8s, main 33.6s (wrapper wall times).
`deliver3.py C4 Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris --no-push`
printed `OK (dry run)`; compilation and preflight passed as CODEX and nothing was pushed.
The repair adds no holes and closes no additional holes; the decomposition below is unchanged.

Retry validation: the first `deliver3.py --no-push` dry run passed as CODEX with nothing pushed. Its note about filtering an added statement dependency was resolved by retaining the original statement dependencies. `lcompile.py --all` compiled all four delivered modules cleanly. The wrapper reported 452.9 seconds for the component module including its admission-slot wait, then 5.3 seconds for Boundary, 5.6 seconds for Squares and 51.2 seconds for the main module. Each Lean subprocess passed the unchanged 60-second deadline.

Closed `AlgebraicGeometry.derivedBaseChange_mayerVietoris_naturality` (node `lem-pc-rf-mv-triangle-naturality`). Its upper assembly proof compiles. This is a decomposition, not a completed proof: one hole is closed and two holes are added (net minus one). The following strictly smaller intermediate theorems remain `sorry`, each with its own node and source proof:

- `AlgebraicGeometry.derivedBaseChange_mayerVietoris_firstTwoSquares` (`lem-pc-rf-mv-base-change-first-two-squares`).
- `AlgebraicGeometry.derivedBaseChange_mayerVietoris_connectingSquare` (`lem-pc-rf-mv-base-change-connecting-square`).

No definition contains `sorry`; all component data are explicit constructions.

## No longer needed

The original direct proof imports `DerivedDirectImageCompositionUnbounded`, `DerivedDirectImagePreservesQCoh`, `DerivedMayerVietorisFunctorial`, `DerivedPullback`, `SchemeDerivedDirectImage`, and `PreDerivedAdjointFunctorsGeneral` are no longer imported by the main module. The Mayer--Vietoris functoriality, direct-image composition, quasi-coherence and derived pullback/direct-image declarations remain needed by the lower intermediate theorems and are not globally pruned. The general pre-derived-adjunction module is not needed by this route: the pinned scheme-derived adjunction is used instead. The old public `AffineDerivedPullbackTensorTilde` import and its `derivedPullback_openRestriction_iso` witness are no longer needed by this route. No claim is made that either module is unreachable from every other target branch.

Every old direct proof dependency is replaced in the main node by the three component/square nodes: `lem-weil-pbc-morphism-affine-schemes-affine`, `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-qcqs-over-affine`, `lem-pc-derived-mayer-vietoris-triangle`, `lem-pc-derived-direct-image-composition`, `def-pc-derived-pullback`, `def-pc-derived-direct-image`, `lem-pc-derived-mayer-vietoris-functorial`, `def-pc-derived-base-change-map`, `lem-pc-pre-derived-adjoint-functors-general`, `lem-pc-derived-direct-image-preserves-qcoh`. The base-change and triangle interfaces remain statement dependencies; the lower argument retains the geometric and derived-functor dependencies described above. Only the general pre-derived-adjunction node and bare affine open-comparison witness are bypassed by this route; no globally unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

A read-only dependency scan of the delivery overlay found no cycle through a delivered node, but encountered ten pre-existing cycles below it. One is `lem-pc-cycle-pullback-tower-comparison-stage3 → new-tower-comparison-first → lem-pc-cycle-pullback-tower-comparison-stage3`; those nodes are outside this item and were not edited. This is reported for the maintainer.

Reviewer X-00326 identified a duplicate canonical pullback adjunction constructor (H4). The repair reuses the existing constructor by `abbrev`, as required by stage 3 §3.

The earlier attempt chose `Classical.choice (derivedPullback_openRestriction_iso ...)`, although that theorem gives only `Nonempty` of an isomorphism and fixes no unit, counit, or nested-restriction coherence. Such data did not satisfy the project rule for definitions. The repaired component construction uses adjunction uniqueness and the canonical pullback-composition family; the lower theorem docstrings now state the required mate and connecting-map arguments explicitly. The Stacks sources read for this route are Tags 0DJ9 (Lemma 36.26.2), 08BV (Lemma 20.33.2), 08HZ (Lemma 20.33.5), 0D5T (Lemma 20.28.2), 0D5S (Lemma 20.27.2), and 08HY (Remark 20.28.3).

## New nodes

`def-pc-rf-mv-base-change-components` records the explicit adjunctions, canonical open comparisons, pasted open maps, triangles and biproduct middle map.

`lem-pc-rf-mv-base-change-first-two-squares` states only the first two squares for those canonical adjunctions, for every pair of objects and ψ.

`lem-pc-rf-mv-base-change-connecting-square` states distinguished triangles and the connecting square for those fixed canonical maps. It does not construct the triangle morphism or assert either of the first two squares.

The change record is `coord/changes/derivedBaseChangeMayerVietorisElaboration.md`. It gives the full old and new signatures: the assigned non-target theorem now uses the explicit canonical open comparison instead of three bare Nonempty witnesses. This follows the unchanged natural-language node's canonical-map requirement. No target signature changes and no forced adaptations are needed. The unit record has empty realized statement and step lists, so no realized unit step is bypassed.

Edge cases checked for the canonical construction: identity morphisms and top opens use the adjunction unit laws; zero maps give zero components; empty opens and redundant covers admit the same exact sequences. Nested-open coherence uses the specified composition path and its associativity, not naturality in objects alone.

## Earlier second reading (a previous round; superseded)

1. Interfaces: diffed all four delivered modules against the repository. Only the main module already exists. Its three open-comparison expressions change from bare Nonempty witnesses to mvPullbackOpenRestrictionIso; these are the only signature changes and are declared in the change record. All hypotheses and triangle/component conclusions remain. No target statement or definition is edited. The downstream uses listed in the change record make no calls to this theorem.

2. Kernel checks: all four files compile with lcompile.py --all, in 43.5, 7.1, 6.8 and 59.2 seconds. A scratch import prints axioms for the three component definitions, both split theorems and the upper theorem. The definitions have only propext, Classical.choice and Quot.sound; the three theorems additionally have sorryAx. The only syntactic holes are the two named split theorems. No prohibited declaration or hollow definition is present.

3. Split statements: the first-two-squares theorem asserts neither a boundary nor distinguishedness; the boundary theorem asserts neither of the first two squares nor a triangle morphism. Both are true strict parts of the argument, with source proofs and nodes. I read exists_schemeDerivedAdjunction and exists_derivedPullbackComposition: their displayed Hom-equivalence and lift identities specify the chosen comparison data used downstream. The latter is now proved in the repository, and the former is also proved; no arbitrary witness of an unproved bare existence statement occurs in the new definitions. The open adjunction is built from the underived restriction adjunction, and leftAdjointUniq gives the unit and counit identities. I checked the source constructions in [Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9), [08BV](https://stacks.math.columbia.edu/tag/08BV) and [08HZ](https://stacks.math.columbia.edu/tag/08HZ): the induction diagram and functorial short exact sequences support this decomposition. Identity squares and repeated top opens use these same identities; zero maps give zero components, and empty opens give zero restriction terms. The boundary proof correctly uses naturality of a morphism of short exact sequences, rather than inferring a third square from two triangulated squares.

I repeated searches with different words using msearch leanfinder (boundary maps of short exact sequences under derived adjunction), loogle (TriangleMorphism) and grep (triangleOfSES and Hom-equivalence naturality), and rg on the library. The generic boundary-naturality hits do not give the fixed canonical mate identifications. I also read the existing Mayer--Vietoris functoriality/direct-image theorems, K-injective presentation, RelativeMVCanonicalTriangles and single-complex open comparison declarations. Their conclusions do not directly close either delivered obligation. No small further closure was found.

4. Route and pruning: the upper proof genuinely constructs TriangleMorphism from the three equations and verifies the two projections by biproduct algebra. The unit record has empty realized statement and step lists, so none is bypassed. The report distinguishes removed main imports from dependencies still needed by the lower argument. This delivery is a decomposition, not net hole reduction.

5. Nodes: the main proof, proof_deps and proof_origin match the assembly. New node signatures match the delivered statements; source, searches, created, blueprint, unit and lean records are present. The lower proof dependencies include the affine permanence, qcqs, composition and functoriality facts their docstrings invoke.

Second reading changed the report to label the result explicitly as a decomposition and to enumerate all old main proof dependencies below. The first delivery dry run timed out at 60 seconds on the main module. I restored backward.isDefEq.respectTransparency.types to false (leaving respectTransparency true); a fresh single-file compile passed in 46.5 seconds. I updated the elaboration change record accordingly. This changes no declaration signature, data or proof body.

## Earlier second reading (a previous round; superseded)

1. **Interfaces.** Diffed the existing module against the repository and read all three new modules. The three open-isomorphism replacements are declared in `coord/changes/derivedBaseChangeMayerVietorisElaboration.md`. This reading additionally compressed the six repeated `Triangle.mk` expressions into calls to the identical `mvBaseChangeTriangle` definition and updated the record's full new signature and the node's `lean.statement`. A scratch `compressionCompatibility` theorem with the previous canonical statement compiled by directly applying the compressed theorem, confirming no proposition changed in this compression. No hypothesis or triangle conclusion is removed, and no target declaration or target definition changes. A fresh declaration-name search found no caller outside the assigned module.

2. **Proof and kernel.** The assembly constructs the triangle morphism from three separate commuting equations and proves both middle projections by biproduct identities. The only syntactic holes are the two named lower theorems reported above. No prohibited declaration or hollow definition occurs. The canonical adjunction uses the same composition-family choices and counits as `schemeDerivedBaseChangeMap`; both upstream existence theorems are proved and specify their comparison behavior. The open comparison is an explicit composite using uniqueness of left adjoints. Scratch axiom checks showed only `propext`, `Classical.choice`, and `Quot.sound` for all seven public component/adjunction/comparison definitions checked; the two obligations and upper theorem additionally use `sorryAx`, as expected. Repeated expanded-statement artifact compiles timed out; the compact main statement compiled to an artifact in 33.7 seconds. The unchanged 60-second Lean deadline is used throughout. The first two runs were accidentally overlapped on the same artifact directory, causing an artifact race; all subsequent checks were sequential.

3. **Split statements.** Read both signatures, their complete docstring arguments, the canonical components, `schemeDerived_mayerVietoris_naturality`, `schemeDerived_mayerVietoris_directImage`, and the K-injective presentation. The first obligation contains only the first two equations; the second contains distinguishedness and the connecting equation, but neither of the first two equations nor a triangle morphism. These are true strict parts of the argument, not restatements. The mate and short-exact-sequence arguments agree with [Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9), [08BV](https://stacks.math.columbia.edu/tag/08BV), and [08HZ](https://stacks.math.columbia.edu/tag/08HZ). Identity squares, top/empty opens, repeated cover members, and zero maps require no arbitrary comparison or extra hypothesis. Boundary naturality is derived from short exact sequences, not inferred merely from two triangulated squares. Repeated msearch used leanfinder (connecting morphisms under inverse/direct image adjunction), loogle (`CategoryTheory.Pretriangulated.TriangleMorphism`), and grep (adjunction units and base-change restrictions), followed by local `rg`. Hits supply generic ingredients, not either fixed canonical obligation; no short further closure was found.

4. **Route and pruning.** The main proof uses the two smaller obligations and the components, then elementary biproduct algebra. Unit `sk-thm-picard-semicon` has realized statement `[]` and steps `[[]]`, so no realized step is bypassed. The report enumerates every old main proof dependency and distinguishes removed direct imports from retained lower dependencies. This is one upper hole closed and two lower holes added (net minus one), a decomposition rather than a completed proof. No global module pruning is claimed.

5. **Nodes.** Checked the main node's assembly steps and union of proof dependencies against the proof. Updated its exact Lean signature for the constructor compression. New nodes have matching signatures, source, searches, creation records, blueprint ancestry, chapter and unit. Lower node plans describe the mate and boundary calculations their docstrings require; component data are statement dependencies of both. No delivered node introduces an import cycle.

Second reading changed the main statement's repeated constructors to definitionally identical calls, its elaboration settings to both transparency options true, and its proof to cache local preadditive and finite-biproduct instances with `let`. In the new component module it marked four adjunction/comparison definitions `irreducible` for elaboration, leaving their bodies unchanged, and explicitly unfolded `mvOpenPullbackIso` in the two private uniqueness proofs. This does not make any definition opaque to the kernel. Updated the change record, main node signature, and this report. No new declaration or hole was added, and neither split obligation changed.

Final dry run: `deliver3.py C4 Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris --no-push` printed `OK`, commit `c249c950fe`, compilation and preflight passed, review class `CODEX`. The repaired artifact compiles and axiom probes passed through the delivery wrapper. The CODEX classification reflects the declared canonical comparison/interface correction, public import changes, and new decomposition nodes; it does not convert this decomposition into net proof progress.

## Second reading by C4

1. Interfaces: diffed the main module against the repository and checked that the other
three modules are new. The only existing signature changes are the three documented
canonical open-comparison replacements and the definitionally identical triangle
constructor compression in derivedBaseChangeMayerVietorisElaboration.md. All geometric
hypotheses, object hypotheses, component specifications and distinguishedness clauses
remain. No target statement or target definition changes. The repository contains no
caller of this theorem outside its declaration. The H4 repair's abbreviation unfolds
to canonicalPullbackAdjunction, which selects literally the same normalized adjunction
as schemeDerivedBaseChangeMap. Its added public import is needed by the exposed body.
Verdict: no accidental interface change; the declared correction is necessary.

2. Proof: compiled all four files locally in import order with lcompile.py --all:
Maps 34.8s, Boundary 6.9s, Squares 8.0s, main 32.1s. Read the actual three
TriangleMorphism commutativity fields and both projection calculations. Fresh scratch
#print axioms checks against these artifacts cover all seven public constructions,
both split theorems and the upper theorem. The constructions use only propext,
Classical.choice and Quot.sound; the three theorems also use sorryAx. Exactly the two
reported lower declarations contain syntactic sorry. No prohibited declaration or
hollow definition occurs. Verdict: the assembly is checked, and its two obligations
remain open; this is one upper hole closed, two lower holes added, net minus one.

3. Split statements: read the two signatures and docstring arguments against their
nodes, exists_derivedPullbackComposition, exists_schemeDerivedAdjunction, the
K-injective presentation, and both existing Mayer--Vietoris functoriality statements.
The first split asserts only the unit and difference squares, independent of the
boundary; the second supplies boundaries, distinguishedness and the connecting
equation, without the first two squares or a triangle morphism. Both are strict
parts, rather than restatements of the item. The canonical composition family has
unit and associativity laws, and the adjunction Hom-equivalence is pinned to its
counits. No bare unproved existence witness supplies data.

Read [Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
[08BV](https://stacks.math.columbia.edu/tag/08BV) and
[08HZ](https://stacks.math.columbia.edu/tag/08HZ). The canonical mate calculation
identifies the open components; the connecting equation comes from a morphism of
short exact sequences, not from the first two triangulated squares. In the identity
square and top/repeated opens, the unit and comparison coherence laws apply; empty
opens give zero restriction terms, and zero psi gives zero component maps. Affine
base change ensures compactness of the inverse-image opens without assuming their
intersection affine. Repeated msearch used leanfinder with a canonical-adjunction
base-change/connecting-morphism query, loogle for leftAdjointUniq, and grep for
triangleOfSES naturality and the uniqueness unit law; rg searched both library roots
and the upstream checkout. Hits give generic short-exact-sequence naturality and
adjunction uniqueness, but neither complete fixed canonical obligation. Verdict:
true, needed, sourced smaller statements; no few-minute closure found.

4. Route and pruning: the upper proof combines the two strict parts with biproduct
algebra. Unit sk-thm-picard-semicon has realized statement [] and steps [[]], so no
realized route is bypassed. The No longer needed section enumerates every old main
proof dependency and distinguishes removed direct imports from lower dependencies.
This reading removed DerivedMayerVietorisFunctorial and
DerivedDirectImageCompositionUnbounded only from the Squares module: its statement
and canonical mate argument require neither, and its node's proof_deps includes
neither. Both remain imported by Boundary, whose proof plan uses them. No additional
global module pruning is claimed. Verdict: decomposition and pruning are reported
without treating a landing as net proof progress.

5. Nodes: checked the existing node's changed fields are only lean, proof, proof_deps
and proof_origin. Its signature and the new node signatures match the Lean text
up to formatting, and each proof_deps is exactly the union of the step uses. The
new nodes have source, three search kinds, created, blueprint, chapter, unit and
Lean records. The components node cites def-pc-affine-global-hom-base-change-map
as a statement dependency, matching the H4 reuse. Verdict: records follow the
delivered construction and assembly.

This second reading changed only the two redundant plain imports in Squares and
this report. It changed no declaration signature, proof body, constructed data, node
or hole count.
