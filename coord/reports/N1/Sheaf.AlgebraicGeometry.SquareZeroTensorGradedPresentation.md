## What changed

Reduced `tensorGradedPresentation_core_exists` to the algebra construction and its
square-zero kernel property, with a complete canonical-kernel assembly.
`tensorGradedPresentation_exists` now uses the constructed algebra's multiplication
law instead of the incorrect law asserted for every arbitrary core.

Added `TensorGradedAlgebraData`, `TensorGradedDegreeData`,
`TensorGradedKernelLocalIdeal`, and `TensorGradedKernelSquareZero`. The degree-data
and square-zero theorems are proved. The former constructs
all projections by coproduct descent, proves that the quotient is epi using
`closedImmersion_unit_epi`, and identifies the coproduct of kernels with the
canonical quotient kernel using Mathlib's exact-colimit and mono-colimit lemmas.
The diagonal and orthogonality equations follow by cancelling kernel inclusions.

The three primitive definitions are moved verbatim to the algebra-data module and
publicly reexported. The degree-data and square-zero modules are proof-only imports;
the local-ideal module is a proof-only import of the square-zero module. All existing
structure signatures remain unchanged. The multiplication theorem now takes a full
presentation, as explicitly requested by reviewer X-f9ba3. No downstream module is edited.
Change record: `coord/changes/tensor-graded-algebra-foundation.md`.

Repair of return X-f9ba3: replaced the false admitted arbitrary-core multiplication
assertion by the requested full-presentation field projection, and added its node
and statement-correction record. Updated hole accounting and citer review.

Repair of return X-31297: added the omitted
`Sheaf.AlgebraicGeometry.TensorGradedCoefficientSheafAction` to the change record
under `## Users`, with its three uses of `tensorGradedUnit` and unchanged meaning.
The current second reading finds 172 transitive importers and three external users;
the additional user and current holders are recorded below.
Compiled the original coefficient-action source unchanged against the delivered
`.lbuild` overlay using `lcompile.py`: exit 0, no errors or warnings (3.9 seconds).
The delivery tool reconstructs the dry-run commit on current `origin/sheaf-dag`.


Repair of landing-tool return at head 12f8c9a7a: added the three omitted users
TensorBoundaryKernelMapLocalMultiplication (D4), TensorGradedActionKernelSecondDiagonal
(unclaimed), and TensorGradedQuotientActionHomogeneous (unclaimed) to the foundation
change record's `## Users`. The fresh full scan also found TensorHomogeneousKernelAction
(E4) and TensorKernelSectionProduct (unclaimed); they and this item are now listed.
The current scan finds 183 transitive importers and eleven external users. Reviewed
each added user's source: moving the verbatim definitions with a public reexport
preserves every use, so no downstream source edit or forced adaptation is required.
The previous second-reading counts below describe that earlier repository snapshot.
Repair validation: all five delivery modules compile with lcompile.py --all, without
errors or warnings (2.8, 22.8, 2.7, 2.7, 12.7 seconds). All five newly listed external
users also compile unchanged against the delivery overlay, without errors or warnings
(3.2, 11.6, 10.6, 3.3, 7.4 seconds). No Lean source or DAG change was needed in this repair.

Repair of landing-tool return at head a5a21609f: added the omitted
`Sheaf.AlgebraicGeometry.TensorIdealSectionLocalMultiplication` to the foundation
change record's `## Users` (unclaimed in the current local claim snapshot).
The fresh repository-wide primitive-name scan finds twelve external users, all
now listed. Read its local multiplication statement and proof: the moved unit
retains its name, body, kernel types, and section equations through the public
reexport. No downstream source edit or forced adaptation is necessary.
All five delivery modules compile cleanly with `lcompile.py --all`.
The original local-multiplication source also compiles unchanged against the
delivery overlay with `lcompile.py` (9.0 seconds, exit 0). This repair changes only
the foundation user inventory and this report; Lean sources and DAG are unchanged.

## Proved and sorry left

Closed the original core-existence hole:
`AlgebraicGeometry.Scheme.Modules.tensorGradedPresentation_core_exists`
(node `lem-sc-square-zero-tensor-graded-presentation-core`). This is a decomposition,
not a proof free of admitted dependencies: two strictly smaller construction lemmas
are split off. The other original hole is removed by correcting its false statement
and proving the corrected field projection; this is a statement correction, not a
proof of the old assertion. Direct hole accounting is 2 removed minus 2 added = 0.

Proved with no new holes:
`AlgebraicGeometry.Scheme.Modules.tensorGradedDegreeData_exists`
(node `lem-sc-tensor-graded-degree-data`), including its private canonical-unit epi
and exact kernel-coproduct helpers.
The already-proved `tensorGradedPresentation_exists` remains proved, now by a route
that does not invoke the disputed universal multiplication assertion.

The corrected `AlgebraicGeometry.Scheme.Modules.tensorGradedPresentation_core_multiply`
(`lem-sc-square-zero-tensor-graded-presentation-core-multiplication`) is proved by
`T.b_multiply` for `T : TensorGradedPresentation j L`; it has no admission.

Every remaining hole in the delivery:

- `AlgebraicGeometry.Scheme.Modules.tensorGradedAlgebraData_exists`
  (`lem-sc-tensor-graded-algebra-data`): new; constructs only the two graded algebra
  coproducts, their quotient, and homogeneous multiplication. It has no kernel,
  exactness, square-zero, or degree projection fields and no square-zero hypothesis.
- `AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_locally_ideal`
  (`lem-sc-tensor-graded-kernel-local-ideal`): new; gives only local membership of
  two kernel sections in the extended immersion ideal, on an affine neighborhood.
  It has no square-zero or invertibility hypothesis and makes no product assertion.

`AlgebraicGeometry.Scheme.Modules.tensorGradedKernel_squareZero` is proved from
this local-membership statement, by evaluating the ideal-square equation on the
supplied affine neighborhood, mapping the ideal product, and sheaf separation.
It no longer contains a hole.

All data definitions are explicit constructions or structures with supplied fields.
No data are chosen inside a definition from a mere existence theorem.

## No longer needed

No existing public imports are removed, and no whole existing module is claimed pruned.
Second reading removed the redundant explicit import of
`WeilConjectures.AlgebraicGeometry.Modules.Invertible` from the new algebra-data
module: its public import of `Modules.TensorSection` already supplies it.
The existence proofs no longer need
`lem-sc-square-zero-tensor-graded-presentation-core-multiplication`
(`tensorGradedPresentation_core_multiply`). It is removed from the presentation
node's proof dependencies. Its declaration is now a proved field projection for a full presentation;
the existence proofs do not use it, even transitively.

The presentation existence theorem also no longer calls
`tensorGradedPresentation_core_exists`; both existence proofs instead assemble the
same canonical kernel data from the independent construction lemmas. The core
existence node is consequently removed from the full presentation's proof dependencies.

The core node's former direct dependencies `def-sc-invertible-module` and
`lem-weil-pbc-closed-immersion-unit-quotient` are now reached through the new
algebra-data and local-ideal arguments; neither is claimed globally unnecessary.
The original public imports are retained as the existing reexport interface.
All newly added imports used only by proofs are plain imports.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described an invalid restatement and gave up. The actual
construction can be decomposed into independent, strictly smaller algebra and
local-ideal assertions; the exactness, degree-map, and square-zero steps are proved
in this delivery.
The old claim that there were three original holes was incorrect: the full existence
theorem was already proved from the two admitted core assertions.

The former statement of `tensorGradedPresentation_core_multiply` was false for
arbitrary cores and is corrected in this repair. After identifying the identity immersion's tensor unit with the identity,
take X = Z = Spec Q, L = O, B = C = O[T], p = id, I = 0. Use twice the standard
inclusion in every degree for b_d and c_d, and half the coefficient projection for
q_d and the middle component of the degree map. The kernel maps are the unique
maps between zero objects. Every core field holds, but in degree zero the proposed
multiplication equality says 2 * 2 = 2. This is an edge-case counterexample to the
statement, not a difficulty proving it. Reviewer X-f9ba3 explicitly requested the correction to require a full presentation,
whose multiplication field gives the equation. This removes the false admission.
The constructed algebra has its own multiplication law, so neither existence
statement changes. See `coord/changes/tensor-graded-core-multiply.md` for verbatim
old/new signatures and the sole DAG citer review; the node has `statement_change`.

The new assertions were checked on identity immersions, the empty scheme, degree
zero, and arbitrary non-quasi-compact opens. The local ideal-generation argument
works on germs, where coproduct elements have finite support; it does not assume that
sections of an infinite sheaf coproduct globally have finite support. For a closed
immersion, coproducts commute with pushforward as checked on stalks. Invertibility
ensures that the tensor-power multiplication is commutative. The algebra-construction
proof also accounts for the noncanonical chosen adjunction: its target homogeneous
inclusions are transported along the unit comparison, preserving coproduct
universality. No multiplicativity is claimed for those target inclusions.

The unit record `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and
has no realized proof steps involving these auxiliary nodes. Its route is preserved.
The source text was read at Stacks Tags 09MS and 0B8S (the local literature files
are absent on this machine). No target statement or target definition is weakened.

## New nodes

`lem-sc-tensor-graded-algebra-data`: the graded polynomial-algebra construction on
local frames, with transition units and the homogeneous quotient law. It is independent
of exactness and square-zero arguments. Module `Sheaf.AlgebraicGeometry.TensorGradedAlgebraData`.

`lem-sc-tensor-graded-degree-data`: the canonical kernel direct sum and projection
maps for any such algebra data. Its proof is complete in Lean and uses the existing
closed-immersion-unit epi theorem and Grothendieck abelianness plus Mathlib APIs.
Module `Sheaf.AlgebraicGeometry.TensorGradedDegreeData`.

`lem-sc-tensor-graded-kernel-square-zero`: proved for supplied graded algebra data
using the local-ideal lemma, mapped ideal multiplication, and sheaf separation.
Module `Sheaf.AlgebraicGeometry.TensorGradedKernelSquareZero`.

`lem-sc-tensor-graded-kernel-local-ideal`: the remaining local-generation step,
without a square-zero hypothesis. Its complete proof in words uses the direct-sum
kernel, finite support on stalks, and restriction to affine neighborhoods.
Module `Sheaf.AlgebraicGeometry.TensorGradedKernelLocalIdeal`.

The existing presentation and core-existence nodes are updated to the actual route.
The existing multiplication node now states the full-presentation equation and
records its field-projection proof with no proof dependencies and statement_change.
Change records: `coord/changes/tensor-graded-algebra-foundation.md` and
`coord/changes/tensor-graded-core-multiply.md`.


## Earlier second reading (a previous round; superseded)

Repair addendum to the prior independent reading, addressing return X-f9ba3.
The reviewer rejected its claim that marking the false assertion as disputed and
unused was sufficient. The exact requested correction is now applied:
`tensorGradedPresentation_core_multiply` takes `TensorGradedPresentation j L`
and its complete proof is `T.b_multiply`. The old false core claim is absent.
This addendum records the repair; it does not claim a new independent worker review.
The downstream name scan finds no external user. The sole DAG citer is the full
presentation node, whose delivered route already constructs the field from
`A.b_multiply` without this theorem. The corrected node records the same signature,
field-projection proof, empty proof_deps, proof_origin, and statement_change with
verbatim old statement/proof/dependencies and the citer review. No unit or target
statement changes. Only the two construction admissions remain; removing the old
false hole is a correction, not a proof of its invalid claim.

Compiled all five delivery modules with lcompile.py --all: exit 0, no errors or
warnings (3.0, 26.1, 2.1, 2.6, and 12.6 seconds).

A scratch axiom check of the corrected multiplication theorem compiled cleanly:
only propext, Classical.choice, and Quot.sound; no sorryAx.

The repair dry run found three newer external users of the moved definitions:
SquareZeroTensorGradedProductProjection (unclaimed),
SquareZeroTensorGradedQuotientMultiply (U2), and TensorCoefficientActionSupport (P3).
The foundation change record now includes them. Their statements use unchanged
names, types and definition bodies; no source adaptation is required.

QuotientMultiply compiled unchanged against the repaired overlay (2.9 seconds).
ProductProjection's unchanged source cannot currently compile locally because
SquareZeroTensorSectionProductComparison has no compiled baseline object;
TensorCoefficientActionSupport imports ProductProjection. Their uses were reviewed
in source and preserve the moved definitions' types and bodies. No forced adaptation
is claimed. The corrected multiplication axiom check was also repeated against the
explicit repaired overlay (1.9 seconds): only the three permitted axioms.


## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-14. Read all five delivery modules, all seven
node records, both change records, the original module, the unit realization,
and the cited Stacks proofs (Tags [09MS](https://stacks.math.columbia.edu/tag/09MS),
[0B8S](https://stacks.math.columbia.edu/tag/0B8S), and
[04CJ](https://stacks.math.columbia.edu/tag/04CJ)).

1. Interface: PASS with the declared correction. The diff and declaration parser
   confirm byte-identical signatures for both structures and both existence
   theorems. Both structure bodies and all three relocated primitive definition
   bodies are byte-identical. The only existing signature change is the recorded
   replacement of the false arbitrary-core multiplication assertion by the full
   presentation field projection. The current downstream scan finds 177 importers,
   exactly the six external primitive-definition users listed in the foundation
   record, and no external user of the corrected theorem. No target is changed.
2. Proof integrity: PASS. Ran lcompile.py --all: all five modules compile without
   errors or warnings (3.5, 24.2, 2.0, 2.2, 11.5 seconds). A fresh scratch axiom
   check against this delivery's .lbuild shows only propext, Classical.choice,
   Quot.sound for the three primitive definitions, tensorGradedDegreeData_exists,
   and the corrected multiplication theorem. The two admitted construction lemmas,
   square-zero theorem, and existence theorems additionally use sorryAx, as expected.
   The only textual admissions are the two report-listed public named theorems,
   each with its complete source/proof docstring and node. No prohibited declaration
   or hollow definition occurs. tensorGradedCore consumes supplied data, and the
   existence proofs eliminate Nonempty only into a proposition. The original
   tensorGradedUnit choice is pinned by the unit's section formula in its upstream
   existence theorem, rather than an arbitrary undetermined witness.
3. Split statements: PASS. Algebra data omit kernels, exactness, degree projections,
   and square-zero; local ideal membership omits square-zero and any product
   conclusion. These are independent proper parts of the construction, not renamed
   copies of the item. Checked identity immersions (zero kernel), empty schemes,
   degree zero, non-square-zero closed immersions, and arbitrary opens. For the
   local lemma, finite support is used only on stalks; representing finitely many
   germs and shrinking gives the single affine neighborhood for both sections.
   The chosen-unit comparison is an invertible module transformation, so it preserves
   the kernel and the target coproduct. Fresh leanfinder searches for symmetric
   algebra sheaves and local finite ideal-coefficient presentations, a Loogle search
   for Ideal.map_mul, and an AlgebraicGeometry grep found building blocks but no
   theorem closing either admission directly. Repository/upstream text searches
   likewise found no duplicate. Neither admission has a short existing-API proof.
4. Route and pruning: PASS. The existence proof assembles the canonical kernel from
   the algebra, exactness/projections, and square-zero lemmas. The degree proof uses
   Mathlib's exact-colimit/mono-colimit theorems and the existing closed-immersion
   unit epi result. Square-zero follows from Ideal.map_mul and sheaf separation.
   The four new modules expose only imports needed for their interfaces; proof
   dependencies use plain imports. Existing public reexports are preserved.
   No longer needed lists all removed old proof edges: core existence and arbitrary
   core multiplication from the full presentation, and the core's old direct
   invertibility/unit-quotient edges (now used through the new lemmas). The corrected
   multiplication node also drops its old invertibility proof edge: invertibility
   remains only in its preserved binders. No whole module is claimed pruned.
   sk-thm-curveestimate realizes thm-sc-proper-cohomology and no auxiliary steps;
   its route is preserved.
5. DAG consistency: PASS. All lean.statement fields match the declaration parser.
   Existing records change only permitted proof fields, except for the recorded
   multiplication statement correction with its counterexample and sole-citer
   review. New records contain the required provenance, source, proof steps,
   dependency union, search records, creation, blueprint, chapter/unit and Lean
   fields. The admitted local-generation node records the complete intended proof;
   the proved degree and square-zero nodes record their actual Lean reductions.

Second-reader changes: repaired the broken Markdown Users table in the foundation
change record; replaced normalized one-line Old/New multiplication signatures with
verbatim multiline source signatures; refreshed its downstream count to 177;
added this independent reading and fresh search/axiom evidence. No Lean proof or
statement needed a further edit.

Accounting verdict: the core-existence hole is decomposed into two smaller holes;
removal of the false multiplication hole is a statement correction, not a proof.
Thus zero of the two original admitted assertions are closed without admissions,
two holes are split off, and direct net hole reduction is zero. The newly proved
exactness/projection and square-zero reductions and the corrected field projection
are valid; no claim of an axiom-free presentation existence proof is made.

## Earlier second reading (a previous round; superseded)

1. **Interface:** PASS. I diffed the delivered presentation module against the repository version. Existing structure and theorem interfaces are byte-identical except for the recorded correction of `tensorGradedPresentation_core_multiply` from an arbitrary core to a full presentation. The three moved primitive definitions retain their names, bodies, and public types through the reexport. No target statement changes.

2. **Proof integrity:** PASS. `lcompile.py --all` compiles all five delivered modules without errors or warnings. The only textual `sorry`s are the two named split theorems `tensorGradedAlgebraData_exists` and `tensorGradedKernel_locally_ideal`, each with a source, proof docstring, and node. There are no prohibited declarations or hollow definitions. The corrected multiplication theorem is a field projection.

3. **Split statements:** PASS. The algebra-data split contains only the graded algebras, quotient, coproduct maps, quotient squares, and multiplication; it omits kernels, exactness, projections, and square-zero. The local-ideal split contains only affine local ideal membership and omits square-zero and multiplication. Both are strictly smaller than the target construction. I checked identity and empty immersions, degree zero, non-square-zero ideals, and arbitrary opens. Fresh searches found no existing theorem that closes either split directly; `Ideal.map_mul` is used for the proved square-zero reduction.

4. **Route and pruning:** PASS. The full presentation is assembled from algebra data, canonical exact degree data, and the square-zero theorem. The degree proof uses the closed-immersion unit epi and exact coproduct APIs; the square-zero proof uses the local ideal theorem, `Ideal.map_mul`, and sheaf separation. Proof-only imports are plain imports, and the report lists removed proof edges. The unit `sk-thm-curveestimate` has no realized step involving this auxiliary route, so its route is unchanged.

5. **DAG consistency:** PASS. Node `lean.statement` strings match the declarations; proof dependencies and origins follow the delivered route. New nodes contain source, proof, search, creation, blueprint, chapter/unit, and Lean provenance fields. The multiplication statement correction has a counterexample and citer review in its change record.

**Changes in this reading:** no Lean proof or statement changed. I verified the five-module build, the delivery diffs, DAG metadata, downstream primitive-definition users, and Mathlib/Stacks searches. I removed the blank line that broke the foundation Users table; its listed users are complete. The current source scan counts 181 transitive importers (rather than the earlier snapshot count of 183), eleven external primitive-definition users, and no external multiplication-theorem user.

Fresh axiom verification: the primitive definitions, degree-data theorem, and corrected multiplication theorem use only `propext`, `Classical.choice`, and `Quot.sound`. The two split theorems, square-zero reduction, and both existence theorems additionally use `sorryAx`, exactly as reported. The scratch check compiled without errors or warnings against this delivery’s `.lbuild` overlay. No split hole was closed in this reading. Accounting remains a core-existence decomposition into two smaller admissions and a correction of the false multiplication statement: zero of two original admissions proved without admissions; two split off; net zero.

## Second reading by N1

1. **Interface:** PASS. I compared the delivered presentation module with the repository
version. The three relocated primitive definitions, both presentation structures, and
both existence theorem signatures are unchanged byte for byte. The sole changed existing
signature is `tensorGradedPresentation_core_multiply`, covered by its open change record:
the arbitrary-core assertion is replaced by the full-presentation field projection. No
target statement changes. The foundation Users table lists all twelve external primitive
users found by a fresh repository scan; their names and uses retain the same public types.

2. **Proof integrity:** PASS. `lcompile.py --all` compiles all five modules without errors
or warnings. The only textual admissions are the named public theorems
`tensorGradedAlgebraData_exists` and `tensorGradedKernel_locally_ideal`, each with a
source, complete proof docstring, and matching node. There are no prohibited declarations
or hollow definitions. The scratch axiom probe gives only `propext`, `Classical.choice`,
and `Quot.sound` for the primitive definitions, degree-data theorem, and corrected
multiplication theorem; the remaining completed reductions carry `sorryAx` only through
the two reported split lemmas.

3. **Split statements:** PASS. The algebra-data theorem supplies only the graded algebra
objects, coproduct maps, quotient squares, and homogeneous multiplication; it assumes no
square-zero condition and gives no kernels, exactness, or projections. The local-ideal
theorem supplies only affine local membership for two kernel sections and has no product
conclusion, square-zero assumption, or invertibility assumption. These are proper parts
of the construction. I checked identity and empty immersions, degree zero, a
non-square-zero ideal, and arbitrary opens. Fresh leanfinder, Loogle, grep, and repository
searches found no existing theorem closing either statement; `Ideal.map_mul` is the
short Mathlib step used by the proved square-zero reduction. The old arbitrary-core
multiplication statement has a concrete scaled degree-zero counterexample, so the
recorded correction is necessary.

4. **Route and pruning:** PASS. The existence route assembles explicit algebra data,
canonical degree data, and the square-zero reduction; it no longer depends on the false
arbitrary-core multiplication claim. The degree proof uses the closed-immersion unit epi
and exact coproduct APIs. The square-zero proof uses local ideal membership, ideal product
mapping, and sheaf separation. Proof-only imports are plain imports. The report's
`No longer needed` section records the removed old proof edges and no whole module is
claimed pruned. Unit `sk-thm-curveestimate` realizes no auxiliary step, so its route is
unchanged.

5. **DAG consistency:** PASS. Every delivered node's `lean.statement` agrees with the
parsed declaration, and each `proof_deps` is exactly the union of its proof-step uses.
Existing nodes change only permitted proof metadata, except for the recorded multiplication
statement correction and citer review. New nodes include source, proof steps, searches,
creation, blueprint, chapter/unit, and Lean provenance. The unit realization remains
unchanged.

**Changes in this reading:** no Lean source, theorem statement, node, or change record was
needed beyond this report section. I verified the five-module build, declaration diffs,
DAG metadata, downstream user inventory, fresh searches, Stacks source references, and
axiom probe. The accounting remains a decomposition of the original core-existence hole
into two smaller admissions (net zero direct hole reduction), plus correction and proof of
the false multiplication assertion.
