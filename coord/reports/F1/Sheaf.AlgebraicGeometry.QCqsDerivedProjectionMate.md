## What changed

Replaced the sole `sorry` in `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionMate` with a
compiling affine-generation argument. The original theorem signature, visibility and
docstring are unchanged. Added three proof-only imports for the remaining obligations,
and used the existing `AffineQCohDerivedEquivalence` and `DerivedModuleFreeGeneration`.

The actual Lean proof defines an isomorphism-invariant all-shifts locus on D(A), supplies
its generators and closure conditions to free generation, and recovers the requested
object through the affine equivalence counit and `shiftFunctorZero`. Its generator proof
constructs the linear isomorphism `ULift A ≅ A`, combines shifts with `shiftFunctorAdd`,
and applies the affine equivalence's supplied structure-sheaf identification. No data
definition was added and no arbitrary object was selected from mere unproved existence.

New modules: `QCqsProjectionMateAffineDescent`, `QCqsProjectionMateShiftedUnit`, and
`QCqsProjectionMateAffineLocus`. Each contains one named public theorem and a sourced
proof in words. Updated the item's DAG proof, proof dependencies and proof origin.

## Proved and sorry left

Closed `AlgebraicGeometry.qcqsDerivedProjectionMate_isIso`
(node `lem-pc-qcqs-derived-projection-mate`), the only original hole. This is a
**decomposition**, not a complete proof independent of remaining obligations.
There are no direct sorries left in the item's module.

Added three holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.qcqsProjectionMate_of_affine`, node
  `lem-pc-qcqs-projection-mate-affine-descent`.
- `AlgebraicGeometry.qcqsProjectionMate_shiftedUnit_isIso`, node
  `lem-pc-qcqs-projection-mate-shifted-unit`.
- `AlgebraicGeometry.qcqsProjectionMate_affineLocus_closed`, node
  `lem-pc-qcqs-projection-mate-affine-locus`.

Thus this delivery closes one original hole and adds three, a net change of -2 before
any closure-ledger reachability effects. Existing affine equivalence and free-generation
dependencies are used as supplied, with their existing proof status.

All four modules compile without warnings through `lcompile.py --all`. The original
scheme morphism and localization universes remain unrestricted. Edge cases checked in
the statement review: empty schemes, the zero ring, zero objects, empty coproducts,
negative and zero shifts, and unrelated module/scheme localization universes. The empty
coproduct clause includes the zero object; generator transport uses `ULift.{0}` exactly
as required by the existing free-generation statement.

## No longer needed

No original import was removed: they supply the unchanged public signature. A trial
`Mathlib.Algebra.Category.ModuleCat.Ulift` import was removed because its needed
linear-equivalence declarations are already available; compilation confirms this.

The new route does not use node `lem-pc-projection-locality` or module
`Sheaf.AlgebraicGeometry.ProjectionFormulaLocality`. Its proof dependencies
`ProjectionFormulaLocalityLocalToGlobal` and `ProjectionFormulaLocalityGlobalToLocal`
are likewise unnecessary for this route. The affine-descent obligation uses general
cohomology/sheaf open-cover detection directly, accommodating the first-factor order
and arbitrary supplied comparison. This is pruning from this proof route, not a claim
that these modules have become globally unreachable from all targets.

The other eight original proof dependencies remain necessary: the affine equivalence
and module free-generation theorems are directly used; open restriction of pullback,
tensor and direct image is retained by the descent node; tensor coproducts, direct-image
coproducts, pullback quasi-coherence and canonical tensor quasi-coherence are retained
by the closure node. The unit's statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original file did not import its planned proof dependencies, as already anticipated
by the dispatch brief. More substantially, the existing locality interface takes a
morphism with source `Rf_*E ⊗ K` and target `Rf_*(E ⊗ Lf^*K)`, whereas the assigned mate
has the opposite tensor order. Braiding can convert that order, and the locality
theorem accepts an arbitrary arrow, despite its canonical-map docstring. However,
it does not supply descent of an arbitrary t and p or comparisons between chosen
localization universes. The new affine-descent node
states that missing part of the original plan, including standard-universe transport;
it does not assume that t is canonical.

The source's generator and triangle sentences are not ready-to-apply Lean declarations
for the unrestricted supplied p and t. The shifted-unit node isolates the actual mate
calculation without adding geometric hypotheses; the locus node isolates preservation
and five-lemma closure, with all shifts to avoid imposing a new shift-compatibility
hypothesis on t. No statement was weakened or marked disputed.

Read Stacks Tags 08EU and 0A9Q from the Stacks website. LeanSearch was unavailable
(HTTP Internal Server Error); this is recorded as unavailable, not as a no-match.
LeanFinder and grep found shifted-adjunction, conjugate-invertibility, localization and
triangle infrastructure but no matching scheme theorem. Existing proper/noetherian
projection-comparison declarations impose hypotheses absent here. Blueprint searches
for projection formula, shifted free generators, locality and isomorphism loci found
no duplicate statement for any of the three required obligations.

## New nodes

`lem-pc-qcqs-projection-mate-affine-descent` records the first step of the existing plan:
from all affine-target cases in standard localization universe u+1 to the original
chosen localization universe. Its proof includes descent of arbitrary p and t and
cohomology open-cover detection. It requires the affine result as a premise, so it is
strictly the geometric/localization part of the argument, not the original theorem
under another name.

`lem-pc-qcqs-projection-mate-shifted-unit` records the generator calculation: for any
scheme morphism and arbitrary ambient L, a first factor isomorphic to O[k] has an
invertible supplied mate. It does not assert the result for arbitrary quasi-coherent M.
The main proof supplies the isomorphism for every shifted free module explicitly.

`lem-pc-qcqs-projection-mate-affine-locus` gives only coproduct, third-triangle-vertex
and retract closure of the all-shifts locus. It does not assert membership of any
nonzero object. The existing free-generation theorem performs that essential step
in the main Lean proof. There are no change records or forced adaptations.


## Second reading by F1

1. **Unchanged interface: pass.** Read the full four delivered modules and diffed
   QCqsDerivedProjectionMate against the repository module. The only existing
   declaration is `AlgebraicGeometry.qcqsDerivedProjectionMate_isIso`; its signature,
   universes, compactness/separatedness hypotheses, arbitrary supplied adjunction p
   and comparison t, conclusion, visibility and docstring are byte for byte unchanged.
   The diff consists of five plain proof imports and the replacement proof. There
   are no definition changes, change records or forced adaptations.

2. **Kernel check: pass as a decomposition.** Independently ran lcompile.py --all:
   affine descent, affine locus, shifted unit and the item compiled cleanly (each
   under six seconds). Appended #print axioms for all four public theorems to a
   temporary scratch copy and compiled through lcompile.py. Each showed exactly
   propext, Classical.choice, Quot.sound and sorryAx. The sole three direct sorries
   are precisely the three named obligations listed above, each `:= by sorry`;
   no axiom, unsafe, opaque, implemented_by, extern, data definition or anonymous
   hole was added. The equivalence e is eliminated inside a proof of a proposition,
   and its existing existential theorem identifies its functor with localized
   termwise tilde and its inverse with derived global sections; no arbitrary
   object from an unconstrained existence theorem becomes exported data.

3. **Split statements: pass.** Read [Stacks 08EU](https://stacks.math.columbia.edu/tag/08EU)
   and [Stacks 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q). The former supplies
   the local/affine reduction, coproduct/triangle argument and shifted-ring
   generators; the latter supplies the parent Hom-chain application. Those sources
   use the canonical comparison. The supplied-p,t extension is the agent-written
   naturality/conjugation argument explicitly recorded in the docstrings and nodes.
   Affine descent has the affine theorem as a hypothesis and asserts only its
   geometric/localization reduction; it does not assume or restate the unrestricted
   theorem without a new premise. Shifted unit restricts M to O[k] and leaves L
   ambient; conjugation between the shifted adjunctions preserves invertibility
   by conjugateEquiv_iso, rather than a false general claim about mates. Affine
   locus supplies only closure, not membership or generation. In its five-term
   Hom sequences the four outside vertices are shifts of the first two objects;
   P supplies their invertibility, while naturality at the actual shifted arrows
   supplies the commuting squares, without assuming shift compatibility of t.
   Checked degree zero and negative shifts, zero L and M, zero ring/empty schemes,
   empty coproduct, identity retract, and independent module/scheme localization
   universes. No nonzero-ring or nonempty-cover hypothesis is concealed.

   Repeated searches with different words using msearch.py LeanFinder, Loogle and
   grep (recorded in searches.jsonl), and searched lean/Sheaf, lean/WeilConjectures
   and the relevant DAG nodes. Found conjugateIsoEquiv/conjugateEquiv_iso and
   localization/natural-transformation and sheaf-detection infrastructure, but
   no theorem giving one of these scheme-specific obligations directly. Read
   MonoidalProjectionConjugate, ProjectionComparisonExact,
   RightAdjointTensorComparisonProjection and RightAdjointTensorLocusLocalizing:
   the first pins the monoidal tensorator, and the geometric closure interfaces
   require proper/noetherian hypotheses or the different right-adjoint comparison.
   They cannot replace these obligations with the unchanged parameters. Closing
   any of the three obligations still requires geometric shift/restriction/exactness
   comparisons; none is a few-minute application of the search hits.

4. **Route and pruning: pass.** Read the affine-equivalence and module-generation
   statements. Checked ULift.moduleEquiv, shiftFunctorAdd, hunit(m+n), and the
   inclusion-map composition connecting the chosen generator to B. The zero-shift
   equivalence counit supplies the final membership witness. All five new plain
   imports are actually used. The original five public imports describe the
   unchanged signature; none was removed. Of the nine old proof dependencies,
   affine equivalence and free generation remain direct, six are retained inside
   the descent/closure obligations, and only lem-pc-projection-locality is dropped.
   Its module and two auxiliary modules are listed under No longer needed; this
   means removal from this route, not demonstrated global unreachability.
   Read dag/units/sk-thm-picard-duality.json: realized.statement is [] and its
   sole realized.steps entry is []; this item realizes no designated unit step.
   The existing parent Hom-chain projection-formula step is retained, and neither
   the unit statement nor its realized record changes.

5. **DAG agreement: pass after metadata repair.** The item names the five actual
   dependencies in their order of use, and its proof_origin explicitly records
   three remaining obligations. Every new node has the item's chapter/unit,
   source, self-contained statement, statement dependencies, creation/provenance,
   searches, split status and Lean module/declaration/signature record. Each
   proof_deps list is the union of the uses in its proof steps. Two formal steps
   previously had uses=[] with elementary=false: changed the shifted-adjunction
   conjugation and the five-term exact-sequence calculation to elementary=true,
   spelling out the Mathlib conjugation fact and the five actual Hom vertices.
   Their non-formal geometric inputs remain in the preceding cited steps.

Changes from the second reading: repaired those two DAG step classifications and
expanded their explanations; corrected the report's locality-interface discussion
(the opposite tensor order alone is convertible by braiding). No Lean proof,
statement, definition or import needed repair. Added this independent review.
One original hole is closed by a reduction, three are added, so this remains a
1-to-3 decomposition with net holes closed minus added equal to -2 before the
pinned closure ledger; no claim of an axiom-free proof or net progress is made.
