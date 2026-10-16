## What changed

Proved `AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`, preserving its
signature, universes and conclusion. Both descent of arbitrary limit classes and
finite-stage detection of vanishing are proved from existing continuity APIs.
No existing definition, visibility or public import changes.

The new proved module `Sheaf.AlgebraicGeometry.FixedBaseCohomologyClassDescent`
implements descent: pass to a final directed index, use the compatible pullback
system, construct its canonical cohomology diagram, apply directed continuity,
extract a representative and cancel the inverse-image comparison isomorphism.
Private congruence utilities, adapted from the library's existing kernel-checked
method, normalize the three compatibility equations. The reindexed diagram and
limit cone are constructed with explicit objects, arrows and projection maps, and
the final definitionally equal proof
is assigned directly for the kernel to check. This avoids the expensive elaborator
conversion exposed by the repair compile; the mathematical argument is unchanged.

The item's vanishing argument restricts the diagram to `Over i`, retains its limit
by initiality, and detects equality with zero in the filtered cohomology colimit.
Finite-stage vanishing now directly applies the existing public theorem
`AlgebraicGeometry.Etale.exists_cohomologyMap_eq_zero_of_isLimit` from
`WeilConjectures.SixFunctors.Etale.Gabber`. The copied private `finiteStageKilling`
helper has been removed, repairing the duplicate-statement return. The import-direction
check confirms this proof-only import creates no cycle. Scheme-map identity transports
are explicit. No other existing module is changed.

Local transparency settings are documented in
`coord/changes/cohomology-continuity-local-transparency.md`. No other existing
module is adapted, and the compiler time limit is unchanged.

## Proved and sorry left

Closed one of the two original holes, with no new holes:
`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit` is proved.
The new intermediate declaration
`AlgebraicGeometry.Etale.exists_cohomologyMap_preimage_of_isLimit` is also fully
proved, not left as a split-off sorry. Its node is
`lem-weil-pbc-fixed-base-cohomology-class-descent`.

The sole remaining sorry is the unchanged original declaration
`AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`.
Its docstring references `lemma-weil-pbc-etale-cohomology-continuity`, but that node's
primary Lean attachment is a different, torsion-coefficient theorem. Its arbitrary
Grothendieck abelian coefficient category is not covered by the available
abelian-group continuity API.

Zero sheaves, empty schemes, degree zero and a one-object index were checked
mathematically. The delivery uses the project's default heartbeat and time budgets. Both
comparison-isomorphism cancellation and the restriction-to-Over argument are
explicit Lean proofs, with no added hypotheses or weakened conclusions.

## No longer needed

No original public import is removed, and no existing DAG node is claimed globally
unreachable. Relative to the returned delivery, removed the proof imports
`Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone` and
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered` from the item: their
finite-stage argument is already provided by the public theorem in `Gabber`.
Removed the duplicate private declaration `finiteStageKilling`; neither duplicate
private helper in `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity` or
`Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` is imported or copied.
This proof also does not use the torsion-only continuity theorem or
`Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent`; neither is imported.

The finite-hypercover class-descent route is not needed for this proof. Descent uses
the already stated compatible-system and directed-continuity APIs, which handle
arbitrary abelian sheaves pulled back from the fixed base. There are no withdrawals.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied a private finite-stage helper already stated word for
word in two Sheaf modules. That was unnecessary: the public
`exists_cohomologyMap_eq_zero_of_isLimit` theorem in `Gabber` has exactly the required
mathematical hypotheses, with the degree argument implicit. The repaired proof imports
and uses it directly, with no new helper or statement change. Its existing node is
`lemma-weil-pbc-finite-stage-killing`.

The source module has no primary top-level `lean.module` attachment in the DAG.
Its blueprint reference `lemma-weil-pbc-etale-cohomology-continuity` primarily attaches
to `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`, whose statement has a torsion
hypothesis and a different indexing presentation. Applying it here would add a
hypothesis. No such weakening is made, and that node is not repointed.

The existing `exists_cofiltered_etale_cohomology_cocone` conclusion specifies its
comparison only on restrictions of base classes. Its colimit property therefore
suffices for finite-stage vanishing but does not directly give canonical pullback
representatives for arbitrary stage classes. The descent proof instead constructs
its canonical directed cohomology diagram using the existing more explicit API.
The original cocone module is unchanged.

Straight definitional conversions between constant/composite functor objects and
iterated inverse images expand large derived-cohomology objects. Repair profiling
localized a 60-second timeout to the final conversion in the new descent module.
Making the diagram objects, arrows, coefficient comparisons and cone projections
explicit, and leaving the final definitional conversion to the kernel, reduced
the diagnostic compile to 32.4 seconds. The compatibility
equations retain their explicit congruence proofs. No new mathematical assumption
or public data definition is introduced, and the time limit is unchanged.

## New nodes

`lem-weil-pbc-fixed-base-cohomology-class-descent` records the now proved first
conjunct of the source-library elementwise continuity statement. Its source,
complete natural-language proof, edge cases, actual searches and matching Lean
signature are recorded. Its proof dependencies are the existing directed
reindexing, compatible pullback, canonical cohomology diagram and directed-limit
continuity nodes. Its module contains no sorry.

Change record: `coord/changes/cohomology-continuity-local-transparency.md`.

## Second reading by W2

1. Compared the entire item with the shared repository using `diff`, then compared
   the three existing declaration signatures as strings: `sectionsFunctor`,
   `isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`, and
   `cohomologyMap_isColimit_of_isLimit` are byte-for-byte unchanged. Definitions,
   universes, visibility and all original public imports are preserved. The three
   added imports in the item are proof-only. No module held by another group is
   changed. Verdict: pass.
2. Compiled both delivered modules in import order with `lcompile.py --all`:
   no errors or warnings. Independently compiled a scratch axiom check importing
   the resulting sandbox modules. Both
   `exists_cohomologyMap_preimage_of_isLimit` and
   `cohomologyMap_isColimit_of_isLimit` have exactly `propext`, `Classical.choice`,
   and `Quot.sound`. The unchanged general-coefficient vanishing theorem also has
   `sorryAx`, as reported above. The new module has no sorry; the item has precisely
   that one original sorry. There are no forbidden declarations or hollow data
   definitions. The private metaprograms construct ordinary congruence terms and
   assign proofs whose types are checked by the kernel. Verdict: pass.
3. No statement is split off with sorry. Read the new proved helper, its docstring,
   and its complete node. It asserts only descent (one conjunct), with the precise
   forward `upperStarComp` comparison; it is strictly part of the original result.
   Checked degree zero, the zero sheaf, empty schemes, and a one-object index;
   nonemptiness follows from cofilteredness. Repeated LeanFinder with the different
   query “Surjectivity of the natural map from stage cohomology to cohomology of an
   inverse limit of schemes”; its eight hits do not supply this theorem. Searched
   the library for preimages, representatives, surjectivity and class descent.
   The closest `exists_cohomology_class_of_isLimit` requires torsion and starts
   with a sheaf at a stage, so cannot replace the arbitrary fixed-base statement.
   `Gabber.exists_cohomologyMap_eq_zero_of_isLimit` does supply the other conjunct
   and is already used directly. Verdict: pass.
4. Read the proof top down and the existing compatible-system, canonical-diagram,
   directed-continuity and Gabber APIs. The class-descent construction uses these
   APIs with explicit diagram and cone data, extracts a colimit representative,
   and cancels an isomorphism. The vanishing proof restricts to `Over i`, keeps
   its limit by initiality, and applies the existing finite-stage theorem. All
   added imports serve these constructions; statements use only the new module's
   two public imports. No old import or old proof dependency of an item node is
   omitted from the report: this source module has no primary item-node attachment;
   the distinct torsion theorem's node is intentionally left unchanged. Inspected
   `dag/units/sk-prop-h2.json`: its `realized` fields do not designate this helper
   or source theorem as a unit statement or step, and its Kummer route is preserved.
   No further short proof of the general-coefficient vanishing theorem was found.
   Verdict: pass.
5. Checked the new node's exact Lean signature, source, proof steps, dependency
   union, origin, searches, creation record, chapter and unit against the helper.
   All four proof dependencies are used. Existing nodes for different theorem
   statements are not repointed. The report accurately counts one original hole
   closed, zero holes added, one original hole remaining, and no globally pruned
   modules. Verdict: pass.

Second-reading changes: added this independent review and axiom evidence; added
an independent alternate-query search to the new node. No Lean repair was needed.
