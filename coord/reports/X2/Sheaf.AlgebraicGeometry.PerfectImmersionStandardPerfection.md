## What changed

Proved `AlgebraicGeometry.perfectImmersion_standardPerfection` in
`Sheaf.AlgebraicGeometry.PerfectImmersionStandardPerfection` with its signature,
visibility, original docstring, and public imports unchanged.

Added three proved private helpers: `standardComplexIso` transports an isomorphism
between Q-images to the standard localization; `standardSinglePerfect` transports
the original local strictly perfect witnesses; `closedDirectImageColimits` obtains
finite-colimit preservation from closed-pushforward cokernel preservation.
The standard tensor unit is definitionally the single structure module. Exact
pushforward commutes with single via the upstream right-derived comparison.
Mapping this comparison through open restriction and composing local witnesses
finishes the proof. No object is chosen from an unproved existence statement.

Added only proof imports:
- `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardCokernel`;
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`.

Updated the item's DAG proof, proof dependencies, and proof origin to this argument.
Both added imports pass `tools/import_direction.py may`.
Local compilation passed without warnings. The argument works with empty schemes,
empty opens, the identity immersion, zero modules, and arbitrary derived Hom universes:
all local transport is through localization equivalences and retains the same K.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.perfectImmersion_standardPerfection`
(node `lem-sc-perfect-immersion-standard-perfection`).
All three private helpers are proved. No sorry remains in the item; no holes were
added, and no statements were split off. This is a proof, not a decomposition.
Existing dependencies retain their existing holes. The scratch `#print axioms` check
shows `sorryAx` in the completed theorem through the pre-existing
`AlgebraicGeometry.schemeDerivedTensorMonoidal` construction. All three new private
helpers, `closedImmersion_pushforward_preservesCokernel`, and
`Functor.singleFunctorCompRightDerivedFunctorIso` use only `propext`,
`Classical.choice`, and `Quot.sound`. Thus the local hole is closed, but the theorem
is not yet axiom-closed in the full library.

## No longer needed

No original imports were removed: all four public imports supply parts of the
unchanged statement. No modules are claimed pruned from the target closure.
The node no longer directly depends on `lem-weil-pbc-closed-pushforward-stalks`
(`Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`); it instead uses
`lem-weil-pbc-closed-immersion-pushforward-cokernel`, whose already proved argument
uses those stalks transitively. The stalk module is therefore still needed there.
The proposed global restriction-versus-localization comparison, and a fresh
K-injective-resolution computation of exact pushforward, are unnecessary here.
No realized unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox held only the unchanged original hole. The original DAG's
mathematics is correct, but its first step can be simplified for a single module:
commute restriction with single first and compare Q-images only in each local
category. Its second step need not repeat the stalk proof or construct a new
resolution comparison: the existing proved cokernel theorem and upstream
`Functor.singleFunctorCompRightDerivedFunctorIso` supply the result.

The cokernel lemma belongs to another unit and is used solely as a general tool
for exactness of module pushforward; the item's unit has no alternative theorem
for it. The maintainer may record this tool use if required. No interface change,
forced adaptation, new node, or change record is needed.


## Second reading by X2

1. Compared the delivered module with the repository using `diff -u`, and checked
   the original theorem signature byte for byte up to `:=`: identical. Its original
   docstring, visibility, and all four public imports are unchanged. The only added
   declarations are private helpers, and both new imports are plain proof imports.
   No definition or statement used by another module changed. Verdict: pass.
2. Compiled the module through `lcompile.py`: no errors or warnings. Scanned the
   delivered Lean for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and
   `extern`: none. Compiled a scratch copy with `#print axioms` for the target,
   the three private helpers, the cokernel theorem, the exact-functor single
   comparison, and the derived tensor construction. The helpers and comparisons
   use only the three permitted axioms; the target additionally uses `sorryAx`
   through the pre-existing derived tensor construction, as recorded above.
   The localization equivalence supplies determined data; no arbitrary witness
   is chosen from an unproved existence theorem. Verdict: pass for stage 3,
   with the existing dependency hole explicitly retained.
3. No statement was split off and no new node was added. Read the private helpers
   against `Scheme.IsPerfect`, `Localization.uniq`, `compUniqFunctor`, and the
   exact-functor single comparison. All isomorphisms have the required direction,
   and the witness complex and its strict-perfectness proof are unchanged.
   Empty schemes make the pointwise conclusion vacuous; an empty open cannot
   contain the chosen point; zero modules and the identity immersion require no
   exceptional construction. Verdict: pass.
4. Searched the project roots for perfection transport, standard-model perfection,
   and exact closed pushforward, and read the upstream exact-functor comparison.
   The proof already uses the short established comparison rather than a fresh
   resolution calculation. Both added proof imports are used. Checked every old
   `proof_deps` entry: only the direct stalk dependency is replaced, and it is
   fully listed under `No longer needed` while remaining needed transitively.
   Read `dag/units/sk-thm-picard-duality.json`: its `realized` record is unchanged;
   this item does not replace a realized unit step. The cokernel theorem is a
   general exactness tool, not a replacement for the unit's duality argument.
   Verdict: pass; no module is claimed pruned.
5. Compared the node JSON with its repository version: only `proof`, `proof_deps`,
   and `proof_origin` changed. Its three proof steps describe respectively the
   local localization transport, exact pushforward, and final local witness
   composition. Their `uses` union equals `proof_deps`; the unchanged Lean record
   matches the unchanged public signature. Verdict: pass.

Second reading changed only this report: recorded the precise inherited axiom
limitation and these review results. No Lean or DAG repair was necessary.
