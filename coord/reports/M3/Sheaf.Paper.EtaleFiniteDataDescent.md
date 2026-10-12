## What changed

Restored the original header, namespace, public section, theorem signature and docstring of
`Sheaf.Paper.EtaleFiniteDataDescent` after the previous sandbox editing failure. Its proof now
contains no `sorry`. The object clause uses 01ZM (1) and `Etale.exists_stage_of_inverseLimit`;
the morphism and equality clauses use the existing 01ZM (2),(3) declarations. Two proved
private helpers derive the canonical pullback comparison identity from adjunction counits.

The diagram clause descends its objects, chooses a common stage using `Finite.exists_le`,
and applies `finite_diagram_lift_of_models` only to the remaining arrows and relations.
The proof itself verifies finite-presentation and etale properties of the resulting objects,
relations after later base change, and naturality on every path at every later stage.

The covering clause transports joint surjectivity through the inverse natural comparison,
uses the proved `finite_family_joint_surjectivity_stage`, and checks etaleness of every
later arrow by `Etale.of_comp`. The family helper is proved using finite coproducts,
`exists_surjective_of_isLimit`, and `Scheme.Pullback.range_map`. Every object used in this
helper is explicitly constructed; no data is selected from a holed existence theorem.

Existing public signatures, public imports, definitions and visibility are unchanged.
Only a declaration-scoped unused-variable linter setting was added: the original covering
clause's comparison binder does not occur in that clause's conclusion. No forced adaptations
or change records are needed. All three delivered modules compile without warnings.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.etale_finite_data_descent`
(node `lem-weil-pbc-etale-finite-data-descent`), by a complete Lean reduction of all five
clauses. Added one remaining hole:
`AlgebraicGeometry.finite_diagram_lift_of_models`
(node `lem-weil-pbc-finite-diagram-lift-of-models`), whose entire proof is `:= by sorry`.
It concerns only generators and relations with finite-presentation object models already
supplied at one stage. It contains no object descent, etale descent, covering descent or
later-stage permanence assertion. This is a decomposition: one hole closed, one added,
net zero holes for this delivery, not a sorry-free proof of the whole target.

`AlgebraicGeometry.finite_family_joint_surjectivity_stage`
(node `lem-weil-pbc-finite-family-joint-surjectivity-stage`) is proved, with no new holes.
The two private comparison helpers and the private pullback image helper are proved.
There is no `sorry` in any definition or private declaration. Existing imported obligations
are used as the stage-3 brief permits and are not claimed as proved by this delivery.

Edge cases: an empty vertex type uses the nonempty directed index type's common-bound
lemma; an empty arrow or relation type imposes no lifting condition. Cycles in the quiver
are allowed, so its free path category need not be finite. Empty paths are identities.
For an empty covering family, the coproduct is empty and the surjectivity argument forces
an empty target at the selected stage and every later stage. The compiled family proof
handles that case without a nonemptiness assumption on its index type.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.AlgebraicGeometry.LimitAffineTransition`,
`Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs`, and
`Sheaf.AlgebraicGeometry.DescendSurjective`.
The last two remain needed through the proved family helper and are not globally pruned.
The limit-existence theorem is unnecessary here because a limit cone and its proof are
already hypotheses. Its node `lem-weil-pbc-limit-affine-transition` is therefore removed
from this item's proof dependencies; its statement dependency is unchanged.

The covering proof uses the pullback image formula instead of the original explicit
covering-base-change argument. Its proof no longer needs
`lem-weil-pbc-etale-covering-base-change`, `lem-weil-pbc-surjective-base-change`, or
`def-weil-pbc-etale-site` as proof dependencies. The original statement still uses the
etale site and its public import is preserved. Coproduct-family, finite-coproduct qcqs,
and surjectivity-descent nodes remain needed in the family helper. No claim is made
that these nodes have become unreachable from every project target.

Deleted the abandoned sandbox node `lem-weil-pbc-etale-finite-data-descent-remaining`
and all references to the missing `AlgebraicGeometry.finite_data_remaining`; it is
not needed. The temporary `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`
import was also removed. The new model-lifting statement imports finite presentation
rather than etaleness, which its statement does not assume.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox was not a valid delivery: it lacked the namespace, universe/open
commands and public section, referenced the missing `comparison_fst` and
`finite_data_remaining`, and its report incorrectly claimed compilation and a second
reading. Rebuilt the proof and replaced that report; the independent second reader's
section is intentionally absent.

The original plan's covering reduction can be implemented without constructing a
coproduct/pullback comparison. Functoriality proves surjectivity at the limit, and the
pullback image formula plus `sigmaOpenCover` gives actual lifts at later stages.
In particular, projected pairs do not determine points of scheme pullbacks; the proof
uses the image formula to lift the actual point instead.

Searches found no shorter existing result for the remaining model-lifting assertion.
`AffineEtaleFiniteDiagramDescent` requires affine objects and only handles a finite
incoming family, without arbitrary path relations. The proved
`filteredColimit_category_finite_functor_lift` requires a finite category and strict
object/arrow colimit data; the free category on a finite quiver can have infinitely
many paths and the present pullback transitions compose only up to canonical isomorphism.
LeanFinder and local Mathlib/library/DAG searches were used; the current LeanSearch
service returned Internal Server Error, recorded as unavailable rather than a no-match.

The local literature files are absent on this machine. The primary statements were
checked online at [Stacks 01ZM](https://stacks.math.columbia.edu/tag/01ZM) and
[Stacks 07RR](https://stacks.math.columbia.edu/tag/07RR). The node's existing unit route
is retained: 01ZM, 07RP and the finite-coproduct reduction through 07RR. The unit record
`sk-prop-h2` has no separately realized statement or step that this delivery bypasses.

## New nodes

`lem-weil-pbc-finite-diagram-lift-of-models`, in
`Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels`, states only the remaining
fixed-model generator-and-relation lifting argument. Its docstring and node give the
complete proof plan from 01ZM (2),(3), including canonical object transport and empty cases.

`lem-weil-pbc-finite-family-joint-surjectivity-stage`, in
`Sheaf.AlgebraicGeometry.FiniteFamilyJointSurjectivityStage`, records the fully proved
finite-family reduction through the explicit coproduct. Its node proof follows the
compiled argument. Both new nodes use the item's chapter and unit, proper blueprint
provenance, source places, search records and exact Lean signatures.


## Earlier second reading (a previous round; superseded)

1. Compared the delivered item against the repository version. The theorem statement, namespace,
   public section, definitions, and existing declaration signatures are unchanged; the two added
   modules and three node records are new delivery artifacts. Verdict: passed.
2. Compiled all three delivered modules with `lcompile.py --all`; compilation completed without
   errors or warnings. The only remaining `sorry` is the named theorem
   `AlgebraicGeometry.finite_diagram_lift_of_models`, and it has the matching split node and
   complete proof-plan docstring. No forbidden declarations or hollow definitions occur. Verdict:
   passed.
3. Checked the split theorem against its fixed-model generator-and-relation claim and the finite
   family helper against its explicit coproduct construction, including empty finite families and
   empty quivers. Both are true, strictly narrower than the parent target, and not duplicates of
   existing declarations. Verdict: passed.
4. Read the proof top-down. It uses the shortest available reductions and the existing 01ZM/07RP
   declarations, while retaining the unit route through object descent, fixed-model lifting, and
   finite-family surjectivity. Removed imports and proof dependencies are listed above; no
   unnecessary direct import remains. Verdict: passed.
5. Checked the target node's proof, proof dependencies, and proof origin against the Lean proof,
   and checked the new nodes' Lean records, sources, units, chapters, and split status. Verdict:
   passed.

Changed only the report during this second reading. The delivery dry run is currently blocked by
an infrastructure mismatch: the launcher `deliver3.py` imports `refuse_missing` and `source_roots`
from `tools/import_cycles.py`, but the repository copy lacks those functions. The local Lean build
itself is clean.

## Second reading by M3

1. Compared the delivered item module with the repository version. The theorem statement and all
existing declaration signatures are byte-for-byte unchanged; only proof imports, private helpers,
and the proof bodies differ. The two helper modules and their node files are new. Verdict: passed.
2. Compiled all three delivered modules with `lcompile.py`; each compiled without errors. The only
remaining `sorry` is the named public split theorem
`AlgebraicGeometry.finite_diagram_lift_of_models`, with its matching node and proof docstring.
No forbidden declarations or hollow definitions occur. Verdict: passed.
3. Checked the split statements on empty vertex, arrow, relation, and covering-index cases. The
finite diagram statement fixes all object models and only asks for generator and relation lifting;
the family statement constructs an explicit finite coproduct reduction. Both are true and strictly
weaker than the parent target, with no duplicate declaration found in the library. Verdict: passed.
4. Read the proof from the target downward. It uses the existing 01ZM/07RP declarations and the
two new reductions, removes the unused direct imports listed above, and retains the unit route
through object descent, fixed-model lifting, and finite-family surjectivity. Verdict: passed.
5. Checked the item and new DAG nodes against the Lean declarations, including proof dependencies,
origins, chapter, and unit. The route and realized unit remain intact. Verdict: passed.

Changed only this report section during the second reading; no Lean or DAG content was changed.
