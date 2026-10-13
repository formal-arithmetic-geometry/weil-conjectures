## What changed

The existing signature of
`AlgebraicGeometry.exists_ordinaryEvaluation_over_comparisons` is unchanged.
Its proof now assembles a natural Hom-complex comparison, the canonical single-unit
comparison, the induced ordinary dual comparison, and a total tensor comparison.
The dual is constructed by applying the Hom functor to the single-unit isomorphism.
No definition or existing statement was changed, and no other held module was adapted.
The monoidal-preadditivity witness is local to the proof, and elaboration options
are scoped to the theorem; no new instance is exposed by the existing module.

Added `Sheaf.AlgebraicGeometry.HomComplexOverEquivProjections` for the remaining
product, differential, and target-naturality argument. Its full proof in words
adapts the existing proved `HomComplexRestrictSchemeTransport` product calculation
to arbitrary over-site complexes and retains the specified projection equations.

Added `Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula` for the remaining
tensor summand calculation. It chooses a termwise Hom comparison with sectionwise evaluation compatibility,
then quantifies over chain-level Hom comparisons pinned on its product projections.
It constructs the dual comparison in its statement using the actual canonical
single-unit map. It asks for the tensor comparison and its evaluation formula;
it does not assert existence or chain-map naturality of a chain-level Hom comparison.

All Lean validation uses `lcompile.py`, followed by the prescribed `deliver3.py`
dry run. Source pages read: Stacks Tags 0A8X (the product Hom complex and signed
differential), 08DL (restriction), 08DM, 08DJ, and 08DQ (ordinary evaluation in the
perfect-complex argument). No perfectness or derived assertion is imported into
the new ordinary statements. Zero complexes and the empty open use the same
product and coproduct universal properties. No arbitrary data are defined by
choosing from an unproved existence theorem: the unit and dual comparisons are
constructed; remaining tensor witnesses are eliminated only in the proposition's
proof.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.exists_ordinaryEvaluation_over_comparisons`
(`lem-pc-ordinary-evaluation-over-comparisons`).

Two remaining holes were added, both with proof exactly `by sorry` and complete
natural-language proofs in their docstrings:

- `AlgebraicGeometry.exists_homComplex_overEquiv_projections`
  (`lem-pc-hom-complex-over-equiv-projections`): product, differential, and
  target-naturality comparison from a natural termwise Hom comparison.
- `AlgebraicGeometry.exists_ordinaryEvaluation_over_tensor_formula`
  (`lem-pc-ordinary-evaluation-over-tensor-formula`): choose a compatible termwise
  comparison and establish the normalized tensor/evaluation calculation for any
  chain-level lift satisfying its projection equations.

The parent combines these strictly smaller statements by actual Lean isomorphism
composition, functoriality, and construction of the single-unit and dual maps.
This is a decomposition, not an axiom-free proof: one original hole closed and
two lower holes added, net minus one. There is no sorry in the parent's proof or
inside a definition. Neither remaining statement alone asserts the parent's
conclusion: the tensor statement assumes the chain-level Hom family, while the
Hom statement contains no tensor/evaluation assertion.

## No longer needed

Removed the parent's proof import `Sheaf.AlgebraicGeometry.TotalTensorOverEquivIso`
and its direct dependency on `lem-pc-total-tensor-over-equiv-iso`. That theorem
asserts only a `Nonempty` isomorphism, without a tensor summand normalization.
The remaining evaluation calculation constructs a comparison with that normalization
using the termwise tensorator; an arbitrary witness of the older theorem is
insufficient for the evaluation formula.

This is removal of one local import, not removal of a module from the targets'
closure: `OrdinaryEvaluationOverTransport` still imports `TotalTensorOverEquivIso`.
No whole module or unit route is claimed globally pruned. The unit record has
empty `realized.statement` and `realized.steps` lists; no prescribed unit step is
bypassed. The Hom-product projection node remains needed. Removed the direct proof import
`Sheaf.AlgebraicGeometry.InternalHomOverEquiv` and parent dependency
`lem-sc-internal-hom-over-equiv`: its existential naturality statement does not
specify a normalization on local linear maps. The remaining lemma constructs the
termwise maps together with evaluation compatibility. Other modules still use
`InternalHomOverEquiv`, so this is also only local pruning.

The other old direct proof dependencies are
`def-pc-ordinary-evaluation-data`, `def-pc-scheme-ordinary-evaluation-formula`,
and `lem-sc-hom-complex-projections`. They are no longer direct proof steps of
the parent: the two definition nodes remain statement dependencies and the
projection node is used by the new intermediate lemmas. Their modules remain
in the import closure. Thus every deleted old proof-dependency edge is accounted
for; only the two comparison imports listed above are actually removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The older total-tensor statement gives an object
isomorphism without the summand compatibility needed by the evaluation calculation;
the original prose implicitly required this extra compatibility. Likewise the
existence of natural termwise Hom isomorphisms does not by itself give their
sectionwise normalization. The remaining lemma explicitly chooses a compatible
termwise comparison before quantifying over its chain-level lifts. The new remaining
lemma spells out that part of the original proof. The starting module also could
not compile locally because the published cache lacked `TotalTensorOverEquivIso.olean`;
no unclaimed module was copied or changed to work around that missing artifact.

The unfinished Hom proof hit the 60-second compile limit. A diagnostic with a
smaller heartbeat budget located repeated unfolding while matching the projection
theorem's direct additive-group instance with the generic categorical differential
lemma's `Preadditive.homGroup`. Abstracting the equivalence, naming all morphisms,
forward construction of the equality, and local irreducibility settings did not
produce a clean complete module. The final delivery leaves the full Hom comparison
as the first intermediate theorem instead of leaving a hole in its attempted proof.
The parent and both intermediate signatures compile. A proved private naturality
calculation and the full constructor attempt are retained locally, outside the
delivered Lean, in
`scratchpad/Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverComparisons/HomComparisonAttemptFinal.txt`;
the scratch draft is not claimed to compile as a whole. No compiler limit or tool
was modified or bypassed.

## New nodes

`lem-pc-hom-complex-over-equiv-projections`, in
`dag/nodes/sec-picard-framework/lem-pc-hom-complex-over-equiv-projections.json`,
records the natural Hom comparison with its projection equations. It is strictly
the first ordinary-complex step and contains no tensor or evaluation assertion.

`lem-pc-ordinary-evaluation-over-tensor-formula`, in
`dag/nodes/sec-picard-framework/lem-pc-ordinary-evaluation-over-tensor-formula.json`,
records the second step: the normalized tensor comparison and its evaluation
component formula, for a Hom comparison already pinned by its projections.
Both nodes retain the parent's chapter, unit and nearest blueprint ancestor;
all recorded Mathlib searches were actually run. LeanSearch was unavailable and
is recorded as unavailable. There are no statement-change records.

## Second reading by M2

1. **Interfaces — pass.** Diffed the sole existing delivered module against the
repository version and compared its theorem signature as bytes, from `theorem`
through the last conclusion before `:= by`: identical. The only existing node
fields changed are `proof`, `proof_deps`, and `proof_origin`. No target,
definition, public import, declaration visibility, or existing signature changed.
The other two delivered modules and their nodes are new; their recorded Lean
signatures occur verbatim in their files. There are no change records or forced
adaptations.

2. **Proof and axioms — pass as a decomposition.** Compiled all three files in
import order with `lcompile.py`: no errors or warnings. Read the actual parent
proof: `hTensor` supplies e and its naturality; the Hom lemma gives b, hb, and
its projection equations; a is the explicit single-complex transport followed
by the inverse unit comparison, d is b at the local unit followed by Hom of a,
and t is c followed by tensor of d. The final evaluation proposition is exactly
the one supplied after these compositions. Choices of e, b, and c are local
witness eliminations inside a proposition, not definitions of arbitrary data.
The only two delivered sorries are the named intermediate theorems, both with
proof exactly `by sorry`. No prohibited declaration or hollow definition occurs.
Scratch `#print axioms` probes check all three public theorems; the dependency
on `sorryAx` remains and is expected for this decomposition.

3. **Intermediate statements — pass.** Read both complete signatures, their
nodes, their docstring arguments, `OrdinaryEvaluationData`,
`SchemeOrdinaryEvaluationFormula`, the proved `InternalHomOverEquiv`,
`HomComplexRestrictSchemeTransport`, `TotalTensorOverEquivIso`, and
`LocalizedOpenTensorEquivalence`. Read Stacks
[0A8X](https://stacks.math.columbia.edu/tag/0A8X),
[08DL](https://stacks.math.columbia.edu/tag/08DL), and
[08DQ](https://stacks.math.columbia.edu/tag/08DQ).
0A8X gives the product and signed differential for arbitrary complexes.
08DL is a derived restriction statement and 08DQ assumes perfectness for its
isomorphism conclusion; here only their underlying ordinary constructions are
used, with the explicit reindexing arguments supplying the comparison. No
perfectness conclusion is claimed for arbitrary P.

For the Hom lemma, the equivalence preserves products and is additive; termwise
naturality identifies each of the two differential summands and each target-map
component. The fixed projections determine the degreewise comparison uniquely,
so the asserted naturality is compatible with its projection equation. For the
tensor lemma, e must be chosen with sectionwise normalization: naturality alone
would not suffice. Its existential e allows precisely that construction. The
hypothesis pins every b on jointly monic product projections, so extra naturality
of b is unnecessary. The canonical a identifies the unit action, and the same
pure-tensor reindexing fixes c and the associator/symmetry identifications.
Checked P=0, F=0, the empty open, and single-degree complexes: the universal
properties still apply; when r+q=0 the component is y*phi(x), and otherwise both
components vanish. No boundedness hypothesis or finite-product substitution is
used. The Hom lemma has no tensor assertion; the tensor lemma assumes b with
specified projections and does not assert its existence or naturality. Neither
merely renames the parent.

Repeated LeanFinder searches with different wording: product-indexed Hom
differential transport, and strong-monoidal preservation of internal-Hom
unit evaluation. Results concerned sheaf product isomorphisms, reindexing of
sheaf maps, or rigid dual pairings; none states either intermediate signature.
Searched the current Lean roots for Hom-complex transport and tensor comparisons;
the restriction theorem only covers complexes restricted from X and provides
neither the required projections nor the target naturality. The tensor theorem
only provides a bare isomorphism. Neither is a direct replacement. The prior
constructor attempts exhibit a substantial elaboration problem, so closing
that hole is not a few-minute repair; I retained the truthful decomposition.

4. **Route and pruning — pass.** The parent first assembles the two smaller
ordinary constructions and explicitly constructs the unit and dual comparisons.
Proof-only imports are plain `import`; the new modules' public imports supply
names appearing in their signatures (including `overEquivFunctorObjUnitIso`).
The old bare Hom/tensor isomorphisms cannot establish the needed normalized
component equations. Checked `dag/units/sk-thm-picard-duality.json`: its realized
statement is empty and its sole realized step is empty; no designated node is
bypassed. No module is claimed pruned from the targets' closure. Completed the
report's accounting for all five old direct proof dependencies, including the
three retained indirectly or as statement dependencies.

5. **DAG agreement — pass.** Parent proof steps match the actual calls and
isomorphism compositions; their union is its new `proof_deps`. The Hom node
records product preservation, the differential calculation, and target
naturality using `lem-sc-hom-complex-projections`. The tensor node records the
choice of normalized e, the tensor/total construction, and the component
calculation using the existing evaluation definitions and projections. Both
nodes are split, retain the chapter/unit and blueprint ancestry, have source,
creation and search records, and point to their new modules and exact signatures.
These remain plans for the two admitted proofs, not claims that those proofs
have been completed.

**Second-reading changes:** completed the missing old-dependency accounting and
added this independent review. No Lean proof or statement needed repair. The
hole count is one original hole closed, two added: decomposition, net minus one.
