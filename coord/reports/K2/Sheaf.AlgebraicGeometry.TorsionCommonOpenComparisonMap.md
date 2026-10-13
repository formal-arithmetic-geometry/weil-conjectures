## What changed

Completed `AlgebraicGeometry.torsion_common_open_comparison_map` in
`Sheaf.AlgebraicGeometry.TorsionCommonOpenComparisonMap` with its original signature and
public imports unchanged. Restrict both local models to the common open, identify their
completed arrows with the restriction of δ, apply the existing torsion-controlled lifting
theorem, and transfer the lifted arrow back through the fully faithful over-site equivalence.
Both required families of section equations follow by evaluating actual morphism equalities.

Added two proved helper modules:
`Sheaf.AlgebraicGeometry.CoherentCompletionOverNormalization` and
`Sheaf.AlgebraicGeometry.TorsionLocalModelRestriction`. The former constructs a coherent
over-site restriction and a completion comparison normalized by quotient projections.
The latter constructs the actual restriction of one local model, transports its kernel and
cokernel bounds, and proves both normalization equations. It compares no two local models.

The restriction proof reuses the already proved private `coherent_pullback`,
`completionPullbackIso`, `powerQuotientIso_π`, and `powerProduct_pullback_zero` helpers through
`import all Sheaf.AlgebraicGeometry.FormalSystemsPullback`, and `powerProduct_zero_of_iso`
through `import all Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction`. These are
ordinary checked declarations, not new assumptions. The module constructs the restricted
module explicitly as `restrictFunctor (X.homOfLE h)` applied to F. Its isomorphisms come from
adjunction uniqueness and normalized cokernel comparisons. No library definition changed.

Large natural-isomorphism definitions are generalized during the proofs so the naturality
arguments use their abstract interfaces without repeatedly unfolding the comparison
constructions. No time or resource limit is raised.

The node proof plans and proof dependencies now follow this Lean assembly. The unit
`sk-thm-p1` and all its realized statements and steps are unchanged. Source read:
[Stacks 0889](https://stacks.math.columbia.edu/tag/0889), especially the opening locality
argument, and [completion equation 0880](https://stacks.math.columbia.edu/tag/0880).

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.torsion_common_open_comparison_map`
(node `lem-weil-pbc-torsion-common-open-comparison-map`): 1 of 1 original sorries.

Also proved the new `AlgebraicGeometry.coherentCompletion_over_normalization`
(node `lem-weil-pbc-coherent-completion-over-normalization`) and
`AlgebraicGeometry.torsionLocalModel_restriction`
(node `lem-weil-pbc-torsion-local-model-restriction`). Its private helper
`coherent_of_iso` is proved as well.

No sorry remains in any delivered module. No hole is added or split off. Existing imported
library theorems may themselves depend on sorry; this delivery uses their stated interfaces
and the proved restriction helpers, as stage 3 requires.

Edge cases checked against the constructions: there is no covering, nonemptiness or
affineness premise; the empty common open uses the same categorical constructions.
The zero ideal gives the original quotient objects and the unit ideal gives zero quotients.
The positive annihilation exponent is retained from the supplied bound, rather than inferred
from a stronger hypothesis. An empty index type cannot supply i or j and causes no exception.

## No longer needed

Removed these direct proof imports from the original item:

- `Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover`;
- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`;
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`;
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The old item proof dependencies omitted from the new direct `proof_deps` are:

- `lem-weil-pbc-coherent-module-local-on-open-cover`;
- `lem-weil-pbc-formal-systems-pullback`;
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`;
- `lem-weil-pbc-module-restriction-open-immersion-limits`;
- `lem-weil-pbc-module-restriction-open-immersion-colimits`.

Their original direct node dependencies are now mediated by the two proved helper nodes.
The item directly needs only those helpers and
`lem-weil-pbc-torsion-controlled-completion-hom-lift-exists`.

These underlying modules still occur in the helper import closures, so no entire mathematical
node or module is claimed globally pruned. In the new restriction module, removed the earlier
attempt's unused direct imports of `CoherentModuleLocalOnOpenCover` and
`Modules.IdealTimesQuasiCoherentAffineSections`; their statements are not directly used there.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped at a failed naturality rewrite, which was a Lean proof error,
not an unavailable tool. Mapping the δ equation through overMap must first be followed by
the target component of overFunctorMap; its naturality then transports both composites.
Only afterwards can overEquiv, the b/q normalization equations, and the normalized
completion comparison be used. This transport is now written and checked in Lean.

The earlier restriction placeholder has also been completed. Instead of assuming that an
unlabelled restriction comparison has the correct projection normalization, the proof
conjugates the existing tensor-pullback quotient comparison by the unique adjunction
comparison and proves the projection equation explicitly. No statement was changed or found
false. Search found the Mathlib over-site equivalences and restriction functor, but no exact
packaged comparison statement; LeanSearch returned an internal server error, recorded in the
new nodes, while Loogle, LeanFinder, and grep searches succeeded.

## New nodes

`lem-weil-pbc-coherent-completion-over-normalization` records the proved normalization helper
and its exact Lean signature in `CoherentCompletionOverNormalization.lean`. It uses coherence
locality, the locally Noetherian coherence criterion, and the existing normalized formal
restriction theorem applied to the identity completed map.

`lem-weil-pbc-torsion-local-model-restriction` records the proved one-model restriction helper
and its exact Lean signature in `TorsionLocalModelRestriction.lean`. Its proof specifies the
actual restricted object, the over-site comparison isomorphisms, the quotient normalization,
and the transport of the actual kernel and cokernel bounds. Both nodes include the source,
three kinds of search, complete proof steps, and the original item's chapter and unit.

No change record is needed: no existing statement, definition, visibility, or public import
was changed, and no other existing module was adapted.


## Second reading by K2

1. Compared the delivered item with the repository using a file diff and checked the
   complete text from the theorem keyword to `:=`: the existing signature is byte-for-byte
   identical. The existing docstring, namespace, visibility and public import are unchanged.
   The two other modules are new proved helpers. No definition, target statement, existing
   auxiliary module or change record is altered. Verdict: passes interface preservation.

2. Read every delivered proof, including `coherent_of_iso`. There is no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or resource-limit increase in these files.
   `Fw` is the actual restriction `R.obj F.obj`; `aw` is the restricted morphism followed by
   the explicit target comparison. The choice of tensor-pullback adjunction uses the proved
   `nonempty_tensorPullbackAdjunction`, and the comparison follows from uniqueness of left
   adjoints. The normalized completion comparisons are determined by their quotient
   projection equations. Thus no arbitrary object is chosen from a holed existence theorem.
   The main proof cancels the actual epimorphic quotient projections, derives both completed
   arrows from `hδ`, applies the lifting theorem with the transported bounds, and evaluates
   the resulting morphism equalities on every contained open. Compilation and axiom results
   are recorded below.

3. No statement is split off with `sorry`. Checked each new helper against its full Lean
   signature and docstring: normalization handles one coherent module, while restriction
   handles one supplied local model and never asserts the desired two-model comparison.
   Both are strictly smaller parts of the original argument and have proved bodies and
   matching nodes. Checked empty W, W=U, zero F, and zero and unit J: restriction and
   cokernel universal properties still apply; the positive exponent is the supplied one.
   The identity-completion use in normalization needs exponent zero only, permitted by the
   existing formal-restriction theorem. Independent Loogle search for
   `SheafOfModules.IsFiniteType` and LeanFinder search for projection-compatible restricted
   ideal-power quotients found no exact replacement. Grep of both library roots and the
   upstream checkout found the existing formal-restriction/pullback helpers, already reused.
   Another module has a private coherence-isomorphism proof; importing its unrelated derived
   category development would not shorten this argument. Verdict: true helper statements,
   no relabelled hole or new assumption.

4. Read [Stacks 0889](https://stacks.math.columbia.edu/tag/0889), proof of (1), and
   [0880](https://stacks.math.columbia.edu/tag/0880), completion-functor equation. The present
   argument supplies the restriction and comparison needed for the source's Zariski-local
   construction. It reuses the proved quotient and pullback helpers rather than reconstructing
   completion. All proof-only imports are private; the sole public import supplies the
   signature's definitions. Checked `dag/units/sk-thm-p1.json`, including every `realized`
   entry: none is changed or bypassed. The old direct dependencies now occur through the
   helper modules, so no whole module is globally pruned. Corrected `## No longer needed`
   to name all five old direct DAG dependencies, including restriction limits and colimits.
   Verdict: route preserved and pruning report complete.

5. Read all three delivered node records and their dependencies. The item records, in order,
   normalization/restriction, transport of `hδ`, the existing completed-map lift, and faithful
   transfer/evaluation; these are exactly the Lean proof's steps. The normalization node's
   identity-completion specialization matches its code. The restriction node records the
   actual restricted object, comparison maps, projection normalization, quasi-coherent
   kernel/cokernel hypotheses, exact restriction, and the same annihilation exponent. Its
   references to FormalSystemsPullback and TorsionControlledFormalRestriction explicitly
   identify the proved private helpers imported with `import all`; they introduce no
   additional hole. New records have sources, three search kinds (the unavailable service
   is recorded as unavailable), creation and blueprint fields, chapter/unit, and verbatim
   Lean statements. Existing node changes are limited to proof, proof dependencies and
   proof origin. Verdict: DAG agrees with Lean.

Second reading changed only one extra space before the item's proof delimiter and the
report's explicit list of former direct DAG dependencies; the mathematical proofs were kept.


Validation: all three delivered modules compiled in import order with no errors or warnings.
The explicit `#print axioms` scratch check returned exactly `propext`, `Classical.choice`,
and `Quot.sound` for each new helper. The item returned those three plus `sorryAx`, inherited
from the existing completed-map lifting dependency; it contains no direct hole. The required
`deliver3.py --no-push` dry run returned OK and its all-declaration axiom probes passed.
The delivery is classified CODEX because it adds the two proved helper modules and nodes.
