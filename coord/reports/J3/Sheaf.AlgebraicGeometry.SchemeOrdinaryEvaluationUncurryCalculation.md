## What changed

Replaced the sorry in `AlgebraicGeometry.schemeOrdinaryEvaluation_uncurry_calculation`
with a complete Lean proof from a strictly lower chain calculation. The proof obtains
an ordinary chain evaluation `e`, rewrites both explicitly uncurried evaluations as
composites with the coefficient augmentations, applies the localization coherence
formula to `e`, and cancels the two localized augmentation maps against their
specified inverses. The existing theorem signature and docstring are unchanged.

Added three modules:

- `SchemeTensorUnitAction`: the actual composite of the complex associator,
  `mapBifunctorMap (id_F) e`, and the complex right unitor. This irreducible definition
  contains no sorry and chooses no data from an existence theorem.
- `SchemeOrdinaryEvaluationChainCalculation`: one remaining named chain calculation,
  with no derived-category hypothesis, a full proof in words, and its own DAG node.
- `SchemeTensorEvaluationLocalizationCoherence`: a proved localization formula for
  arbitrary complexes and any chain map into the single unit. It has no ordinary
  evaluation hypothesis. Two proved private helpers establish the general lax monoidal
  calculation and identify the inverse unit comparison for Q.

Only proof imports were added to the original module. Updated its DAG proof to follow
these steps. No existing definition, statement, or dependent module was adapted.

All four modules compiled together without warnings using lcompile.py --all; the
observed times were 15.3, 6.2, 46.7, and 30.4 seconds respectively. Initially spelling
out the entire complex tensor-action composite in theorem signatures caused expensive
instance elaboration/export. The explicit irreducible action definition gives that
constructed map a small interface, and all files now compile within the fixed limit.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.schemeOrdinaryEvaluation_uncurry_calculation`
(node `lem-pc-scheme-ordinary-evaluation-uncurry-calculation`).

Added one lower hole:
`AlgebraicGeometry.schemeOrdinaryEvaluation_chain_calculation`
(node `lem-pc-scheme-ordinary-evaluation-chain-calculation`, in its own new module).
Its whole proof is exactly `:= by sorry`. It concerns chain maps and coefficient
augmentations only; it omits all localization tensor comparisons and derived coherence.
The existential witness is consumed inside a theorem proof, never selected as the
body of a definition.

Proved the new theorem
`AlgebraicGeometry.schemeTensorEvaluation_localization_coherence`
(node `lem-pc-scheme-tensor-evaluation-localization-coherence`) and both its private
helpers `derived_unit_comparison` and `lax_tensor_evaluation`, without sorry.
Constructed `AlgebraicGeometry.schemeTensorUnitAction`
(node `def-pc-scheme-tensor-unit-action`) without sorry.

This is a decomposition: one original hole closed and one strictly lower hole added,
for net zero new closure holes before considering already imported dependencies.
The ordinary component calculation remains to be formalized; the localization and
augmentation-cancellation parts are complete Lean proofs.

## No longer needed

No original imports or library modules were pruned. The original signature still
needs SchemeOrdinaryEvaluationFormula and CanonicalTensorHomUncurryDifferential.
The old immediate proof dependencies on the ordinary formula, uncurrying differential,
Hom projections, and localization tensor comparison are now carried through the
appropriate lower nodes; all four remain needed transitively. No unit statement or
unit proof step was bypassed.

The discarded same-statement `schemeOrdinaryEvaluation_uncurry_calculation_core`
helper, its attempted node and the earlier trivial private helper are absent from
this delivery. Neither is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report described a core theorem that was not present in its Lean
file and proposed a restatement of the original theorem. A draft restatement was also
rejected by deliver3.py during this session and was discarded. The final reduction is
different: the remaining theorem is a chain calculation with no HasDerivedCategory
binder, and the derived coherence step is separately proved for arbitrary chain maps.

The parent DAG's listed declarations supply constructions and component APIs, but
none states the triple tensor chain calculation. It is now stated as the one remaining
intermediate theorem, instead of pretending those APIs alone finish that calculation.
The original signature does not need correction.

Read the statements and proofs of Stacks Tags
[08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[08DM](https://stacks.math.columbia.edu/tag/08DM), and
[08DQ](https://stacks.math.columbia.edu/tag/08DQ).
The new chain identity isolates the formal evaluation calculation underlying those
constructions; it does not assert their perfectness-dependent isomorphism claims for
arbitrary complexes. Its proof in words treats q+r=0 and q+r nonzero separately.
Zero complexes and the empty scheme give zero component maps, and unboundedness
requires only the same coproduct universal properties. No tensor comparison is inverted.

LeanSearch was unavailable (HTTP internal server error), recorded as unavailable;
Loogle, LeanFinder, repository searches and Mathlib source inspection were used.

A traversal of statement and proof dependencies also found an existing cycle outside
this item's changes:
`lem-weil-pbc-sheaf-algebraic-structures-objects` depends on
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`, whose statement dependency
points back to `lem-weil-pbc-sheaf-algebraic-structures-objects`. The same cycle is
reachable from the original parent in the unchanged checkout. It is reported here for
the maintainer; these nodes are not edited by this delivery. None of the new nodes
has a dependency back to the parent, and the delivered Lean imports compile together.

## New nodes

`def-pc-scheme-tensor-unit-action`, module `Sheaf.AlgebraicGeometry.SchemeTensorUnitAction`:
the explicitly constructed tensor action on F of a chain evaluation into the single unit.

`lem-pc-scheme-ordinary-evaluation-chain-calculation`, module
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationChainCalculation`:
the sole remaining hole, asserting the two augmented chain evaluation identities.
It is strictly the chain-component part of the parent argument.

`lem-pc-scheme-tensor-evaluation-localization-coherence`, module
`Sheaf.AlgebraicGeometry.SchemeTensorEvaluationLocalizationCoherence`:
the proved lax monoidal localization equation for an arbitrary evaluation chain map.

No change records or forced adaptations are needed.

## Second reading by J3

1. **Visible declarations and statements.** I compared the delivered item module against the repository version with `diff`. The existing theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, a heartbeat option, and the proof body changed. The three added modules contain the declarations recorded by their new DAG nodes.

2. **Compilation and proof hygiene.** I compiled all four sandbox modules with `lcompile.py --all`; they compile without errors or warnings. The item theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The sole remaining `sorry` is the named theorem `schemeOrdinaryEvaluation_chain_calculation`, exactly as listed above and paired with node `lem-pc-scheme-ordinary-evaluation-chain-calculation`; no definition contains a `sorry`.

3. **Truth and strength of split statements.** The chain-calculation statement is a strict lower-level reduction: it removes the derived-category hypothesis and isolates the two explicit chain equalities needed by the parent. Its witness is used only inside a theorem proof, so no data is selected from an underdetermined existence theorem. The localization-coherence theorem is stated for arbitrary chain maps and the tensor-unit action is an explicit composite; both are stronger general lemmas used by the parent and have no hidden hypotheses.

4. **Shortest route and pruning.** The parent proof uses the imported ordinary formula, uncurrying differential, chain calculation, and localization coherence, then cancels the fixed augmentation maps by their inverse laws. I found no shorter Mathlib or existing-library theorem for the component calculation. Imports were checked and none can be removed without losing a used declaration; no unit route is bypassed. The DAG proof and `proof_deps` match the Lean proof steps.

5. **Nodes, sources, and unit route.** Each added node has the required statement, source, proof record, searches, Lean declaration, chapter, unit, and creation metadata. The parent node now records the two lower dependencies and the explicit cancellation route. The unit `sk-thm-picard-duality` remains the same and its realized route is preserved. I found no statement or definition change requiring a change record.

**Changes made during second reading:** none to the Lean or DAG files; this section was added to document the checks above.
