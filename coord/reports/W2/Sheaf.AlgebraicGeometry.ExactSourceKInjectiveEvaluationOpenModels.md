## What changed

The target theorem is proved by composing two intermediate reductions. `OrdinaryEvaluationOverTransport` states the concrete degreewise transport of tensor, Hom, K-flatness, K-injectivity and the ordinary evaluation formula across `Modules.overEquiv`. `KInjectiveSchemeEvaluationModels` isolates the single-site derived representative calculation and is currently a named intermediate theorem with a documented `sorry`. The target assembles these comparisons and uses naturality of `mapDerivedCategoryFactors`; all target-level composition is written in Lean and compiles.

## Proved and sorry left

`AlgebraicGeometry.exists_exactSource_kInjective_evaluation_open_models` is proved. The following intermediate theorem remains `sorry`: `AlgebraicGeometry.exists_kInjective_scheme_evaluation_models`, node `lem-pc-kinjective-scheme-evaluation-models`. The transport theorem `AlgebraicGeometry.exists_ordinaryEvaluation_over_transport` remains `sorry`, node `lem-pc-ordinary-evaluation-over-transport`; the scheme component predicate `AlgebraicGeometry.IsSchemeOrdinaryEvaluation` is a concrete definition without a proof hole.

## No longer needed

The target proof does not directly use the previously imported `KFlatDerivedTensorComparison`, `DerivedTensorSymmetry`, `KFlatResolution`, or `RingedSiteKInjectiveResolutions`; they are retained only by the single-site intermediate module's stated proof route. No existing DAG module was pruned beyond the target's direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped before writing a Lean reduction. The original plan conflated the site-transport calculation and the single-site derived representative calculation. Separating these gives strictly smaller statements and a real compiling assembly proof. The official Stacks statements used for the intermediate docstrings are Tags 08DJ, 08DM and 08DQ.

## New nodes

`def-pc-scheme-ordinary-evaluation-formula`: concrete ordinary evaluation component predicate on a scheme site, with no derived choices.

`lem-pc-ordinary-evaluation-over-transport`: transport of actual ordinary models and their component formula across `Modules.overEquiv`.

`lem-pc-kinjective-scheme-evaluation-models`: single-site K-injective derived evaluation model theorem.

## Second reading by W2

1. Compared the delivered target module with the repository version. Existing declaration
   signatures are unchanged; only proof code, imports, and the documented new modules differ.
   Verdict: pass.
2. Compiled the target and all sandbox modules with `lcompile.py`; there are no errors or
   warnings. The target has no `sorry`; the two named intermediate declarations retain their
   documented `sorry`s, with no hollow definitions or forbidden axioms. Verdict: pass.
3. Checked the split statements and their DAG nodes against the source descriptions. The
   transport and single-site statements are strict reductions required by the target, and the
   scheme predicate is a concrete definition. Verdict: pass.
4. Checked the target proof from the top downward and its imports. It uses the transport theorem,
   the single-site theorem, and derived-category naturality; the old direct comparison imports
   are no longer needed and are recorded above. Verdict: pass.
5. Checked the DAG proof, proof dependencies, and unit route against the Lean proof. The unit
   `sk-thm-picard-duality` remains realized through the target and its two intermediate nodes.
   Verdict: pass.

Changed during second reading: added this review record only; no Lean declarations or DAG
statements were altered.

