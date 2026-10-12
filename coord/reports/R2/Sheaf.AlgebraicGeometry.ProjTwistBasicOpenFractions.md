## What changed

Replaced the hole in `AlgebraicGeometry.Proj.single_twist_basicOpen_fractions` with a
construction of the additive chart from its uniquely determined pointwise representative.
The proof establishes additivity, injectivity, the range equality, scalar compatibility and
restriction compatibility. Added three proof imports and three intermediate modules.
`twist_fraction_realization` is proved directly using `degreePart.mk` and
`isLocallyFraction_mk`, including negative shifted degree and nilpotent denominators.
No existing statement or definition changes. The node proof now follows the Lean argument.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Proj.single_twist_basicOpen_fractions`.
This is a decomposition into two remaining holes, rather than a sorry-free proof of the
original result. Also proved `AlgebraicGeometry.Proj.twist_fraction_realization` without sorry.

Added exactly two holes:
- `AlgebraicGeometry.Proj.twist_fraction_descent`
  (`lem-sc-proj-twist-fraction-descent`).
- `AlgebraicGeometry.Proj.basicOpen_localization_detection`
  (`lem-sc-proj-basic-open-localization-detection`).

The representative is selected inside a theorem, not a definition. Its pointwise values
uniquely determine it by localization detection, which is also used to prove additivity.
No arbitrary data from an existence-only theorem enters a public definition.

## No longer needed

None. The two original public imports are needed by the unchanged statement. All three
added proof imports are used. No original nodes or modules are pruned; the original
finite-cover route remains in the descent node, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node's first step had no stated intermediate declarations for fraction descent
or detection in ordinary localization. The delivery isolates these arguments and proves
the chart and both compatibility formulas from them. A trial proof of detection by simply
passing equality from a homogeneous core to the original prime had the localization direction
wrong and was discarded. The remaining node instead records the graded-component and
homogeneous-annihilator argument. Search found no exact chart theorem in Mathlib or the source
library. LeanSearch was unavailable; LeanFinder, Loogle and source searches ran successfully.

## New nodes

`lem-sc-proj-twist-fraction-descent`: every twist section over a positive-degree basic open
has a shifted homogeneous representative with the prescribed pointwise values. This is the
finite-cover descent part of the original argument and is left for the next worker.

`lem-sc-proj-basic-open-localization-detection`: homogeneous primes of a positive-degree basic
open detect equality in the ordinary localization. This is independent of the twist and
provides uniqueness and the final equality checks. It is left for the next worker.

`lem-sc-proj-twist-fraction-realization`: a shifted homogeneous fraction defines a twist
section with prescribed values. This is proved, including negative numerator degree, and
supplies the reverse range inclusion. No change record is needed: existing signatures and
public imports are unchanged.

## Second reading by R2

1. **Interface and unchanged statements.** I compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; the added declarations are the two strictly smaller reductions named in the report and the constructive realization lemma. No target hypothesis, conclusion, or definition was altered.

2. **Compilation and trust.** I compiled all four delivered modules with `lcompile.py --all`; they compile without errors or warnings. The only remaining `sorry`s are the named declarations `twist_fraction_descent` and `basicOpen_localization_detection`; no definition contains `sorry`, and no forbidden axiom-like declaration occurs. Explicit `#print axioms` in a scratch copy showed only `propext`, `Classical.choice`, and `Quot.sound` for `twist_fraction_realization`; the target and the two open reductions additionally use only `sorryAx`, as expected. The scratch copy was removed before delivery.

3. **Truth and strength of split statements.** `twist_fraction_descent` is exactly the existence-and-pointwise-representative part of the source’s basic-open fraction argument, including negative shifts and nilpotent denominators. `basicOpen_localization_detection` is exactly the uniqueness/detection part needed to compare representatives, with the positive-degree and homogeneous hypotheses required by the Proj basic-open statement. The realization lemma is proved directly from `degreePart.mk` and `isLocallyFraction_mk`; its statement has no unnecessary positivity assumption. I checked the zero/negative-degree and nilpotent cases in the realization proof and the empty-open behavior described by the source.

4. **Proof route and pruning.** The target proof uses the three imported intermediate declarations exactly where the DAG plan says: descent supplies representatives, detection supplies uniqueness/additivity/injectivity and compatibility, and realization supplies reverse range inclusion. The unit’s source route is retained in the descent statement; no old proof dependency or import became unused, so nothing was pruned.

5. **DAG agreement.** The target node’s `proof`, `proof_deps`, and `proof_origin` match the Lean proof. Each new node has its own module, declaration, source, proof plan, search record, and split status. The remaining holes are reported by declaration name and correspond to their node files.

I repaired the detection docstring and matching node proof: injectivity of homogeneous localization into ordinary prime localization is justified using the grading map and McCoy’s criterion, before separating homogeneous components. I removed stray comment terminators from two node proof texts and restored the original spacing before the target proof delimiter. No Lean statement or definition changed.
