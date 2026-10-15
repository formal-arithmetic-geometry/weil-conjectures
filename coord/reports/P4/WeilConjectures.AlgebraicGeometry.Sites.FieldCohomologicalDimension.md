## What changed

Closed the single hole in
`WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension` without changing
any existing signature or public import. Added proof imports for Mathlib Noetherian
schemes, the source library's bounded-exponent reduction and Leray vanishing, and the
new proved `Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk` module.

The argument reduces torsion sheaves to bounded exponent. The geometric bound kills
higher-direct-image stalks above e; the one geometric point over Spec K detects zero.
Additivity preserves the bounded annihilator, so the field bound kills Leray columns
above c. The already proved Leray rectangle bound gives the sum bound.

The new stalk comparison is proved from the existing strict-henselization stalk
formula and chart maximal-ideal lemma. The strict localization ring C has zero
maximal ideal and separably closed residue field, hence is a separably closed field.
Compatibility of evaluation with K → L makes L algebraic over C, hence purely
inseparable over C. Topological invariance after base change gives the comparison
with X_L. Explicit derived-functor isomorphisms identify the formula's bounded-below
homology with ordinary right derived functors and Ext cohomology.

Updated `lem-sc-cd-ground-field` to follow this proof and attach to the source theorem.
Recorded two existing, proved source-library tools as DAG nodes so the route does not
schedule duplicate spectral-sequence or bounded-exponent proofs. No existing
statement or definition changed; no forced adaptations or change records.

Validation: both delivery modules compiled without warnings. After one 60-second
timeout during import cleanup, a diagnostic compile of the helper completed in
39.8 seconds; profiling showed derived-comparison type checking and linting as the
expensive work. The profiling option was removed. Import-direction checks allow all
dependencies.
Edge cases: degree zero is included in the stalk comparison; empty X and c=e=0 need
no additional hypotheses; the purely-inseparable step covers characteristic zero
and positive characteristic uniformly.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure`
(`lem-sc-cd-ground-field`).

Added 0 holes. The new theorem
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure`
(`lem-sc-field-higher-direct-image-stalk`) and all three private helpers are proved.
No `sorry` remains in either delivered Lean file. Nothing is split off unfinished.

The final axiom audit of the item, the new stalk comparison, the existing Leray
bound, and the existing bounded-exponent reduction shows only `propext`,
`Classical.choice`, and `Quot.sound`. Thus the closed theorem's current transitive
proof closure is also sorry-free. An earlier audit before rebuilding the sandbox artifact showed the original
`sorryAx` on the item; after rebuilding both sandbox modules the final audit no
longer does.

## No longer needed

No original import was removed: all four support existing statements in the module.
Second reading removed the redundant direct import of
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` from the new
helper. It is already public through `TorsionSheaf` → `CohomologyColimit` → `HasExt`.
The new helper imports `TorsionSheaf` and ordinary right-derived-functor interfaces,
so it does not import `TorsionCohomologicalDimension`.

Pruned from this item's argument:

- `def-weil-pbc-scheme-conventions` as a proof dependency: it remains a statement
  dependency and is not a step of the proof;

- `def-weil-pbc-relative-separable-closure`;
- `lem-weil-pbc-strict-henselization-pointed-map` and
  `Sheaf.Paper.StrictHenselizationPointedMap`;
- `lem-pc-kbar-pure-insep`: replaced by Mathlib's generic
  `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`;
- `lem-pc-homeo-pure-insep` and
  `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`: replaced by the
  proved source universal-homeomorphism instance and stability under base change;
- `lem-exc-abelian-sheaves-gmodules` and
  `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`: replaced by the surjective
  singleton family of etale points, and direct additivity for the annihilator;
- `thm-sp-grothendieck` and `Sheaf.CategoryTheory.GrothendieckSpectralSequence`;
- `def-sp-convergence` and `Sheaf.CategoryTheory.ExactCoupleConvergence`;
- the separately stated `lem-weil-pbc-abelian-etale-sheaves-grothendieck`,
  `def-weil-pbc-global-sections-functor`,
  `lem-weil-pbc-direct-image-preserves-injectives`, and
  `lemma-weil-pbc-leray-acyclicity` as direct proof obligations: the proved source
  `Etale.subsingleton_H_of_rightDerived_lowerStar` supplies the Leray argument.

The strict-henselization structural-map definition remains needed through the new
stalk-comparison helper. The chart maximal-ideal lemma, strict-local stalk formula, local ring structure,
universal-homeomorphism invariance, torsion filtered union and cohomology filtered
colimits remain needed. The latter two are used by the already proved
bounded-exponent reduction. The compact-support-base-change unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing node's Lean attachment pointed at
`Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField`, a duplicate with
a downstream import path back to this item. Importing it would create a cycle.
The source theorem is now the attachment. The existing source library already
proves the generic Leray vanishing and bounded-exponent reduction, so restating or
proving those constructions was unnecessary.

The planned identification with a chosen relative separable closure is stronger
than needed. Working directly with the strict localization field removes the
pointed-map compatibility proof and the Galois-module equivalence. Its geometric
point still provides the same vanishing test. No mathematical statement was found
false.

## New nodes

`lem-sc-field-higher-direct-image-stalk`: the new, proved stalk comparison module.
Its proof and source citations cover the chart calculation, scalar tower,
purely-inseparable map, strict-local stalk formula, derived comparisons and
cohomological topological invariance. No further work is left in this module.

`lem-sc-leray-vanishing-bound`: records the existing proved theorem
`AlgebraicGeometry.Etale.subsingleton_H_of_rightDerived_lowerStar` in
`WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing`. No new Lean module or
statement is introduced for this existing source result.

`lem-sc-torsion-bounded-exponent-vanishing`: records the existing proved theorem
`AlgebraicGeometry.Etale.subsingleton_H_of_isTorsion` in
`WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing`. No new Lean module or
statement is introduced for this existing source result.

## Second reading by P4

1. **Interfaces: pass.** Compared the complete item with the shared repository by
   `diff -u`. All five existing declaration signatures and their public imports
   are byte-for-byte unchanged; the difference consists of four plain proof imports,
   one private lemma, and the proof replacing the original `sorry`. The helper
   module is new. The existing node changes only `lean`, `proof`, `proof_deps`, and
   `proof_origin`; there is no definition change or forced adaptation.

2. **Proof and trust: pass.** Read both complete Lean files and compiled them in
   import order through `lcompile.py`. No new `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern` occurs. A scratch audit prints only `propext`,
   `Classical.choice`, and `Quot.sound` for the item, the new public helper, and the
   two source reductions. The strict-local field structure comes from the zero
   maximal ideal, with the uniquely determined inverse operation. The chosen
   comparison maps occur inside a theorem proof of `Nonempty`, never in a new
   data definition.

3. **New statements: pass.** No unfinished statement was split off. Checked the
   new stalk comparison against the existing chart maximal-ideal theorem and
   strict-local stalk formula, and against
   [Stacks 03Q9](https://stacks.math.columbia.edu/tag/03Q9) and
   [Stacks 03SI](https://stacks.math.columbia.edu/tag/03SI).
   The algebraic-closure, finite-type, qcqs, torsion and coefficient hypotheses
   match their uses. For an empty source both sides vanish; for the identity of
   an algebraically closed field, including degree zero, the result is the usual
   stalk/global-sections comparison. The characteristic-zero case gives an
   isomorphism of the strict-local field with L; in positive characteristic the
   purely inseparable extension suffices. Fresh LeanFinder, Loogle and local
   searches found no pre-existing exact field-stalk comparison. The other two new
   nodes attach to existing source theorems and add no Lean statements or holes.

4. **Reduction and pruning: pass after report repair.** The upper proof really
   combines bounded-exponent reduction, stalkwise geometric vanishing, additive
   preservation of the annihilator, and the Leray rectangle bound; it does not
   rename the target as a new hole. Each map and pullback in the helper has the
   required orientation. Checked every old `proof_deps` entry: unused ones are
   listed above; chart maximal ideal, structural map, local structure, stalk
   formula, topological invariance, filtered torsion union and cohomology colimits
   remain through the helper or existing bounded-exponent reduction. Added the
   omitted scheme-conventions proof-dependency entry to the report. The unit
   `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`; this item
   replaces no unit realization, and the compact-support-base-change route is
   untouched. Removed the redundant enough-injectives import from the helper.

5. **DAG: pass.** Read all four delivered nodes and checked the Lean attachment
   signatures, sources, created fields, chapter/unit, proof steps and their
   `proof_deps` unions. The field-stalk lemma is the strictly smaller geometric
   comparison used by the item. The Leray and bounded-exponent attachments match
   their source declarations. The item's former duplicate downstream attachment
   is replaced by the theorem whose proof this delivery supplies, without changing
   the mathematical statement.

Second reading changed only the helper's redundant import and report corrections
(pruning completeness and the final, sorry-free axiom audit). No proof repair was
needed. Closed 1 original hole; added 0 holes; 0 unfinished statements split off.
