## What changed

Replaced the body of
`CategoryTheory.ConstantCompletion.completedKoszulDualTowerPullback` by a complete
Lean assembly of two distinct construction steps: the augmented positive Koszul
diagram comparison and ordinary finite free complex duality. Its signature is
unchanged. Added proof imports of `Sheaf.Paper.CompletedPositiveKoszulPullback`,
`Sheaf.Paper.FiniteFreeComplexDualPullback`, and an `import all` of
`Sheaf.CategoryTheory.RingedCechKoszulDualKFlat` to reuse its already proved private
`koszulDiagram_finiteFree` helper. No existing shared module was changed.

The private proved lemma `dualizeAugmentedDiagram` constructs the dual diagram
comparison in arbitrary categories. Its components are the finite dual comparison
followed by Hom of the inverse positive comparison. The proof checks naturality
using the inverse positive comparison, and checks the coaugmentation by moving the
positive projection through the natural dual comparison and cancelling the
positive isomorphism. In particular, it handles the prescribed arbitrary `j`
rather than silently replacing it by a canonical unit isomorphism.

The new finite dual statement concerns arbitrary coefficient maps and arbitrary
termwise finite free source complexes, with target the ring in degree zero; it
contains no Koszul diagram, completion or transitions. The new positive statement
contains the positive tensor diagram, transitions and projections, but no duals
or internal Hom. These are complementary steps of the original source argument,
not a new name or repackaging of the original augmented dual tower statement.

Read the finite dual argument of Stacks algebraization.tex,
lemma-derived-completion-koszul (Tag 0A0E), and the ordinary tensor and internal-Hom
pullback constructions in sites-modules.tex. Checked the unit's realized route in
`dag/units/sk-lem-integral-models.json`; this reduction stays within that route.
Mathlib searches and project/blueprint searches found no exact replacements.
Existing finite-free Hom comparison for etale/proetale comparison and the
continuous-site dual free chart theorem have additional geometric/site-map
hypotheses and do not supply the general inverse-image theorem here.

Validation: both new theorem modules compile. The final item module compiles via
`lcompile.py` in 18.3 seconds. No profiler options, new global definitions,
statement changes, or source-library changes were introduced.

## Proved and sorry left

One original hole is replaced by a complete proof from two lower statements:
`CategoryTheory.ConstantCompletion.completedKoszulDualTowerPullback`
(node `lem-sfb-completed-koszul-dual-tower-pullback`). There are zero `sorry`s
left in the item module. This is a decomposition, not a proof with zero added
holes: one original hole closed, two holes added, net minus one.

The two added holes, each the entire proof of its named public theorem, are:

- `CategoryTheory.ConstantCompletion.finiteFreeComplexDualPullback`
  (`lem-sfb-finite-free-complex-dual-pullback`), in
  `Sheaf.Paper.FiniteFreeComplexDualPullback`.
- `CategoryTheory.ConstantCompletion.completedPositiveKoszulPullback`
  (`lem-sfb-completed-positive-koszul-pullback`), in
  `Sheaf.Paper.CompletedPositiveKoszulPullback`.

Each new declaration has its complete proof in words and source in its docstring,
and its matching DAG node. The actual combination of the parts, including the
normalization equation, has no holes. Finite freeness of the positive terms is
reused from the existing proved helper, including r=0 for the ring single complex.

Edge cases checked mathematically: no generators; zero or repeated generators;
zero ring and empty sites; finite rank zero; arbitrary invertible rank-one
normalization j. In the finite dual statement, no boundedness of the source is
needed because the target single complex leaves only one potentially nonzero
product factor in each degree. Finite free dual base change needs no flatness of
the coefficient map.

## No longer needed

No existing imports were removed; the public statement import is still necessary.
No modules or declarations are withdrawn or claimed to be pruned from the targets.

The item's direct proof no longer invokes
`lem-sp-completed-pullback-adjunction` or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; those entries are replaced in
its `proof_deps` by the two new lower lemmas. Ordinary tensor comparison is needed
in the lower positive/finite-dual steps, recorded through
`lem-sfb-ringed-complex-tensor-pullback`; that existing theorem already supplies
module adjunction and total-tensor preservation. Thus these direct dependency
removals are not assertions that their modules are transitively unused.

The same-site restriction theorem `strictScalarKoszulComparison` and the
negative-Koszul-coordinate theorem are not imported: they do not compare the
arbitrary two sites in this item. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The old proof plan described
coordinates but had not provided the cross-site duality interface needed to turn
that description into chain isomorphisms. The updated plan separates ordinary
finite free duality from the positive tensor construction and records the actual
contravariant assembly. Two lower construction proofs remain open and are not
represented as already proved by tensor pullback alone.

## New nodes

`lem-sfb-finite-free-complex-dual-pullback` records ordinary inverse image of
termwise finite free dual complexes, source naturality and evaluation
normalization. Its proof reduces to the single surviving Hom product factor in
each degree, ordinary finite free module duality, and the Hom differential.

`lem-sfb-completed-positive-koszul-pullback` records the augmented positive Koszul
diagram comparison. Its proof is induction over the two-term factors using
constant-scalar compatibility and ordinary tensor pullback, followed by scaling
the canonical comparison to the specified rank-one normalization.

Both nodes belong to the item's chapter and unit, and cite the same blueprint
ancestor and finite Koszul calculation. No change record is needed: all existing
signatures, definitions, attributes and public imports are unchanged.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
