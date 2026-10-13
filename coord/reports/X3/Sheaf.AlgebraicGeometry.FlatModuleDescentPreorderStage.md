## What changed

Proved `AlgebraicGeometry.exists_isFlatOver_of_isPullback_limit_preorder_stage` in
`Sheaf.AlgebraicGeometry.FlatModuleDescentPreorderStage`, preserving its complete signature.
Added proof-only imports of `Mathlib.CategoryTheory.Filtered.Final` and
`Sheaf.AlgebraicGeometry.FlatModuleDescent`. All pre-existing public imports remain needed by
its statement and remain unchanged.

The proof constructs the directed partial order of pairs `(k,n)`, with order equality or
`k <= k'` and `n < n'`. The first-coordinate projection is monotone and final, proved using
Mathlib's `Monotone.final_functor_iff`. The starting pair `(i,0)` projects definitionally to
`i`. Restricting the cone along its opposite preserves the limit and the affine vertex by
`Functor.Initial.isLimitWhiskerEquiv`. Apply the existing partial-order descent theorem,
then specialize its eventual conclusion to the resulting stage itself. The projection
converts its inequality and canonical pullback directly to the original conclusion.

Updated the existing node's proof, proof dependencies, and proof origin to this route.
No existing statement, definition, signature, or visibility changed. The auxiliary type,
order instances, and monotonicity lemma are private, fully proved proof infrastructure.

## Proved and sorry left

Closed the sole local hole:
`AlgebraicGeometry.exists_isFlatOver_of_isPullback_limit_preorder_stage`
(blueprint `lem-pc-flat-module-descent-preorder-stage`). One of one local sorries closed;
zero holes added or split off. No sorry remains in the delivered module or is added elsewhere.
This is a proof from the existing `AlgebraicGeometry.exists_eventually_isFlatOver_of_limit`
dependency, not a claim that every transitive geometric dependency is now sorry-free.

The construction works when the preorder has distinct mutually comparable elements:
strict increase of the natural-number level prevents antisymmetry from identifying them.
For equal levels only equality is allowed, and the common upper bound always has a larger
level. A greatest original stage causes no problem, since its level can still increase.
The object `(i,0)` gives nonemptiness. Zero modules and empty source schemes are passed
unchanged to the existing descent theorem. The auxiliary index remains in universe `u`.

## No longer needed

No existing import was removed: the original module contained only statement imports.
The following planned direct dependencies are unnecessary for this proof:

- `lem-weil-pbc-filtered-category-exists-directed-final`: its general existential replacement
  is replaced by a concrete directed partial order and a final projection proved here.
- `lem-pc-tensor-pullback-finite-presentation`, module
  `Sheaf.AlgebraicGeometry.TensorPullbackFinitePresentation`: no module is pulled to a
  different initial stage, so preservation of finite presentation is not invoked.
- `lem-pc-pullback-model-flatness-comparison`, module
  `Sheaf.AlgebraicGeometry.PullbackModelFlatnessComparison`: the canonical pullbacks are
  definitionally the same, so no change of cartesian models is needed.
- `lem-pc-module-pullback-identity-composition`: neither of its two theorems is used.
  `Sheaf.AlgebraicGeometry.TensorPullback` remains a public import because its functor occurs
  in the theorem statement; the module itself is not pruned.
- `def-pc-base-change` as a direct proof dependency: no theorem of
  `Sheaf.AlgebraicGeometry.BaseChangeConventions` is used; the canonical pullbacks already
  occur in the unchanged statement. This module remains transitively imported by
  `FlatModuleDescent`, so no global unreachability is asserted.

The retained node dependencies are `lem-weil-pbc-initial-functor-limit` and
`lem-pc-flat-module-descent`. The unit's realized statement and step lists are empty here;
the geometric descent route is retained and no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The general directed replacement in the
original DAG plan needlessly moved the starting stage. A concrete replacement with the
fixed preimage `(i,0)` removes the resulting geometric comparison work.

Searches: LeanFinder found flatness/localization results, but no exact limit descent result;
Loogle confirmed `Monotone.functor`; the prescribed grep service found
`Monotone.final_functor_iff` in Mathlib. Local searches found the existing partial-order
`exists_eventually_isFlatOver_of_limit`, whose full signature was read and reused.
The existing finite-presentation class supplies quasi-coherence automatically.

Read the statements and proofs of Stacks Tags 0032 and 05LY at
https://stacks.math.columbia.edu/tag/0032 and https://stacks.math.columbia.edu/tag/05LY.
The concrete order argument is written and proved by X3; it implements the directed
replacement principle of 0032 in the thin-category case. The flatness argument uses the
existing Tag 05LY theorem. Local literature source files named in the unit record are
absent on this machine, so their source was read online; the unit JSON was read in full.
The requested section I of `coord/delivery-errors.md` is absent in this checkout.

## Second reading by X3

1. I compared the delivered module with the repository version. The theorem signature,
   all existing declarations, and visibility are unchanged; only proof imports,
   private proof infrastructure, and the theorem body differ.
2. I compiled the module with `lcompile.py`; it succeeds without errors or warnings.
   There are no remaining `sorry`s, axioms, unsafe declarations, or hollow definitions.
   The two auxiliary order instances are private proof infrastructure, and the
   projection monotonicity theorem is fully proved.
3. I checked the theorem and the auxiliary construction on edge cases: equal indices,
   incomparable indices, a greatest original stage, zero modules, and empty source
   schemes. The strict natural-number coordinate yields antisymmetry and a directed
   upper bound in every case; `(i,0)` witnesses nonemptiness. The statement remains
   exactly the original one and the proof uses the existing partial-order descent
   theorem without weakening hypotheses.
4. I checked the split-off/node metadata and searched Mathlib and the library for an
   existing declaration of the result. No new theorem was split off, the existing
   node statement is unchanged, and its proof/proof dependencies match the Lean route.
   The removed planned dependencies are listed above; the retained imports are needed
   by the statement or proof.
5. The unit record was checked: its `realized` lists are empty for this node, so no
   unit step is bypassed. The descent route through the existing partial-order theorem
   and initial-limit preservation is retained.

I changed only the proof route and proof-only imports, updated the node's proof metadata,
and added this second-reading record. No declarations or statements were changed, and
no holes were added.
