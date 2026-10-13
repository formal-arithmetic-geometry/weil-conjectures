## What changed

Reduced the sole hole of `Sheaf.Paper.ModuleCupGlobalTensorPullback` without changing
its existing theorem or diagram definition. Its complete Lean proof combines the
ordinary global pullback data with the derived tensor data, retaining the original
K-flat normalization and absolute postcomposition clauses.

Added three modules, one theorem per module:

- `Sheaf.Paper.GlobalTensorPullbackUnderivedData`: proved the transport of concrete
  ordinary pullback through point evaluation. The proof uses
  `RingedSpace.globalSectionsFunctor_isEquivalence_of_unique`,
  `RingedSpace.exists_tensorModulePullback`, composition of adjunctions, and the
  identity-linear-map comparison of pushforward followed by point evaluation
  with global sections. Object and morphism equations are proved by substitution,
  and additivity is inferred for the composite of additive functors.
- `Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization`: split off the ordinary
  strong tensor constraint and its concrete section-tensor/counit normalization.
- `Sheaf.Paper.GlobalTensorPullbackDerivedData`: split off the absolute K-flat
  derived tensor comparison for the already supplied ordinary pullback functor.
  The normalization is stated as the actual morphism equation, avoiding an import
  cycle with the original diagram definition.

All four modules compile individually through the launcher in dependency order,
without warnings. The original module's parsed existing signatures are unchanged.
The two remaining statements were checked on the empty scheme, zero modules and
zero complexes; none requires exactness of ordinary pullback or boundedness.
No data is defined by choosing a witness from an unproved existence theorem.
Witnesses are eliminated solely inside theorem proofs.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.globalRingedSpace_derivedTensor_pullback_comparison`
(blueprint `lem-sc-module-cup-global-tensor-pullback`). There is no sorry in the item.

Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_underived_data`
(node `lem-sc-global-tensor-pullback-underived-data`) from existing declarations
and the strictly smaller monoidal normalization statement.

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.Modules.globalTensorPullback_monoidal_normalization`
  (node `lem-sc-global-tensor-pullback-monoidal-normalization`).
- `AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_derived_data`
  (node `lem-sc-global-tensor-pullback-derived-data`).

This is a decomposition of one original hole into two lower holes, not a
sorry-free proof. Holes closed: 1; holes added: 2; net: -1. The normalization hole
asserts no derived functor, while the derived hole constructs no ordinary functor
or adjunction and asserts no ordinary counit normalization. The ordinary transport
and the Lean proof assembling all data are complete.

## No longer needed

Removed the original module's proof imports of
`Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived` and
`Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute`; their uses now belong
respectively to the proved ordinary transport and to the remaining derived step.
They remain dependencies of the delivery, so no module is pruned from the import
closure. No public import of the original module was removed or changed.
The second reading also removed the redundant public import of
`Sheaf.Paper.ModuleCupNaiveMap` from the new derived-data module: its signature
uses no declaration from that module, and its tensor infrastructure is already
provided by `Sheaf.AlgebraicGeometry.DerivedTensorStructure`. This does not prune
a module from the targets' closure, since ordinary normalization still needs it.

The original node now has direct proof dependencies only on
`lem-sc-global-tensor-pullback-underived-data` and
`lem-sc-global-tensor-pullback-derived-data`. Its earlier dependencies remain
needed below these nodes or as notions in its statement:
`def-pc-global-derived-rhom`, `lem-pc-ringed-space-tensor-pullback-underived`,
`lem-sc-module-cup-naive-map-chain`, `lem-pc-ringed-space-tensor-pullback-absolute`,
`lem-pc-kflat-pullback-preservation`, and `def-pc-scheme-derived-tensor-structure`.
No existing node is claimed to have become globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies supply concrete ordinary pullback and its absolute
left derivation on ringed-space modules. They do not directly supply transport
through point evaluation, a strong monoidal structure normalized by the concrete
section tensor map, or the normalized derived tensor isomorphism. The transport
is now proved in Lean; the two missing comparisons have separate statements.

The upstream `LeftDerivedFunctor.Monoidal` comparison requires ordinary exactness,
which global pullback need not have. It cannot justify this statement unchanged.
No mathematical error in the original statement or unit route was found. No
existing statement, definition, chapter route or unit route was changed.
LeanSearch returned Internal Server Error; the other searches and source grep
were completed and recorded without treating that service failure as a verdict.

## New nodes

`lem-sc-global-tensor-pullback-underived-data` records the proved point-evaluation
transport of the concrete functor and adjunction, followed by normalization.
Its module is `Sheaf.Paper.GlobalTensorPullbackUnderivedData`.

`lem-sc-global-tensor-pullback-monoidal-normalization` records precisely the
ordinary tensor/counit comparison needed after that transport.
Its module is `Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization`.

`lem-sc-global-tensor-pullback-derived-data` records the absolute derivation and
canonical bifunctorial tensor comparison for a supplied concrete global pullback.
Its module is `Sheaf.Paper.GlobalTensorPullbackDerivedData`.

Each inherits the item's chapter and unit and records the source, complete proof
in words, exact Lean signature and searches. The original node's proof and direct
proof dependencies follow the actual new Lean proof. No change record is needed:
existing signatures, definitions and visibility remain identical.

## Second reading by E4

1. **Existing interfaces: PASS.** Read the full repository/sandbox diff. Its only
   changes to the existing module are two private proof imports and the theorem
   body. The existing diagram definition, local instances, options, declaration
   visibility and theorem signature are unchanged byte for byte. The declaration
   scanner also reports no changed signatures. There are no forced adaptations
   or changes requiring a change record.
2. **Proof and trust: PASS as a decomposition.** Compiled all four modules in
   dependency order with `lcompile.py`, then compiled scratch copies with explicit
   `#print axioms` for all four theorems and the diagram definition. Every probe
   succeeded without warnings. The diagram definition uses only `propext`,
   `Classical.choice`, `Quot.sound`; the four theorem declarations additionally
   use `sorryAx`, as expected from the two named open statements and upstream
   open results. Scanned the complete delivered sources: exactly two `sorry`s,
   each the whole proof of its reported public theorem; no forbidden declaration,
   hidden hole, or definition selecting an arbitrary unproved existence witness.
   The ordinary functor is the concrete composite `e.inverse ⋙ T`, constructed
   inside a proposition proof. Identity-linear-map components give the comparison
   of direct image followed by evaluation with global sections; the composed
   adjunction and object/map substitutions compile.
3. **Split statements: PASS.** Neither new hole restates the item. Ordinary
   normalization constructs no derived functor; derived data assumes the supplied
   ordinary functor and constructs neither it nor its adjunction or normalized
   ordinary constraint. Read their full signatures, word proofs and matching
   nodes. Checked the empty scheme, zero modules/complexes, and the one-point
   case. On a point with a counit rescaled by an invertible scalar c, transport
   gives tensor constraint c and unit c-inverse, so the counit equation remains
   valid for the arbitrary adjunction in the normalization theorem. Exact point
   evaluation and inverse image, K-flat pullback and total tensors give the derived
   comparison without asserting exactness of scalar extension. Independently
   checked [Stacks 079U](https://stacks.math.columbia.edu/tag/079U) for the tensor
   isomorphism and [0FP0](https://stacks.math.columbia.edu/tag/0FP0) for its polygon,
   and Tags 008A/008Y for the component adjunctions. Repeated searches with new
   terminology through Loogle, Lean Finder, and grep (logged in `searches.jsonl`),
   and searched both Lean roots. Mathlib's `map_μ_comp_counit_app_tensor` requires
   an already compatible monoidal adjunction; it does not construct the normalized
   strong tensor constraint. The upstream derived tensor comparison requires
   finite-limit preservation (ordinary exactness), and scheme pullback results
   require a scheme morphism. Neither supplies these ringed-space/global-point
   statements directly. No hole could be closed by a short application found.
4. **Route and pruning: PASS after import repair.** The item combines the proved
   ordinary transport with the separate derived comparison, retaining every
   original counit, absolute postcomposition, K-flat invertibility, naturality and
   normalization clause. Removed the new derived-data module's redundant public
   `ModuleCupNaiveMap` import; recompilation of its scratch copy passed. The
   report accounts for all six former direct proof dependencies: they remain as
   lower dependencies or statement notions. No module is globally pruned.
   Read `dag/units/sk-prop-av-cube.json`; the item is below the unit level and is
   absent from its `realized` entries. No unit statement, step, route or record is
   changed.
5. **DAG agreement: PASS after metadata repair.** Compared the old/new item node
   and read all three new nodes. The item's two direct dependencies are exactly
   the two theorems its Lean body applies. Ordinary transport names evaluation,
   concrete pullback and normalization. The two remaining nodes record their
   actual remaining arguments. Verified that each `proof_deps` equals the union
   of its steps' `uses`, and every new node has source, word proof, searches,
   status, provenance, blueprint ancestry, chapter, unit and Lean record. Replaced
   whitespace-collapsed new Lean signatures by their exact multiline source text.

Second reading changed only one redundant import, the new ordinary-transport
proof docstring (it now accurately says it applies the normalization theorem),
verbatim signature formatting in the three new nodes, and this report. No proof
term, existing statement, definition, or hole count changed. The outcome is one
original hole closed by decomposition into two named lower holes, net -1; it is
not a sorry-free proof of the original theorem.
