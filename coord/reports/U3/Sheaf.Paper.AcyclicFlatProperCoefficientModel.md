## What changed

Proved `AlgebraicGeometry.Etale.acyclicFlatProperCoefficientModel` using the existing
bounded-flat K-flat criterion, bounded-below acyclic-complex computation, canonical
unbounded comparison, and derived-adjunction unit and counit identities. The square
uses the prescribed scalar/pullback normalization and the ordinary coefficient mate.
The six naturality identities follow from the corresponding natural transformations.
All original public signatures are preserved.

The coefficient chain map is constructed degreewise from the ordinary mate, with
differential compatibility given by naturality. This replaces composition
isomorphisms with the same explicit components.

The acyclic comparison and scalar representative are assembled as natural
transformations before evaluation. They now specialize the generic constructions
directly, without redundant transports by reflexive functor equalities. The
ordinary scalar adjunction is exposed through a generic representative
transformation in `Sheaf.Paper.EtaleDerivedScalarTensor`. That unclaimed module
retains its original public signatures and canonical maps.
The ordinary complex counit is also exposed through a private natural-transformation
interface before evaluation, keeping the concrete complex functors consistent in
the mate calculation.

The coefficient square uses a fully proved private categorical pasting lemma,
combining the six existing normalization, naturality, and counit identities before
specializing to sheaves. This avoids repeated expensive concrete functor comparisons.
The complete repaired item compiles cleanly in 50.9 seconds through `lcompile.py`.

The definition changes, consumers, and unchanged meanings are recorded in
`coord/changes/U3-acyclic-comparison-canonical-complex-instance.md` and
`coord/changes/U3-scalar-representative-natural-transformation.md`, and
`coord/changes/U3-proper-coefficient-degreewise-map.md`.

## Proved and sorry left

Closed the one assigned hole:
`AlgebraicGeometry.Etale.acyclicFlatProperCoefficientModel`
(node `lem-sp-acyclic-flat-proper-coefficient-model`). Added zero holes and split off
zero statements. No sorry remains in the assigned module.

The adapted scalar-interface module retains its pre-existing hole
`AlgebraicGeometry.Etale.scalarTensorIso_existsUnique`
(docstring blueprint `lem-pur-derived-change-of-rings`), unchanged. This proof does
not use that tensor-isomorphism theorem. No hole is added to any definition.

## No longer needed

Removed the following direct proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.RingedTopoiDerivedPullback`

Removed these planned proof dependencies and their obsolete `tool_uses` entries:

- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pur-derived-change-of-rings`
- `def-kun-derived-tensor`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`

The source library already supplies the relevant structures and canonical derived
adjunctions for `Sheaf smallEtaleTopology (ModuleCat A)`. Its proved bounded-flat
criterion applies directly. No separate module-sheaf equivalence, general SheafOfModules cochain-model theorem, new K-flat
resolution, or derived tensor associativity result is needed. The unused equality support declarations from the returned packet
(`acyclicProperPushforward_eq`, `scalarRepresentativeComplexFunctor`, and
`scalarSheafRepresentativeComplexFunctor_eq`) are no longer introduced.
Statement dependencies
are preserved, including the tensor/pullback node where it remains a statement
dependency. These are removals from this proof's route, not withdrawals of modules
that may have other consumers. No source-library declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

The original plan mixed the separate `SheafOfModules` presentation with the actual
constant-coefficient `Sheaf (ModuleCat A)` interface. The adopted source library
already proves the needed homological facts in the latter presentation. The unit
record has no realized proof steps bypassed by this route.

The returned head `2e9d7b02c9` was rejected because the source hole ledger
classified the option name in `set_option warn.sorry false` as an unattributed
hole at line 37, offset 1608. Removed that redundant global option. A source
census now finds zero hole markers and no attribution warnings in the assigned
module; no proof hole needed relocating.

The retained packet also repeatedly exceeded the 60-second compile gate. Removed
redundant functor-equality transports and factored the concrete square calculation
through a generic, fully proved adjunction pasting lemma. This reduces repeated
kernel comparisons of concrete sheaf functors without splitting the module,
raising the limit, or changing any prescribed map or hypothesis.

The general SheafOfModules change-of-rings theorem is unnecessary for this proof: its
constant-coefficient computation is proved directly using the adopted derived adjunctions.
Other modules retain their existing imports of that theorem.

The scalar-interface file's historical blueprint tag points to
`lem-pur-derived-change-of-rings`, whose current Lean attachment is the separate
general cochain-model interface. This delivery preserves that attachment and the
existing scalar-interface theorem; it does not replace either with an empty module.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
