## What changed

Filled `WeilConjectures.IntegralOnSlice.isomorphismOrdinaryCompletionChain` with its
original signature and public imports unchanged. The only existing Lean module changed
is the assigned item; all its added imports are private proof imports.

Three new modules contain proved intermediate comparisons:
`IsomorphismOrdinaryModuleNormalization`, `IsomorphismOrdinaryQuotientTowerNormalization`,
and `IsomorphismOrdinaryFiniteAugmentation` (all under `Sheaf.Paper`). Their statements
are respectively a module-functor isomorphism with its unit formula, a strict tower
isomorphism with its insertion components, and a finite-degree augmentation equality.
None asserts the completion-chain conclusion. The item combines these comparisons using
`podReindexingRoosComparison` and both mapping-cocone coordinates.

Profiling the combined implementation showed it exceeded the 60-second file limit.
Eliminated expensive tower transports after checking that the chosen tower presentations
are definitionally equal; the insertion isomorphism now applies directly. The module,
tower and finite-augmentation stages compile separately in the new modules, as permitted
by brief step 3a.
No shared definition, signature, attribute, instance or public import was changed.
Updated the item's DAG proof and dependencies and added the three helper nodes.

Validation: all helper modules compiled with `lcompile.py`; the complete sandbox was
compiled in dependency order. After resolving the final component-type conversion,
the item compiled cleanly in 16.3 seconds. No profiling options remain.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.IntegralOnSlice.isomorphismOrdinaryCompletionChain`
(node `lem-pur-isomorphism-ordinary-completion-chain`). Added zero holes: all three
new public theorems and every private helper are proved. Every delivered Lean file
contains zero `sorry`. Factoring proved arguments into modules is not a sorry split.

The new public theorems are
`WeilConjectures.IntegralOnSlice.isomorphismOrdinaryModuleNormalization`,
`WeilConjectures.IntegralOnSlice.isomorphismOrdinaryQuotientTowerNormalization`, and
`WeilConjectures.IntegralOnSlice.isomorphismOrdinaryFiniteAugmentation`.

## No longer needed

The proof does not use the planned `lem-pur-isomorphism-inverse-image-tensor-hom`
(`Sheaf.Paper.PurInverseImageTensorHom`): the existing unrestricted insertion
construction identifies the entire finite pullback tower for arbitrary complexes.
It does not use `lem-cbc-exact-product-functor-roos-chain-maps`
(`Sheaf.Paper.ExactProductFunctorRoosChainMaps`): `podReindexingRoosComparison`
directly handles the actual mapping-cocone model, without a Good hypothesis.
Removed these two edges from the item's proof dependencies. Neither module was
explicitly imported in the original item, so no original import line was removed.
No module is withdrawn and no claim is made that either is globally unreachable.
The item and helpers need no direct proof import of `IntegralDerivedOperationsOnSlices`:
its public API already comes through `QcqsCompletionOrdinaryModels`. The private
`globalTower_eq` is unnecessary because the existing insertion isomorphism type checks
directly against the slice-none tower.

## Where the brief, the DAG or earlier work was wrong

The planned tensor/Hom and general exact-product interfaces are unnecessary. Stronger
unrestricted internal insertion and Roos constructions already exist below the public
Good-complex statements. The proof reuses those proved private constructions with
`import all`, preserving the public interfaces and the unit route. The current
blueprint unit has no separately realized proof step that this route bypasses.
The quarantine/rework row was checked; the current item source is present and its
Lean attachment and mathematical statement are preserved.

Restriction maps in a presheaf of modules are semilinear maps over varying rings;
the cancellation proof uses `PresheafOfModules.map_comp_apply`, not ordinary
composition of two maps over a fixed scalar ring.

The inherited DAG dependency walk also encounters an existing cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. Those records are untouched;
the new dependency edges form no cycle through any delivered node.

## New nodes

`lem-pur-isomorphism-ordinary-module-normalization`: the ordinary pullback and
sectionwise inverse image have canonically identified right adjoints; left-adjoint
uniqueness gives an isomorphism, normalized on ordinary-unit sections by the site
counit. This is a module comparison, before any complexes or Roos construction.

`lem-pur-isomorphism-ordinary-quotient-tower-normalization`: the two chosen strict tower
presentations are definitionally equal. The existing unrestricted insertion isomorphism
therefore applies directly and has the specified finite components by reflexivity. This is a tower
comparison, before taking products or mapping cocones.

`lem-pur-isomorphism-ordinary-finite-augmentation`: for given normalized module and
tower comparisons, naturality and the site right triangle identify one exponent and
one cochain degree of the two augmentations. This supplies the finite equation that
the item assembles using product projections. All three nodes are fully proved.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
