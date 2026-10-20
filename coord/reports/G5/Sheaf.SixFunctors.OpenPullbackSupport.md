## What changed

Proved `SheafOfModules.OpenTensorNormalization.derivedPullback_openSupported` in
`Sheaf.SixFunctors.OpenPullbackSupport`, with its signature and public import unchanged.
Added three fully proved private helpers: `resolving_exists`, `pullback_absolute`, and
`pullback_derivedAdjunction`. Updated the theorem's proof explanation and its node's
proof, proof dependencies and proof origin to the actual shorter argument.

Flat-term K-flat resolutions and the supplied flat-model comparisons make each
specified left-derived pullback absolute. The proof reuses the proved private
`CategoryTheory.Functor.pro_absolute` helper through the proof-only `import all
Sheaf.Algebra.Homology.DerivedCoefficientMapDescent`; it does not use the public
coefficient-map theorem. Deriving the ordinary adjunction then identifies the
specified pullback as left adjoint of the canonical K-injective derived direct image.
Exact restriction and its preservation of K-injectives derive `o.rightSquare`.
Uniqueness of composite left adjoints provides the essential-image witness
`o.gUPull.derived.obj M`.

The other proof-only imports supply the tensor-predicate comparison, K-injective
resolutions for the actual coefficient universes, and the right-derived composition
comparison with an exact functor. There are no statement or definition changes,
consumer adaptations, new modules, or new nodes. The unit route is retained.

## Proved and sorry left

Closed 1 of 1 holes:
`SheafOfModules.OpenTensorNormalization.derivedPullback_openSupported`
(node `lem-sf-open-pullback-support`). Added 0 holes; 0 remain in the item.
All three private helpers are proved. Nothing was split off.

The server compiled the file cleanly, without warnings, in 4.4 seconds.
`#print axioms` for the theorem reported exactly `propext`, `Classical.choice`,
and `Quot.sound`; the diagnostic command was removed before delivery.

## No longer needed

No original Lean imports were removed: the sole original public data import remains.
The proof does not use the following former direct proof dependencies, which were
removed from this node's `proof_deps` and proof-step uses:

- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-diagram-site-realization`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-proetale-weakly-etale-localization`

The corresponding localized-site, ringed-pullback, extension/tensor, diagram-site,
and tensor-descent modules are not added as direct proof imports. In particular,
no preservation of K-flatness by open extension is proved or assumed: deriving
right adjoints replaces that part of the old plan. The supplied `Operations`
record already contains the ordinary square and exact open-extension adjunctions.
This is pruning of this node's planned route, not a claim that these modules have
no remaining users elsewhere; no source module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and valid. The previous proof plan was longer than
necessary: it reconstructed an ordinary square already included in `Operations`
and used preservation of K-flatness by extension to obtain the derived comparison.
Deriving the supplied right-adjoint square and invoking uniqueness of left adjoints
avoids both constructions. Ordinary and vertical sites, arbitrary allowed coefficient
maps, and arbitrary supplied derived-pullback presentations are all retained.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
