## What changed

Proved `AlgebraicGeometry.ProEtale.isLocallyFinitelyPresented_comap_iff_sameCover`
without changing its signature or any public import. Private, proved helpers transport
fixed-rank cokernel presentations along module isomorphisms and scalar restriction,
then along pullback. Inverse restriction gives reflection. The existing
`Mod.extendScalarsIsoComapInv` gives both extension assertions.

The finite-free comparison `Mod.finiteFreeIsoComap`, already proved in the adopted
source library, makes general extension finite presentation unnecessary. The node's
proof and dependencies now describe this route. All source-library files are unchanged;
no consumer adaptations are needed. The change record
`coord/changes/lfp-scalar-isomorphism-proof-scopes.md` documents declaration-local
helper scope and lint commands required by preflight; no public interface changes. The unit's constructibility route
is preserved: this supplies exactly the coefficient-relabelling lemma it requires.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.isLocallyFinitelyPresented_comap_iff_sameCover`
(node `lem-sfb-lfp-scalar-isomorphism`). Added 0 holes; split off 0 statements.
Every private helper is proved. No `sorry` remains in any delivered Lean file.

The completed proof compiled through `lcompile.py` in 7.9 seconds, and helper
assumption cleanup compiled in 7.1 and 7.4 seconds. The last remaining warning
concerned the original public hypothesis `IsCommMonObj S`, which this shorter
proof does not need. A declaration-local `linter.unusedSectionVars` setting retains
that original hypothesis without a lint warning; it changes no proof-checking option.
The delivery performs the final warning-free compile and axiom/preflight checks.
The public theorem signature was compared byte for byte with the original.
The construction works uniformly for zero ranks and zero coefficient rings;
existential cover witnesses are reused unchanged, including empty covers.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation`: the fixed-rank
  restriction calculation uses `Mod.finiteFreeIsoComap` and cokernel preservation.
- `Sheaf.CategoryTheory.SheafTensor` and
  `Sheaf.CategoryTheory.GrothendieckSheafification`: the necessary ambient structures
  are already available through retained public imports. Their mathematical content
  remains in the proof dependencies; the redundant direct imports are removed.
- `Mathlib.CategoryTheory.Abelian.Basic` and
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: available through retained public imports.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`:
  its pullback structure is available through the retained module-object monoidal import.

The proof no longer uses node `lem-sfb-internal-extension-finite-presentation`,
module `Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation`, or its associated
`tool_uses` approval. They are removed from this node's route, without withdrawing
their declarations or asserting that other consumers no longer need them.
`def-sp-abelian` and `def-weil-pbc-proetale-site` are no longer separate proof steps:
ambient structures and the site are supplied by retained imports and definitions.
Node `lem-sfb-finite-upper-star-braided` is also unnecessary for this route:
restriction and its finite-free comparisons require only monoid objects, so the
pullback need only be lax monoidal. Its existing public import remains unchanged.
The identity-coefficient case of `def-sfb-comap-mapmod-square` is used through the
already proved `Functor.mapModComapIso`; no general square construction is imported.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original plan was longer than
necessary: an existing direct restriction-of-scalars calculation preserves both ranks,
so applying the general extension finite-presentation theorem in both directions is
unnecessary. No new public statements, definitions, or DAG nodes were introduced.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
