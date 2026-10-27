## What changed

Proved `WeilConjectures.GeneratorReduction.constantDirectUnderlying_existsUnique` in
`Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` without changing its signature.
The proof imports all of `Sheaf.Paper.CompletedPullbackAdjunction` privately to use its
already proved `ConstantCompletion.module_adjunction_exists` construction, for the
specified algebraic inverse-image data of `sfCbcMorphism f`.

The proved private helper `normalizedRightAdjointUnderlying` transports a normalized
underlying-functor comparison along `Adjunction.rightAdjointUniq`. Naturality and the
unit equation show that it preserves every adjunct. Evaluating the proposed
normalization at the original counit makes that adjunct the identity and proves
uniqueness of each component. This implements the existing Yoneda argument in the
item's docstring, with no geometric or coefficient hypotheses added. The generic
argument also applies to empty categories and identity adjunctions.

The second proved private helper `normalizedModuleDirectUnderlying` specializes this
argument to the existing module adjunction construction before applying it to schemes.
Keeping the reasoning generic avoids repeated expansion of the geometric constructions
during kernel checking.

The existing public definitions, imports, attributes and all other theorem statements
are unchanged. A local irreducibility setting for `ordinaryU`, after its evaluation
comparison, prevents later elaboration from repeatedly expanding the strict restriction.
This is recorded in `coord/changes/X5-constant-semilinear-local-restriction.md`;
no importer sees the local setting and no consumer adaptation is needed. The main generator theorem and the other existing holes remain for
subsequent workers; this is a partial proof delivery, not a decomposition.

Searches: LeanFinder for extension-by-zero adjunctions returned ordinary scheme-module
restriction and module sheafification adjunctions, without an exact comparison for these
small-site functors. Loogle found `Adjunction.ofNatIsoRight` and its normalization laws.
The logged grep for localized module adjunctions found no Mathlib match. Local searches
identified the specified module Hom formula in `CompletedPullbackAdjunction` and the
uniqueness/unit equations in Mathlib's `Adjunction.Unique`; these yield the completed
proof directly. No new intermediate obligation is needed.

## Proved and sorry left

Closed 1 of the module's 13 original holes:
`WeilConjectures.GeneratorReduction.constantDirectUnderlying_existsUnique`.
Added 0 holes and split off 0 theorems. Both private helpers are proved.

The 12 remaining holes, all owned by
`lem-sf-constant-semilinear-generator-comparison`, are:

- `WeilConjectures.GeneratorReduction.ordinaryRho_existsUnique`
- `WeilConjectures.GeneratorReduction.rho_existsUnique`
- `WeilConjectures.GeneratorReduction.ordinarySystemDirectIso_existsUnique`
- `WeilConjectures.GeneratorReduction.ordinaryIntegralDirectIso_existsUnique`
- `WeilConjectures.GeneratorReduction.systemDirectScalarIso_existsUnique`
- `WeilConjectures.GeneratorReduction.ordinarySystemPullMap_isIso`
- `WeilConjectures.GeneratorReduction.integralDirectScalarIso_existsUnique`
- `WeilConjectures.GeneratorReduction.constantOpenAdjunction_nonempty`
- `WeilConjectures.GeneratorReduction.systemOpenScalarMap_isIso`
- `WeilConjectures.GeneratorReduction.ordinaryIntegralPullMap_isIso`
- `WeilConjectures.GeneratorReduction.integralOpenScalarMap_isIso`
- `WeilConjectures.GeneratorReduction.constantSemilinearGeneratorComparison`

## No longer needed

None. No existing import, node or module is removed. The new private proof import is
used for the actual module adjunction construction. The unfinished generator argument
still needs its declared dependencies, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The necessary normalized underlying module Hom formula
already exists as a proved private helper of the declared dependency
`Sheaf.Paper.CompletedPullbackAdjunction`; importing its implementation avoids
reconstructing the module direct image. The proof follows the existing argument, so no
node route or attachment is changed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
