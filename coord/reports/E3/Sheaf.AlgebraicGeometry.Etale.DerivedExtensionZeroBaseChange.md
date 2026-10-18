## What changed

Proved `AlgebraicGeometry.Etale.derivedExtensionZeroBaseChange` in
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`, including invertibility,
naturality, the identity square, successive base changes, and composition of open immersions.
The theorem's signature and both public definitions are unchanged. No other Lean module changed.

The proof identifies the canonical underived exchange with its inverse-image square mate,
then proves its identity and both pasting equations using the existing mate and square-pasting
APIs. For composition of opens it checks the conjugate of the actual
`openImmersionLowerShriekComp` using the unit equation for uniqueness of left adjoints.
The identity equation descends through localization by natural-transformation extensionality.
The two pasting equations use the existing generic
`CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso_comp`, with private proved lemmas
identifying its comparisons with the unchanged public definitions. All helpers are proved;
none introduces an assumption or a public interface.

Added proof imports `Sheaf.CategoryTheory.DerivedExactSquare` and
`WeilConjectures.SixFunctors.BaseChange.Pasting`. Updated the item's DAG proof and proof
dependencies to this actual route, retaining the blueprint's exactness, canonical underived
map, and degreewise localization route. No blueprint-unit statement or proof step is bypassed.

The preflight flags scoped helper-section commands as a conservative interface change.
`coord/changes/derived-extension-zero-base-change-proof-setup.md` documents their scopes,
verbatim command setup, unchanged public API, and all six direct importers. No consumer
adaptation is required.

Validation: the complete module compiled after pruning its proof imports. The final delivery
checks compile it again and check the existing signatures. There are no lines over 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.derivedExtensionZeroBaseChange`
(node `cor-cbc-derived-extension-zero-base-change`).

Proved 1 of 1 original holes. Zero holes left in the delivered module, zero holes added,
zero split-offs, and no new modules or nodes. Both public definitions remain concrete and
unchanged. This is a proof from existing declarations, not a decomposition.

The existing imported theorem
`CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso_comp`
(node `lem-weil-pbc-derived-exact-square-factorization`) still has its pre-existing `sorry`.
It is the remaining generic localization obligation on this route, not a hole added by this
delivery. No claim is made that the resulting transitive axiom closure is already sorry-free.

## No longer needed

Removed these twelve direct proof imports:

- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`: the higher identity
  and associativity wrapper is unnecessary. The existing canonical composition definition
  from the public source import is retained; its mate is proved directly here.
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`: its specialized composition
  theorem is unnecessary; the public source coherence API supplies the precise comparisons.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: the generic constant-coefficient
  source sheaf functors already have the exactness instances required here.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`: its separate
  variable-ring module-sheaf mate construction is unnecessary.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`: unnecessary
  variable-ring module-sheaf composition wrapper.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`: its separate
  module-sheaf base-change theorem is unnecessary; use the actual constant-coefficient
  `openImmersionLowerShriekBaseChangeMap` already in the public definition.
- `WeilConjectures.SixFunctors.OpenClosed.Complex`: unused open/closed complex machinery.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: redundant
  direct import; the exact-functor API is still used through the public derived imports.
- `WeilConjectures.SixFunctors.BaseChange.Square`: redundant direct import, supplied by
  the new proof import `BaseChange.Pasting`; its actual square comparisons remain used.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`: redundant
  direct import, supplied by the retained public derived base-change import; the canonical
  map, its unit equation, and its invertibility remain used.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`: redundant direct
  import; its actual adjunction remains used transitively.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: unnecessary
  variable-ring module-sheaf exactness implementation.

Removed from the item's proof dependencies these three planned helper nodes, whose conclusions
are instead proved by private helpers from the source mate API in this delivery:

- `lem-cbc-derived-extension-zero-base-change-underived-compatibility`
  (`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`);
- `lem-cbc-derived-extension-zero-base-change-vertical-pasting`
  (`Sheaf.AlgebraicGeometry.DerivedExtensionZeroBaseChangeVerticalPasting`);
- `lem-cbc-derived-extension-zero-base-change-open-pasting`
  (`Sheaf.AlgebraicGeometry.Etale.OpenImmersionBaseChangeOpenPasting`).

Also removed the obsolete proof dependencies and corresponding old `tool_uses` approvals
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-inverse-image-composition-module-linear`,
`lem-weil-pbc-derived-inverse-image-composition`, and
`lem-weil-pbc-etale-shriek-base-change-modules`. Removed the unused old approval
`lem-weil-pbc-extension-by-zero-unit-iso`. These are not needed on this item's route.

`lem-cbc-extension-zero-composition` remains cited for its existing canonical composition
isomorphism, but its wrapper theorem `openImmersionLowerShriekComp_coherence` is not used.
The underlying exact-functor, adjunction, square, composition and localization APIs remain
needed; redundant direct imports above do not mean those source APIs can be withdrawn.
Pruning elsewhere depends on whether other parents still use the corresponding modules.

## Where the brief, the DAG or earlier work was wrong

Three declared helper-node attachments named modules absent from both the checked-out source
and the published compilation library: the underived-compatibility and the two pasting modules
listed above. Rather than restating their conclusions as new holes, this delivery proves the
required component equations directly from the existing source mate calculus.

The old route also went through variable-ring module-sheaf wrappers although the actual public
map is defined using constant-coefficient sheaves valued in `ModuleCat Λ`. The source
`upperStar`, `openImmersionLowerShriek`, their exactness instances and their canonical mate
already have precisely these coefficients. No statement, coefficients, hypotheses, universes,
public visibility, or definition was changed to shorten the proof.

The original theorem API docstring retains its earlier proof-plan references; the updated
DAG proof and this report describe the actual route and its pruned dependencies.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
