## What changed

Filled both existing holes in `Sheaf.Paper.NativeAdicEncodingCore` without changing any
existing declaration signature, definition body, public import, or target.

`encoding_isEquivalence` composes the existing proved
`nativeScalarForgetting_isEquivalence` with `Mod.comapEquivalenceOfIsIso`.

`encoding_ordinary_operations` constructs the normalized pushforward comparison using
`mapModComapIso`, `mapModCompIso`, `comapComp`, and the coefficient naturality square.
Its components are identities on sections. The inverse mate is invertible by
`isIso_inverseMate_of_equivalences`; its inverse supplies the actual pullback comparison.
The mate equation is `mateEquiv.apply_symm_apply`, and the existing condensed pullback
instances give finite limits and colimits preservation.

The coefficient naturality proof is reused locally from the already proved
`LocallyFiniteCoefficientRingRealization`: the explicit `coefficientIso` is normalized
on every finite-field leg by `globalCoefficientIso_fac`; continuous-chart naturality
and native precomposition give agreement on these legs; the abelian-sheaf colimit then
gives equality. Importing the realization module itself would create a cycle through
its public `WeilSheaf.LowerShriek` import. The local helpers are private and proved.
The colimit argument uses
`isColimitOfPreserves` and `Profinite.isColimitPadicAlgClRingObjCocone` directly,
so no completed integral/rational coefficient package is imported.
The large private pushforward comparison is irreducible, with a proved identity-on-
underlying-maps lemma; the mate cancellation is proved generically before specialization.
This keeps the final theorem from unfolding the module-transport construction.
The same module-composition construction already occurs in
`NativeScalarRestrictionComparison`, which also cannot be imported at this position.

Added only proof imports for native scalar forgetting, continuous-chart naturality,
the monoidal forgetting/pushforward comparison, and the inverse-mate lemma. Updated the existing node's proof and proof dependencies to match.

## Proved and sorry left

Closed two original holes, both attached to
`lem-sf-native-adic-encoding-ordinary-operations`:

- `AlgebraicGeometry.ProEtale.NativeEncoding.encoding_isEquivalence`.
- `AlgebraicGeometry.ProEtale.NativeEncoding.encoding_ordinary_operations`.

No new holes and no split-off statements. No `sorry` remains in the delivered module.
All previously proved declarations are retained. The initial profiling compile timed out
while reducing the large module-transport comparison. Replacing unfolding by the
existing component equations and explicit identity rewrites removed that bottleneck;
the final single-file compile and delivery preflight verify the complete module.

## No longer needed

No original imports were removed; all existing public imports are preserved.
This module no longer needs the following planned dependencies:

- `lem-sf-finite-span-module-derived-comparison` /
  `Sheaf.Paper.FiniteSpanModuleDerivedComparison`: the existing scalar-forgetting
  equivalence and explicit scalar restriction prove the specified heart equivalence
  directly; generic module transport and mates prove its ordinary operations.
- `def-pur-sheaf-tensor-product` /
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: no sectionwise
  reconstruction or cochain tensor construction is needed in this module.
- `lem-weil-pbc-equivalence-injective-resolutions`: the actual ordinary unbounded
  K-injective and exact-equivalence APIs already prove the retained derived clause.
- `def-sfb-right-derived-functor` /
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the unchanged
  derived comparison uses the native universal right-derived composition APIs.
- `sk-prop-sfb-cartesian-coefficients` /
  `Sheaf.Paper.CartesianCoefficients`: the native generic module-object pullback
  already has the required exactness instances; no signed twists are used here.
- The proof-only uses of `def-sf-native-weil-derived-framework` and its large
  `WeilConjectures.WeilSheaf.LowerShriek` entry module are unnecessary: the relevant
  native definitions are already publicly imported through `Adic.Module`.
- `lem-sf-locally-finite-coefficient-ring-realization` /
  `Sheaf.Paper.LocallyFiniteCoefficientRingRealization`: its proof of naturality for
  this explicit coefficient is repeated privately from its lower coefficient inputs,
  avoiding its cyclic public Weil-sheaf interface and the unrelated existence package.

These are removed dependencies of this proof, not claims that their modules have no
other consumers. No module or declaration is withdrawn. The unit's realized statement
and step lists are unchanged.

## Where the brief, the DAG or earlier work was wrong

The plan's section-module detour is unnecessary now that the actual ambient-scalar
forgetting functor has a complete equivalence proof. Its existence-style coefficient
comparison is also insufficient by itself to identify the specified `coefficientIso`
without checking normalization; the delivered local argument proves the required
square for that very isomorphism. Neither source issue changes the statement.

The existing inverse-mate result is used as a general category-theoretic tool, with
both side encoding functors checked to be equivalences. No invertibility of arbitrary
mates is assumed. The underlying-map proof uses component equations for module transport and scalar
restriction, avoiding reduction of the large transported action. The construction uses
no finiteness or invertibility-of-l hypothesis
on schemes and also covers empty schemes and zero modules.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
