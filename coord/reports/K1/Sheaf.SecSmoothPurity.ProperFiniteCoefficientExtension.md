## What changed

The statement and public imports of
`Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` are unchanged. Its original
hole is replaced by a complete Lean proof from the existing projection theorem and
one separate tensor/pullback normalization lemma.

The new proof contains three proved private helpers:

- `restricted_mate_eq`: a calculation with two adjunctions, their mates and tensor
  identifications. It compares the actual morphisms by their counit transposes.
- `restricted_kInjective_directImage_quasiIso`: compare two coefficient structures
  through a common abelian K-injective replacement. Two-out-of-three and exact
  conservative forgetting give the required direct-image quasi-isomorphism.
- `scalarRestrictionDirectImageMap_isIso`: identify the exact-derived mate with
  the derived direct-image square, use that acyclicity argument, and transport
  the adjunctions to the actual left-derived inverse images.

The main proof uses the tensor/pullback normalization at `Rf_* L`, the explicit projection-formula transpose, and tensor naturality.
It inserts the two symmetries exactly as stated, cancels the invertible comparison
maps, and reflects invertibility through exact derived restriction. The last
conjunct is proved directly by `mateEquiv_counit`.

The new normalization module also retains a complete proved ordinary tensor
square, `scalarSheafPullback_tensor_compatibility`, with private helpers for the
scalar unit, monoidality of the restriction comparison, and a generic balancing
calculation. These are the ordinary part of its remaining derived argument.

Private imports added: the new normalization module,
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`,
`Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic`, and `import all`
of `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison`,
`Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux`, and
`WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities`.
The latter three provide already proved generic localization/mate helpers. The
normalization module privately imports the underived adjunction identities and
`WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal` for its
proved ordinary calculation. No
source-library declaration, definition, signature, attribute or public import is changed.

The original DAG proof and dependencies are updated to follow this argument.
No consumer adaptation or change record is needed. Instance caching and explicit
isomorphism cancellation replace expensive instance searches; the integrated file
has compiled within the 60-second limit (21 seconds; the normalization module
compiled in 12 seconds). A fresh sequential profiled compilation passed after an
earlier timeout; the profile showed no slow declaration. Development profiling was
removed. The first preflight classified ambient elaboration options as an interface
change; they are now scoped to individual declarations, preserving the original
ambient commands. Final delivery checks are run by deliver3.py.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Etale.properFiniteCoefficientExtension`
(`lem-asd-proper-finite-coefficient-extension`). Its three conjuncts have complete
Lean proofs. There are zero holes in the item module, including its private helpers.

One hole added and left:
`AlgebraicGeometry.Etale.scalarPullback_tensor_compatibility`, in
`Sheaf.SecSmoothPurity.ScalarPullbackTensorCompatibility`
(`lem-asd-scalar-pullback-tensor-compatibility`). Its proof is exactly `by sorry`;
its docstring and node give the source and a complete representative proof.

This is a decomposition: within the delivered files, one original hole is closed
and one strictly smaller hole is added. It is not reported as a net proof gain. The remaining
statement concerns inverse image and tensor comparison only. It asserts neither
proper direct-image invertibility nor a projection-formula or mate identity, and
has no properness, finiteness or boundedness hypotheses. The original theorem
combines it with the separately proved unbounded direct-image comparison,
projection transpose, isomorphism cancellation and conservativity.

## No longer needed

Removed all ten original private proof imports:

- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.TensorProjectionAdjunct`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`

The last two APIs are already available through the unchanged public interfaces.
The representative construction dependencies are needed only by the separate
normalization lemma, whose node records them; the main proof uses their fixed
canonical comparisons. No source module or declaration is withdrawn.

`lem-amb-tensor-projection-adjunct` is unnecessary: the actual unordered projection
transpose and tensor naturality suffice, and the specified symmetries are appended
afterwards. `lem-amb-proper-coproducts-projection` is not used as a proof lemma:
the existing finite specialization of `lem-kun-0f0g` gives invertibility of the
unordered projection map directly. Its public module is retained for the original
public interface.

`lem-pur-sheaf-ring-derived-coefficient-adjunction` and
`lem-weil-pbc-exact-functor-derived-functor` are unnecessary as direct proof tools;
exact-functor homology and the existing module-valued restriction API suffice.
Their obsolete entries are removed from the item's `tool_uses`. The remaining
original tensor/K-flat tools are still needed by the extracted normalization.
The direct invocation of
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is replaced by the
proved module-to-abelian acyclicity API; that API still uses the composition result,
so no global pruning of that node or its module is claimed.

The other original proof dependencies now used within the normalization rather
than directly are `def-kun-derived-tensor`, `lem-kun-inverse-image-monoidal`,
`lem-pc-kflat-resolution`, `lem-pur-change-of-rings-tensor-comparison`,
`lem-pur-derived-change-of-rings`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. They remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The supplied bounded-below
`scalarMate_restrict_eq_projection` cannot be applied to arbitrary unbounded L;
its boundedness assumptions are not silently dropped. The existing separate
representative normalizations do not themselves state the unbounded compatibility
of scalarTensorIso and scalarPullbackIso, so that precise part of original step 2
is recorded as the new lemma.

The direct-image proof does not assume that scalar restriction preserves
K-injectivity. A second module resolution and a common abelian resolution are
essential in the two-out-of-three argument.

The repository contains a maintenance backup of
`Sheaf.Paper.ScalarTensorPullbackNormalization` with a K-flat representative lemma.
It is not a live importable module or a live DAG attachment, and it was not deleted,
modified or used as a theorem. The new lemma is stated for the fixed canonical
scalarPullbackIso on arbitrary derived objects. Blueprint searches found no
existing imported blueprint statement of this compatibility.

Edge cases of the new lemma were checked mathematically: zero objects and a zero
coefficient ring have unique maps; identity coefficient changes and identity
geometric morphisms give the unit compatibilities; arbitrary shifts introduce no
factor interchange and hence no additional sign. Nonflat coefficient maps are
allowed because tensor is computed with the K-flat complex in the other factor.
The unit's realized route and all target statements are preserved.

## New nodes

`lem-asd-scalar-pullback-tensor-compatibility`, in the item's chapter and unit,
records the inverse-image compatibility of the fixed scalar and tensor
normalizations. Its module is
`Sheaf.SecSmoothPurity.ScalarPullbackTensorCompatibility`. It is extracted from
original step 2, not a renaming of the proper direct-image theorem. Its proof
uses ordinary balancing, the K-flat representative normalizations, the tensor
comparison counit equation, and cancellation of invertible model comparisons.
The module contains the proved ordinary scalar/pullback unit identity,
monoidality of the restriction/pullback comparison from the generic monoidal
sheaf-pushforward comparison and the explicit inverse-mate formula, and the
complete ordinary tensor equation. Transporting that equation through the chosen
scalar/tensor representatives remains the new lemma's unfinished Lean work.
LeanSearch, LeanFinder, Loogle and Mathlib grep found no matching declaration.
No change record is needed because every existing statement and definition is
unchanged.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
