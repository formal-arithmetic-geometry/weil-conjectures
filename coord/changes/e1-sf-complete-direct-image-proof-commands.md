# WeilConjectures.sfCompleteDirectImage_reduction

## Reason

The completed proof uses private categorical transport lemmas, private coefficient
comparison lemmas, and the universal derived-unit API. The static preflight scan
classifies the added section variables, open commands, and attribute commands as
an interface change and requests this record. All original public imports,
theorem binders, universes, hypotheses, conclusions, and data definitions remain
unchanged. No source-library module is modified and no target meaning changes.

## Old

The public signature, verbatim:

```lean
theorem sfCompleteDirectImage_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) :
    IsSfDerivedComplete l E Y L.obj ∧
      ∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n)
```

The original module contained no private proof helpers and no corresponding
section variables or proof-specific attribute commands.

## New

The public signature, verbatim and unchanged:

```lean
theorem sfCompleteDirectImage_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : IsSfDerivedComplete l E X K)
    [HasProduct (sfDirectImageTerm l E f K)] (L : SfIntegralDirectImage l E f K) :
    IsSfDerivedComplete l E Y L.obj ∧
      ∀ n : ℕ, IsIso (sfDirectImageReductionComparison l E f L n)
```

The single original proof hole is replaced by the complete proof in the item
module. Every added declaration is private and proved; no public definition uses
a private helper. The original declaration docstring is preserved.

The added outer transparency controls are:

```lean
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
```

Additional local irreducibility controls cover the private canonical cochain unit,
the private specified projection mate, the ordinary coefficient comparisons, and
the existing direct-image comparison wrappers used in ProjectionTransport. They
avoid unfolding localization and sheafification data during elaboration. The
NormalizedCube and Comparison section variables are bound only by private helpers.
ProjectionTransport also installs the existing composite finite-limit/colimit
preservation lemmas and the fixed coefficient-universe Abelian/derived-category
interfaces as local instances. The namespace and open commands supply notation
and name resolution for these proofs; they change no declaration statement.

The proof-only import CompletedCoefficientPushforwardComparison supplies two broad
instances whose flexible universes interfere with the native coefficient API.
The item explicitly contains these instance-erasure commands:

```lean
attribute [-instance] CompletedCoefficientPushforward.modAbelian
attribute [-instance] CompletedCoefficientPushforward.hasDerived
```

These are reported explicitly, rather than described as local irreducibility
attributes. The existing instance declarations, bodies, and source attributes are
not edited. The proof selects the existing native Abelian and derived-category
interfaces instead. All new imports are non-public proof imports. No new axiom,
unsafe mechanism, hollow definition, or additional proof hole is introduced.

## Users

Computed with `tools/downstream.py Sheaf.Paper.SfCompleteDirectImageReduction
--uses sfCompleteDirectImage_reduction` on 2026-10-21. There are 1002 transitive
importers, all retaining the same public theorem type and original public imports.
The two modules with textual declaration uses are listed below; the external use
was read at its application of the unchanged theorem. Claim records were checked.
No downstream source adaptation is needed or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfCompleteDirectImageReduction | E1 | Complete proof and private helpers; unchanged public signature. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Its application receives the same completeness and finite-comparison conclusions with identical arguments. |

No other group-held module is edited. The independent reader should review the
recorded elaboration commands along with the actual normalized-mate argument;
the global build checks the unchanged consumers after landing.

## Status

landed 20261022T002351-L-1921179 2026-10-22 (merge of deliver/E1/Sheaf.Paper.SfCompleteDirectImageReduction)
