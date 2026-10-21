# AlgebraicGeometry.ProEtale.RationalLocalizedHom.rationalLocalizedHom

## Reason

Proving the existing statement requires matching its encoded scalar actions and controlling
unfolding of large derived-functor definitions. Preflight requires a record for the added
elaboration commands. Every original public definition, original instance body, public import,
and the theorem signature is unchanged. No mathematical statement or definition is repaired.
The original three private imports identified as unit-route modules are retained.

## Old

The original theorem signature, verbatim:

```lean
theorem rationalLocalizedHom
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [IsNoetherian T] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ K : rational T ℓ E, rationalConstructible T ℓ E K →
      ∃ K₀ : integral T ℓ E, integralConstructible T ℓ E K₀ ∧
        Nonempty ((extend T ℓ E).obj K₀ ≅ K)) ∧
    (∀ K₀ L₀ : integral T ℓ E,
      integralConstructible T ℓ E K₀ → integralConstructible T ℓ E L₀ →
      ∀ q : ℤ, ∃ c :
        (E.1 ⊗[PadicAlgCl.integers ℓ E.1] (K₀ ⟶ L₀⟦q⟧)) ≃ₗ[E.1]
          ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧),
        ∀ (e : E.1) (h : K₀ ⟶ L₀⟦q⟧),
          c (e ⊗ₜ h) = @SMul.smul E.1
            ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧)
            (rationalHomModule T ℓ E _ _).toSMul e
            ((extend T ℓ E).map h ≫ ((extend T ℓ E).commShiftIso q).hom.app L₀)) ∧
    Comparisons ℓ k E
```

There were no additional proof helpers or proof-local elaboration commands after `Comparisons`.
The theorem's body was `by sorry`.

## New

The theorem signature, verbatim and identical:

```lean
theorem rationalLocalizedHom
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [IsNoetherian T] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ K : rational T ℓ E, rationalConstructible T ℓ E K →
      ∃ K₀ : integral T ℓ E, integralConstructible T ℓ E K₀ ∧
        Nonempty ((extend T ℓ E).obj K₀ ≅ K)) ∧
    (∀ K₀ L₀ : integral T ℓ E,
      integralConstructible T ℓ E K₀ → integralConstructible T ℓ E L₀ →
      ∀ q : ℤ, ∃ c :
        (E.1 ⊗[PadicAlgCl.integers ℓ E.1] (K₀ ⟶ L₀⟦q⟧)) ≃ₗ[E.1]
          ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧),
        ∀ (e : E.1) (h : K₀ ⟶ L₀⟦q⟧),
          c (e ⊗ₜ h) = @SMul.smul E.1
            ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧)
            (rationalHomModule T ℓ E _ _).toSMul e
            ((extend T ℓ E).map h ≫ ((extend T ℓ E).commShiftIso q).hom.app L₀)) ∧
    Comparisons ℓ k E
```

The body is proved. The initial proof-local elaboration commands are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 100] homModule integralHomModule rationalHomModule
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  CategoryTheory.Functor.mapDerivedCategory
  CondensedRing.continuousRingModuleEquivalence upperStarFromPoint upperStar
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
```

Further `attribute [local irreducible]` commands keep the encoded Hom module and the large
left/right derived-functor constructions from unfolding during proof elaboration. Two
`attribute [-instance] homModule integralHomModule rationalHomModule in` commands affect
only their following private theorem. Scoped `set_option ... in` commands likewise affect
only the following helper. None changes the exported reducibility or registration of an
existing declaration.

The following new helpers have proved bodies and are declared `private local instance`:

- `continuousRestriction_limits`
- `continuousRestriction_colimits`
- `continuousCoefficient_comm`
- `integralCoefficient_comm`
- `coefficientInclusion_isMonHom`
- `coefficientNormedAlgebra`
- `padicInclusion_isMonHom`
- `extend_additive`
- `exactExtension_map`


Thus their instance registrations apply only while elaborating this file. The additional
`internalLinear`, `restrictLinear`, and `derivedSquare` definitions and all other added
helpers are private, with no public signature or public definition referring to them.

## Users

`tools/downstream.py Sheaf.Paper.RationalLocalizedHom --uses
AlgebraicGeometry.ProEtale.RationalLocalizedHom.rationalLocalizedHom` lists no downstream
modules and only the declaration's own module as a name use. No consumer adaptation is
needed, and no other module is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalLocalizedHom | C3 | Existing theorem proved; proof-local elaboration only |

## Status

landed 20261021T225101-L-3764898 2026-10-21 (merge of deliver/C3/Sheaf.Paper.RationalLocalizedHom)
