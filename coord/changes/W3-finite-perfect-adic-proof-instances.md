# AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization

## Reason

The proof uses the existing locally bijective sheafification instance and the new
explicit small Grothendieck derived localization. The preflight conservatively
flags their local instance attributes as a change visible to importers. Both
attributes are local to this module. The existing public theorem signature, all
original public imports and all target statements stay verbatim. No existing
public definition or source-library module changes.

## Old

The original environment starts immediately with the theorem docstring after:

```lean
namespace AlgebraicGeometry.Scheme
```

The original signature is:

```lean
theorem finitePerfectModels_adic_realization
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A]
    [(koszulConstantFunctor X A).PreservesZeroMorphisms]
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (_hφ : ∀ n : ℕ, IsIso (φ n)) (_hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (_hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        ∃ (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((reconstructionRlim X d).obj ((completedAdicReduction X d).obj M)) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X A P))))
```

Its proof was `by sorry`.

## New

The added commands after the namespace are exactly:

```lean
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] finitePerfectAdicAlgebraDerived
```

The unchanged signature is:

```lean
theorem finitePerfectModels_adic_realization
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A]
    [(koszulConstantFunctor X A).PreservesZeroMorphisms]
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (_hφ : ∀ n : ℕ, IsIso (φ n)) (_hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (_hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        ∃ (P : CochainComplex (ModuleCat.{t} A) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Projective A (P.X i) ∧ Module.Finite A (P.X i)) ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((reconstructionRlim X d).obj ((completedAdicReduction X d).obj M)) ≅
              ringedSiteDerivedRestrictionOfUniverses (completedAdicRing X d) U
                ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
                  (DerivedCategory.Q.obj (finiteModelConstantComplex X A P))))
```

Its proof now combines the compatible local algebraic tower, the proved algebraic
reconstruction helper and the proved specified-limit assembly. The new private
helpers are fully proved. Their supporting imports are private proof imports.
The seven new public modules and their declarations are separately attached to
seven new DAG nodes and documented in report.md; they change no existing API.
The local attributes do not export an instance or change any consumer's instance
selection. No target meaning changes or statement re-review is requested.

## Users

`tools/downstream.py Sheaf.Paper.FinitePerfectAdicRealization --uses
finitePerfectModels_adic_realization` lists two downstream modules, and finds the
actual theorem use in ResidueLissePerfectLift and the declaration in the item.
All three modules are included below. The direct consumer still applies exactly
the same theorem to the same arguments at line 405; the transitive consumer has
no new statement or definition. This is a source/interface check, not a full
consumer rebuild. No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FinitePerfectAdicRealization | W3 | Completed assembly proof; unchanged signature and public imports. |
| Sheaf.Paper.ResidueLissePerfectLift | unclaimed | Its application at line 405 uses the same statement; local attributes do not escape. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | A3 | Transitive consumer; unchanged API and no adaptation. |

The holder table was checked against current claim records. No file held by another
group is changed, and no additional claims were taken.

## Status

landed 20261021T012429-L-2190159 2026-10-21 (merge of deliver/W3/Sheaf.Paper.FinitePerfectAdicRealization)
