# AlgebraicGeometry.ProEtale.TwoTermReduction.two_term_reduction_cohomology

## Reason

The proof needs private additive and exactness interfaces, local opacity boundaries,
and an assembly section. The stage-3 interface checker flags the added proof context.
The helper interfaces are proved private theorems registered with `[local instance]`;
there are no added global instances. The opacity attributes are also local. Existing
public definitions, structures, fields, theorem signatures, and public imports are
unchanged. Only proof imports, private helpers, and the target proof are changed.

The opacity boundaries prevent expansion of the coefficient functor, its comparison
isomorphisms, and the chain and homology constructions after their concrete formulas
are proved. Direct categorical composition lemmas and explicit mono/epi proofs reduce
elaboration cost without changing any construction.

## Old

There was no private-helper context, no added helper instance registration, and no
assembly section. The existing target declaration was:

```lean
theorem two_term_reduction_cohomology (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a) (N : Normalization.{u + 1, u, u + 1, w} p) :
    Nonempty (Calculation ℓ (Spec (.of Ω)) p N) := by
  sorry
```

## New

The existing target now has this proof, with the same signature:

```lean
theorem two_term_reduction_cohomology (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    [hD : ∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) CommRingCat.{u + 1},
      HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) CommRingCat.{u + 1}}
      (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a) (N : Normalization.{u + 1, u, u + 1, w} p) :
    Nonempty (Calculation ℓ (Spec (.of Ω)) p N) := by
  exact ⟨{
    realization := realizationData ℓ (Spec (.of Ω)) p N
    cohomology := cohomologyData ℓ (Spec (.of Ω)) p N
    tensor := tensorData ℓ (Spec (.of Ω)) p N
    realization_spec := realizationData_spec ℓ (Spec (.of Ω)) p N
    cohomology_spec := cohomologyData_spec ℓ (Spec (.of Ω)) p N Ω rfl
    tensor_spec := tensorData_spec ℓ (Spec (.of Ω)) p N
  }⟩
```

The four proved local interfaces are:

```lean
private theorem upperStar_additive (X : Scheme.{u}) :
    (upperStarFromPoint X).Additive :=
  leftExactFunctor_le_additiveFunctor _ _ _ (upperStarFiniteLimits X)

attribute [local instance] upperStar_additive

private theorem coefficientFunctor_additive (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : (coefficientFunctor X A).Additive :=
  exactFunctor_le_additiveFunctor _ _ _ (coefficientFunctor_exact X A)

attribute [local instance] coefficientFunctor_additive

private theorem restriction_finiteLimits (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (restriction.{u + 1, u, u + 1} a) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose

attribute [local instance] restriction_finiteLimits

private theorem restriction_finiteColimits (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits (restriction.{u + 1, u, u + 1} a) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction a).choose_spec.choose

attribute [local instance] restriction_finiteColimits
```

The added name-resolution and elaboration context is:

```lean
open CategoryTheory.Preadditive CategoryTheory.Category
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The transparency options occur only after the unchanged public definition section.
The additional assembly variables are enclosed in this section, closed before the
public target theorem:

```lean
section Assembly

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
  [hD : ∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
    HasDerivedCategory.{w} (Modules.{u + 1, u, u + 1} R)]
  (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S), Presentation.{u + 1, u, u + 1, w} a)
  (N : Normalization.{u + 1, u, u + 1, w} p)

-- Private assembly declarations.

end Assembly
```

The proof's local opacity boundaries are:

```lean
attribute [local irreducible] coefficientFunctor coefficientRegularIso coefficientResidueIso
attribute [local irreducible] minusIso zeroIso sheafInclusion sheafReduction
attribute [local irreducible] restrictHomology
attribute [local irreducible] scalarUnitIso ordinaryComplexIso
attribute [local irreducible] reductionChain
attribute [local irreducible] ring finiteRing
```

Every newly added helper is private and proved. No public data definition or target
statement changes, and no target statement review is reopened by this proof context.

## Users

`python3 tools/downstream.py Sheaf.Paper.TwoTermReductionCohomology --uses
two_term_reduction_cohomology` reports zero downstream Lean modules and only the item
itself as a textual user of the theorem. The unfinished parent in the DAG still needs
this item; no withdrawal is requested. There are no consumer adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TwoTermReductionCohomology | Q7 | Completes the existing proof; adds private proof context and local instance registrations. |

## Status

landed 20261022T011916-L-3231336 2026-10-22 (merge of deliver/Q7/Sheaf.Paper.TwoTermReductionCohomology)
