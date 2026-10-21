# AlgebraicGeometry.Scheme.ProEt.bounded_epimorphic_top_derivedLimit

## Reason

The new proof asks Lean to synthesize the abelian module-sheaf category while
elaborating derived homology and countable products. The generic
`GrothendieckTopology.hasSheafify_of_essentiallySmall` instance leaves the universe
constraint `?u + 1 = max (t + 1) u` stuck. The existing public
`ProEtaleSurjectiveTowerDerivedLimit` import already supplies the appropriate
large-coefficient sheafification instances on the unchanged pro-etale site.

Exclude the generic instance only while elaborating this one theorem, using
`attribute [-instance] ... in`. The exclusion ends with the declaration; it does
not remove the instance from downstream modules. This is the same resolution used
by the existing `ProEtaleMilnorEpimorphic` proof, with a narrower command scope.
The preflight command scan requires this record even for a theorem-scoped attribute.
No definition, exported import, hypothesis, conclusion, universe or declaration
visibility changes. The proof and its direct dependencies are described in report.md.

## Old

The theorem had no scoped instance exclusion. Its exact signature was:

```lean
theorem bounded_epimorphic_top_derivedLimit
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (_hcomm : ∀ U : X.ProEtᵒᵖ, ∀ r s : R.obj.obj U, r * s = s * r)
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (P : ℕ → CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
    (τ : ∀ n : ℕ, P (n + 1) ⟶ P n)
    [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))]
    (L : DerivedCategory (ringedSiteModules.{max u (t + 1)} R))
    (_hL : IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.map (τ n)) L)
    (a b : ℤ) (_hab : a ≤ b)
    (_hP : ∀ (n : ℕ) (j : ℤ), j < a ∨ b < j → IsZero ((P n).homology j))
    (_htop : ∀ n : ℕ, Epi (HomologicalComplex.homologyMap (τ n) b)) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (ringedSiteModules.{max u (t + 1)} R) j).obj L)
```

## New

The signature is identical, preceded by the scoped elaboration command (the
existing theorem docstring occurs between the command and signature in the file):

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
theorem bounded_epimorphic_top_derivedLimit
    (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (_hcomm : ∀ U : X.ProEtᵒᵖ, ∀ r s : R.obj.obj U, r * s = s * r)
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]
    (P : ℕ → CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ)
    (τ : ∀ n : ℕ, P (n + 1) ⟶ P n)
    [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))]
    (L : DerivedCategory (ringedSiteModules.{max u (t + 1)} R))
    (_hL : IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))
      (fun n : ℕ ↦ DerivedCategory.Q.{w}.map (τ n)) L)
    (a b : ℤ) (_hab : a ≤ b)
    (_hP : ∀ (n : ℕ) (j : ℤ), j < a ∨ b < j → IsZero ((P n).homology j))
    (_htop : ∀ n : ℕ, Epi (HomologicalComplex.homologyMap (τ n) b)) :
    ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (ringedSiteModules.{max u (t + 1)} R) j).obj L)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleBoundedEpimorphicTopDerivedLimit
--uses bounded_epimorphic_top_derivedLimit` reports zero downstream Lean modules;
its only declaration-name hit is the item itself. The DAG parent
`lem-sf-complete-residue-cohomology-bounds` still cites this theorem and keeps the
same Lean attachment and dependency. Its input statement is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedEpimorphicTopDerivedLimit | H5 | The proof elaborates with existing large-coefficient sheafification instances; exact signature preserved. |

No consumer adaptation is needed. The complete item compiles cleanly in 5.9 seconds,
with no remaining holes. The original and delivered signature texts were compared
verbatim and are equal.

## Status

landed 20261021T111151-L-30437 2026-10-21 (merge of deliver/H5/Sheaf.AlgebraicGeometry.ProEtaleBoundedEpimorphicTopDerivedLimit)
