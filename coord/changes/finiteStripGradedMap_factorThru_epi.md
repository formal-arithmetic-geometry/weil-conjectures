# HomologicalComplex₂.finiteStripGradedMap_factorThru_epi

## Reason

STATEMENT-DISPUTED (original statement): a single row does not cover the current
filtration tail. If p<n+1, its composite with the cone source projection to
A.X(n+1) is zero, while the tail contains the full source summand. For example,
take K=0, r=0, A concentrated in degree 1 with a nonzero term, p=n=0 and b=f=0.
The row source and target are zero, while the current tail is A.X(1).

The intended diagonal quotient argument (the explicit cone refinement of
[Stacks Tag 0133](https://stacks.math.columbia.edu/tag/0133)) only requires the row
to cover the graded quotient. The source and all target generators strictly
above p belong to the next tail. The correction replaces the false prequotient
claim with this intended quotient claim, retaining every hypothesis and every
definition. It is proved completely, with no new sorry. The source is a
refinement of the Stacks spectral sequence argument, not a verbatim assertion
of Tag 0133.

The scratch file scratch/Obstruction.lean compiles a conditional categorical
refutation: with p<n+1 and nonzero source term, any subobject containing the
source summand cannot be covered epimorphically by the row. It is evidence, not
a delivered dependency.

## Old

```lean
theorem finiteStripGradedMap_factorThru_epi
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) : Epi ((F.complexStep p n).factorThru
      (finiteStripRowInclusion K A b f p n)
      (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p n))
```

## New

```lean
theorem finiteStripGradedMap_factorThru_epi
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) : Epi (finiteStripGradedMap K r hsupport A b f F hsteps p n)
```

The corrected name is a compatibility alias proved by one application of the
existing `finiteStripGradedMap_epi`. Its category and instance binders are
explicit, with the same universes as the existing theorem. There is only one
substantive proof, in `FiniteStripConeGradedMapEpi`.

## Users

The only external user is the existing epimorphism theorem module:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteStripConeGradedMapSplitEpi | M1 | Corrected alias; imports and uses the existing quotient theorem. |
| Sheaf.Algebra.Homology.FiniteStripConeGradedMapEpi | unclaimed | Forced proof and proof-import adaptation; exact signature and visibility retained. |

The original caller fails at line 51 against the corrected signature: it expects
Epi of the row-to-tail factorization, while the corrected name supplies Epi of
the graded quotient map. Replace its proof with the direct joint-image and
cokernel cancellation proof. Four fully proved private helpers support that
proof. Remove its proof-only import of SplitEpi, which otherwise creates a
cycle when SplitEpi imports the existing theorem as requested by return X-80797.
No public import or existing caller signature changes. These are the necessary
proof and import changes for this dependency reversal; no other consumer is
adapted. The original also depends on its own old compiled epimorphism theorem
through the reversed import when checked against the overlay, but fails with
the recorded type mismatch rather than compiling.

The two node copies now record the dependency reversal, with no DAG cycle.
All downstream interfaces through `finiteStripGradedMap_epi` stay identical.
No target or definition changes. The split node's statement correction remains
as documented above; the epimorphism node's statement stays unchanged.

## Status

landed 20261013T190144-L-3217385 2026-10-13 (merge of deliver/M1/Sheaf.Algebra.Homology.FiniteStripConeGradedMapSplitEpi)
