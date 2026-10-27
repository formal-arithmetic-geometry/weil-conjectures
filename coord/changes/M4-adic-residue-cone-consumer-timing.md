# AlgebraicGeometry.Scheme.adicResidue_koszul_tensor_cone_proZero

## Reason

The sole direct importer of the assigned module is unclaimed and its original
source failed the required consumer check:

> NOT ACCEPTED: this compile took 62 s > 60 s, the limit for one file.

Profiling its original source against this delivery located the comparison
`obtain` at 19.5 seconds, the remaining cone construction at 4.03 seconds, and
kernel checking and linting at about 15.7 seconds each. Keep the coefficient
category abstract when deriving quasi-isomorphism preservation from exactness
and when constructing the cone isomorphism. Specify the comparison theorem's
universes and avoid unfolding coefficient sections and the tensor transpose.

All existing declarations, public imports, signatures, binders and attributes
exported to consumers remain identical. Added helpers are private and proved;
reducibility attributes are local to this proof module. There are no new holes.
The mathematical route and node statement are unchanged.

## Old

```lean
  have hcoef : FlatConstantConeProZero ε :=
    proZero_of_exact_comparison (E.mapHomologicalComplex (.up ℤ))
      (fun g hg ↦ by
        have : QuasiIso g := hg
        infer_instance) _ _ _ e he hz
  have ht := flatConstantConeProZero_tensor (C := Over U) (O := R)
    ((coefficientProEtaleModelTopology.{u, v} X).over U) P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (R := R) P).2 hP) ε hcoef
  let f := (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map
    (Functor.whiskerRight ε ((ringedKoszulTensor R).obj P))
  let α := adicResidueKoszulTensorAugmentation X J U r b P ε
  let c : CochainComplex.mappingCone α ≅ CochainComplex.mappingCone f :=
    HomologicalComplex.homotopyCofiber.mapArrowIso α f
      (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.isoMk (adicResidueKoszulTensorTranspose X J U r b P) (Iso.refl _)
        (by
          simp only [Iso.refl_hom, Category.comp_id]
          symm
          unfold α adicResidueKoszulTensorAugmentation
          rfl))
```

## New

Added these proved private helpers:

```lean
/-- Keep exact-functor instances abstract while transporting the derived zero maps. -/
private theorem proZero_of_exact_realization
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : ℕ → CochainComplex C ℤ) (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (T : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.obj (op n))
    (he : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map (t n m h) ≫ (e n).hom =
      (e m).hom ≫ T.map (homOfLE h).op)
    (hz : ∀ n, ∃ m h, DerivedCategory.Q.map (t n m h) = 0) :
    ∀ n, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map (T.map (homOfLE h).op) = 0 := by
  exact proZero_of_exact_comparison (E.mapHomologicalComplex (.up ℤ))
    (fun g hg ↦ by
      have : QuasiIso g := hg
      infer_instance) K t T e he hz

/-- Construct the cone comparison before specializing the coefficient category. -/
private def coneIsoOfSource
    {B : Type*} [Category B] [Abelian B]
    {K K' L : CochainComplex B ℤ} (f : K' ⟶ L) (e : K ≅ K') :
    CochainComplex.mappingCone (e.hom ≫ f) ≅ CochainComplex.mappingCone f :=
  HomologicalComplex.homotopyCofiber.mapArrowIso (e.hom ≫ f) f
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    (Arrow.isoMk e (Iso.refl _) (by simp))

```

The replacement proof fragment is:

```lean
  have hcoef : FlatConstantConeProZero ε :=
    proZero_of_exact_realization E _ _ _ e he hz
  have ht := flatConstantConeProZero_tensor (C := Over U) (O := R)
    ((coefficientProEtaleModelTopology.{u, v} X).over U) P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (R := R) P).2 hP) ε hcoef
  let f := (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map
    (Functor.whiskerRight ε ((ringedKoszulTensor R).obj P))
  let α := adicResidueKoszulTensorAugmentation X J U r b P ε
  let c : CochainComplex.mappingCone α ≅ CochainComplex.mappingCone f := by
    unfold α adicResidueKoszulTensorAugmentation
    exact coneIsoOfSource f (adicResidueKoszulTensorTranspose X J U r b P)
```

The call to the assigned comparison theorem now supplies `.{u, v}` explicitly.
The existing local irreducibility list additionally contains `coefficientMap`,
`algebraSection`, `ringedKoszulSliceSection` and
`adicResidueKoszulTensorTranspose`. No global reducibility setting changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicResidueKoszulTensorConeProZero | unclaimed | Proof timing repair; no public interface change. |
| Sheaf.Paper.AdicResidueStrictKoszulAugmentation | unclaimed | Sole direct importer; all imported signatures and exports unchanged, no adaptation. |

## Status

landed 20261026T135627-L-4051345 2026-10-26 (merge of deliver/M4/Sheaf.Paper.AdicResidueKoszulCoefficientConeComparison)
