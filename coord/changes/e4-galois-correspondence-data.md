# Galois correspondence data and generated structure lemmas

## Reason

The component theorems must refer to the finite and adic correspondence types, so those
existing definitions must be available below the theorem that imports the components.
Move all 46 data declarations to `Sheaf.Paper.GaloisLisseCorrespondenceData` and publicly
re-export that module from the original module. Their fully qualified names, normalized
signatures and definition bodies are identical. A parser comparison checked all 46.
This is an import-cycle separation, with all statements retaining exactly their meaning.

The four large structures also trigger expensive automatic constructor injectivity and
size-of specification generation. Profiling showed generated `mk.congr_simp` / `mk.injEq`
work comparing prime parameters through p-adic norms and repeated module instances.
The extracted data module exceeded the 60-second limit when producing its olean before
these local generation options were added.
Disable those optional generated lemmas locally on the four structures. The repaired data
module compiles with its olean in 25 seconds; the theorem module compiles in about 25 seconds. This performance repair is independent of the import-cycle separation.

No binder, universe, field, construction, target, or mathematical predicate changes.
Only unused automatically generated constructor/size-of lemma names cease to be generated.
There are no downstream references to them or to any of the moved data declarations.

## Old

All 46 data declarations were in `Sheaf.Paper.GaloisLisseRepresentations`. The four
structure declarations receiving scoped generation options were, verbatim:

```lean
structure GaloisLisseFiniteData
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)] where
  γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
    (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
  Φ : Y.FiniteEtale ≌ Y.FLC
  η : Φ.functor ⋙ ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
    FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  e : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], LisseModuleSheafCategory Y Λ ≌
    galoisFiniteRepresentations Λ G
  τ : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], (e Λ).functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u
    + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅ ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A :=
    ModuleCat.{u + 1} Λ)

structure GaloisLisseFiniteCorrespondence
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    extends GaloisLisseFiniteData y G where
  yonedaComparison : galoisYonedaComparison y G toGaloisLisseFiniteData
  finiteEtaleAction : galoisFiniteEtaleAction y G toGaloisLisseFiniteData
  finiteAbelian : galoisFiniteAbelian y G toGaloisLisseFiniteData
  finiteKernels : galoisFiniteKernels y G toGaloisLisseFiniteData
  finiteCokernels : galoisFiniteCokernels y G toGaloisLisseFiniteData
  finiteLimits : galoisFiniteLimits y G toGaloisLisseFiniteData
  finiteColimits : galoisFiniteColimits y G toGaloisLisseFiniteData
  finiteUnit : galoisFiniteUnit y G toGaloisLisseFiniteData
  finiteEvaluationAction : galoisFiniteEvaluationAction y G toGaloisLisseFiniteData
  finiteTensor : galoisFiniteTensor y G toGaloisLisseFiniteData
  finiteScalarExtension : galoisFiniteScalarExtension y G toGaloisLisseFiniteData

structure GaloisLisseAdicData
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] where
  P : ProfiniteGrp.{u}
  δ : G ≃ₜ* P
  eI : ∀ E : Padic.FiniteCoefficientFields l Q, LisseIntegralSheaf l E.val Y ≌
    galoisIntegralRepresentations l E.val P δ
  eR : ∀ E : Padic.FiniteCoefficientFields l Q, LisseRationalSheaf l E.val Y ≌
    galoisCoefficientRepresentations l E.val P δ
  eA : LisseAlgebraicSheaf l Y Q ≌ galoisAdicRepresentations l Q P δ
  τI : ∀ E : Padic.FiniteCoefficientFields l Q, (eI E).functor ⋙ ObjectProperty.ι _ ⋙ forget₂
    (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G) (ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E.val)) ≅ lisseIntegralFiberFunctor l E.val Y y
  τR : ∀ E : Padic.FiniteCoefficientFields l Q, (eR E).functor ⋙ ObjectProperty.ι _ ⋙ forget₂
    (Rep.{u + 1} E.val G) (ModuleCat.{u + 1} E.val) ≅ lisseRationalFiberFunctor l E.val Y y
  τA : eA.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Q G) (ModuleCat.{u + 1} Q) ≅
    lisseAlgebraicFiberFunctor l Y y Q

structure GaloisLisseAdicCorrespondence
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    extends GaloisLisseAdicData y G c l Q where
  rationalSheavesAbelian : galoisRationalSheavesAbelian y G c l Q toGaloisLisseAdicData
  rationalRepresentationsAbelian : galoisRationalRepresentationsAbelian y G c l Q
    toGaloisLisseAdicData
  rationalFiniteLimits : galoisRationalFiniteLimits y G c l Q toGaloisLisseAdicData
  rationalFiniteColimits : galoisRationalFiniteColimits y G c l Q toGaloisLisseAdicData
  algebraicSheavesAbelian : galoisAlgebraicSheavesAbelian y G c l Q toGaloisLisseAdicData
  algebraicRepresentationsAbelian : galoisAlgebraicRepresentationsAbelian y G c l Q
    toGaloisLisseAdicData
  algebraicFiniteLimits : galoisAlgebraicFiniteLimits y G c l Q toGaloisLisseAdicData
  algebraicFiniteColimits : galoisAlgebraicFiniteColimits y G c l Q toGaloisLisseAdicData
  integralEvaluationAction : galoisIntegralEvaluationAction y G c l Q toGaloisLisseAdicData
  rationalEvaluationAction : galoisRationalEvaluationAction y G c l Q toGaloisLisseAdicData
  integralMonoidal : galoisIntegralMonoidal y G c l Q toGaloisLisseAdicData
  rationalMonoidal : galoisRationalMonoidal y G c l Q toGaloisLisseAdicData
  algebraicMonoidal : galoisAlgebraicMonoidal y G c l Q toGaloisLisseAdicData
  integralTensor : galoisIntegralTensor y G c l Q toGaloisLisseAdicData
  integralUnit : galoisIntegralUnit y G c l Q toGaloisLisseAdicData
  rationalTensor : galoisRationalTensor y G c l Q toGaloisLisseAdicData
  rationalUnit : galoisRationalUnit y G c l Q toGaloisLisseAdicData
  algebraicTensor : galoisAlgebraicTensor y G c l Q toGaloisLisseAdicData
  algebraicUnit : galoisAlgebraicUnit y G c l Q toGaloisLisseAdicData
  algebraicModelScalarExtension : galoisAlgebraicModelScalarExtension y G c l Q
    toGaloisLisseAdicData
  integralScalarExtension : galoisIntegralScalarExtension y G c l Q toGaloisLisseAdicData
  rationalScalarExtension : galoisRationalScalarExtension y G c l Q toGaloisLisseAdicData
```

## New

The 46 declarations are in `Sheaf.Paper.GaloisLisseCorrespondenceData`, publicly imported
by `Sheaf.Paper.GaloisLisseRepresentations`. The original public imports are public imports of the data module and remain re-exported.
All mathematical definitions are copied unchanged. The four structure declarations are:

```lean
set_option genSizeOfSpec false in
set_option genInjectivity false in
structure GaloisLisseFiniteData
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)] where
  γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
    (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
  Φ : Y.FiniteEtale ≌ Y.FLC
  η : Φ.functor ⋙ ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
    FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  e : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], LisseModuleSheafCategory Y Λ ≌
    galoisFiniteRepresentations Λ G
  τ : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], (e Λ).functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u
    + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅ ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A :=
    ModuleCat.{u + 1} Λ)

set_option genSizeOfSpec false in
set_option genInjectivity false in
structure GaloisLisseFiniteCorrespondence
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    extends GaloisLisseFiniteData y G where
  yonedaComparison : galoisYonedaComparison y G toGaloisLisseFiniteData
  finiteEtaleAction : galoisFiniteEtaleAction y G toGaloisLisseFiniteData
  finiteAbelian : galoisFiniteAbelian y G toGaloisLisseFiniteData
  finiteKernels : galoisFiniteKernels y G toGaloisLisseFiniteData
  finiteCokernels : galoisFiniteCokernels y G toGaloisLisseFiniteData
  finiteLimits : galoisFiniteLimits y G toGaloisLisseFiniteData
  finiteColimits : galoisFiniteColimits y G toGaloisLisseFiniteData
  finiteUnit : galoisFiniteUnit y G toGaloisLisseFiniteData
  finiteEvaluationAction : galoisFiniteEvaluationAction y G toGaloisLisseFiniteData
  finiteTensor : galoisFiniteTensor y G toGaloisLisseFiniteData
  finiteScalarExtension : galoisFiniteScalarExtension y G toGaloisLisseFiniteData

set_option genSizeOfSpec false in
set_option genInjectivity false in
structure GaloisLisseAdicData
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] where
  P : ProfiniteGrp.{u}
  δ : G ≃ₜ* P
  eI : ∀ E : Padic.FiniteCoefficientFields l Q, LisseIntegralSheaf l E.val Y ≌
    galoisIntegralRepresentations l E.val P δ
  eR : ∀ E : Padic.FiniteCoefficientFields l Q, LisseRationalSheaf l E.val Y ≌
    galoisCoefficientRepresentations l E.val P δ
  eA : LisseAlgebraicSheaf l Y Q ≌ galoisAdicRepresentations l Q P δ
  τI : ∀ E : Padic.FiniteCoefficientFields l Q, (eI E).functor ⋙ ObjectProperty.ι _ ⋙ forget₂
    (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G) (ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E.val)) ≅ lisseIntegralFiberFunctor l E.val Y y
  τR : ∀ E : Padic.FiniteCoefficientFields l Q, (eR E).functor ⋙ ObjectProperty.ι _ ⋙ forget₂
    (Rep.{u + 1} E.val G) (ModuleCat.{u + 1} E.val) ≅ lisseRationalFiberFunctor l E.val Y y
  τA : eA.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Q G) (ModuleCat.{u + 1} Q) ≅
    lisseAlgebraicFiberFunctor l Y y Q

set_option genSizeOfSpec false in
set_option genInjectivity false in
structure GaloisLisseAdicCorrespondence
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    extends GaloisLisseAdicData y G c l Q where
  rationalSheavesAbelian : galoisRationalSheavesAbelian y G c l Q toGaloisLisseAdicData
  rationalRepresentationsAbelian : galoisRationalRepresentationsAbelian y G c l Q
    toGaloisLisseAdicData
  rationalFiniteLimits : galoisRationalFiniteLimits y G c l Q toGaloisLisseAdicData
  rationalFiniteColimits : galoisRationalFiniteColimits y G c l Q toGaloisLisseAdicData
  algebraicSheavesAbelian : galoisAlgebraicSheavesAbelian y G c l Q toGaloisLisseAdicData
  algebraicRepresentationsAbelian : galoisAlgebraicRepresentationsAbelian y G c l Q
    toGaloisLisseAdicData
  algebraicFiniteLimits : galoisAlgebraicFiniteLimits y G c l Q toGaloisLisseAdicData
  algebraicFiniteColimits : galoisAlgebraicFiniteColimits y G c l Q toGaloisLisseAdicData
  integralEvaluationAction : galoisIntegralEvaluationAction y G c l Q toGaloisLisseAdicData
  rationalEvaluationAction : galoisRationalEvaluationAction y G c l Q toGaloisLisseAdicData
  integralMonoidal : galoisIntegralMonoidal y G c l Q toGaloisLisseAdicData
  rationalMonoidal : galoisRationalMonoidal y G c l Q toGaloisLisseAdicData
  algebraicMonoidal : galoisAlgebraicMonoidal y G c l Q toGaloisLisseAdicData
  integralTensor : galoisIntegralTensor y G c l Q toGaloisLisseAdicData
  integralUnit : galoisIntegralUnit y G c l Q toGaloisLisseAdicData
  rationalTensor : galoisRationalTensor y G c l Q toGaloisLisseAdicData
  rationalUnit : galoisRationalUnit y G c l Q toGaloisLisseAdicData
  algebraicTensor : galoisAlgebraicTensor y G c l Q toGaloisLisseAdicData
  algebraicUnit : galoisAlgebraicUnit y G c l Q toGaloisLisseAdicData
  algebraicModelScalarExtension : galoisAlgebraicModelScalarExtension y G c l Q
    toGaloisLisseAdicData
  integralScalarExtension : galoisIntegralScalarExtension y G c l Q toGaloisLisseAdicData
  rationalScalarExtension : galoisRationalScalarExtension y G c l Q toGaloisLisseAdicData
```

## Users

`tools/downstream.py Sheaf.Paper.GaloisLisseRepresentations --uses` was run for the four
structures and the affected action/representation definitions. It listed 34 downstream
modules and no use outside the item itself. A second comparison checked every moved
signature and definition body, not only the primary structures. Holders are recorded at
preparation time; none of these modules is adapted by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| TargetsCheck | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.Statement | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same exported declarations and definitions; no source edit required. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same exported declarations and definitions; no source edit required. |

## Status

landed 20261018T111931-L-553702 2026-10-18 (merge of deliver/E4/Sheaf.Paper.GaloisLisseRepresentations)
