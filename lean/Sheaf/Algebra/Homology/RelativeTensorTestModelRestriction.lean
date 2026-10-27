module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Linear
import Sheaf.Algebra.Homology.RingedDerivedTensorNative

/-! # Algebra-linear test-resolution models of the base derived tensor

Source: Stacks Project, More on Algebra, Tags 0B67, 06Y5 and 064M;
Sites Cohomology, Tags 06YU and 0FPT.
(blueprint: lem-trf-relative-tensor-test-model-restriction).

The signed direct-sum total tensor is the existing `ModuleCat.mixedTotalTensor`.
The comparisons below form one family, natural in both chain maps and augmentations.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ModuleCat

/-- Algebra-linear test models restrict to the derived tensor over the base ring.
Source: Stacks Project, More on Algebra, Tag 0B67, proof of
`lemma-tor-amplitude-localization`, expanded by Tags 06Y5 and 064M.
(blueprint: lem-trf-relative-tensor-test-model-restriction).

Proof plan:
1. Use `def-pc-mixed-total-tensor` to form the actual A-complex with the A-action
   on K and differential d_K tensor 1 + (-1)^p 1 tensor d_P. Restriction identifies
   this with Tot(Res K tensor P), naturally in both maps, on each pure tensor.
2. Apply the one-K-flat native localization comparison of
   `lem-sf-ringed-derived-native-tensor` (Tags 06YU, 0FPT) to Res K and P on the
   one-object identity-cover site. Compose its inverse tensorator with Q of the
   restriction identification and then 1 tensor Q ε. The last map is invertible
   by `def-weil-abstract-derived-category`, since ε is a quasi-isomorphism.
3. Naturality of the inverse tensorator in both inputs, the symbolwise naturality
   of the restriction identification, and h followed by ε' = ε followed by g[0]
   give the displayed square. No quasi-isomorphism assumption on h is needed.
4. Specialize f to multiplication by a, g and h to identities. This identifies
   multiplication on the total complex with the stated derived endomorphism.
   Kernels and images of the A-linear differentials are A-submodules, so their
   quotient is an actual A-module. Apply the localization cohomology factorization
   and the exact restriction/homology comparison to η; their naturality gives
   the last scalar square. No flatness of A over R or boundedness is used. -/
theorem exists_relativeTensorTestModelRestriction
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    ∃ η : ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (N : ModuleCat.{u} R)
      (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P →
      ∀ ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N,
      QuasiIso ε →
        (DerivedCategory.Q.obj
          (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
            (((mixedTotalTensor φ).obj K).obj P)) ≅
          (DerivedCategory.Q.obj
            (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ⊗
            DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N))),
      (∀ (K K' : CochainComplex (ModuleCat.{u} A) ℤ) (N N' : ModuleCat.{u} R)
        (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
        (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
        (hP' : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P')
        (ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
        (ε' : P' ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N')
        (hε : QuasiIso ε) (hε' : QuasiIso ε') (f : K ⟶ K') (g : N ⟶ N') (h : P ⟶ P'),
        h ≫ ε' = ε ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g →
        DerivedCategory.Q.map
            (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
              ((((mixedTotalTensor φ).map f).app P ≫ ((mixedTotalTensor φ).obj K').map h))) ≫
          (η K' N' P' hP' ε' hε').hom =
        (η K N P hP ε hε).hom ≫
          (DerivedCategory.Q.map
              (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f) ⊗ₘ
            DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (N : ModuleCat.{u} R)
        (P : CochainComplex (ModuleCat.{u} R) ℤ)
        (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
        (ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
        (hε : QuasiIso ε) (a : A),
        DerivedCategory.Q.map
            (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
              (a • 𝟙 (((mixedTotalTensor φ).obj K).obj P))) ≫
          (η K N P hP ε hε).hom =
        (η K N P hP ε hε).hom ≫
          (DerivedCategory.Q.map
              (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).map (a • 𝟙 K)) ⊗ₘ
            𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} A) ℤ) (N : ModuleCat.{u} R)
        (P : CochainComplex (ModuleCat.{u} R) ℤ)
        (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P)
        (ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)
        (hε : QuasiIso ε) (n : ℤ),
        ∃ e : (restrictScalars φ).obj
            ((((mixedTotalTensor φ).obj K).obj P).homology n) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
            (DerivedCategory.Q.obj
                (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) ⊗
              DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)),
          e = (((((mixedTotalTensor φ).obj K).obj P).sc n).mapHomologyIso
                (restrictScalars φ)).symm ≪≫
            ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app
              (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
                (((mixedTotalTensor φ).obj K).obj P))).symm ≪≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso (η K N P hP ε hε) ∧
          ∀ a : A,
            (restrictScalars φ).map
                (a • 𝟙 ((((mixedTotalTensor φ).obj K).obj P).homology n)) ≫ e.hom =
              e.hom ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
                (DerivedCategory.Q.map
                    (((restrictScalars φ).mapHomologicalComplex (.up ℤ)).map (a • 𝟙 K)) ⊗ₘ
                  𝟙 (DerivedCategory.Q.obj
                    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)))) := by
  sorry

end ModuleCat
