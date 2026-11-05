/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.NativeHomSingleShift
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse

/-!
# Tate twists as tensor products of Weil complexes

The Tate twist `K ↦ K(m)` of Weil complexes (`AlgebraicGeometry.WeilComplex.tateTwist`) is
defined as the derived tensor product with the lisse Tate sheaf `ℚ̄_ℓ(m)`, through the derived
internal hom out of its dual. This file compares it, followed by a shift `[n]`, with the native
derived tensor product of Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`) with the Weil complex `ℚ̄_ℓ(m)[n]`
(`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`).

## Proof

The Tate sheaf `ℚ̄_ℓ(m)` is the constant twist `ℚ̄_ℓ ⊗ 𝓑_c` of `ℚ̄_ℓ` by `c = χ_ℓ(σ)ᵐ`, and the
Tate twist of Weil complexes is the derived constant twist `C` by `c`
(`AlgebraicGeometry.WeilComplex.tateTwistCompιIso`), an autoequivalence with inverse the
twist by `c⁻¹`. In the ambient derived category, `- ⊗ ℚ̄_ℓ(m)[n]` is left adjoint to the native
internal hom `RHom(ℚ̄_ℓ(m)[n], -)`, which is `C⁻¹(-)[-n]` since `𝓗om(ℚ̄_ℓ ⊗ 𝓑_c, -)` is the
constant twist by `c⁻¹` (`AlgebraicGeometry.ProEtaleWeilSheaf.nativeHomSingleShiftIso`). The
functor `C(-)[n]` is also left adjoint to `C⁻¹(-)[-n]`, so the two left adjoints agree.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Tate twists are tensor products** (blueprint: `def-wf-tate-twist`, where the Tate twist
`K(m) = K ⊗^L ℚ̄_ℓ(m)` is the derived tensor product with the Tate sheaf): for a Weil complex `K`
on `X`, the native derived tensor product `K ⊗ ℚ̄_ℓ(m)[n]` is the shifted Tate twist `K(m)[n]`,
naturally in `K`. -/
theorem nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift (m n : ℤ) :
    Nonempty ((𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const (WeilComplex k₀ l X)).obj
        (((tateTwist k₀ l X m).obj
          (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧)) ⋙
          nativeConstructibleTensor k₀ l X ≅
      tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) n) := by
  let := (ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
  let c := WeilSheaf.cyclotomicUnit k₀ l ^ m
  let ι := (objectProperty k₀ l X).ι
  let C := (ProEtaleWeilSheaf.constantTwist k₀ l X c).mapDerivedCategory
  let A := (ProEtaleWeilSheaf.constantTwist k₀ l X c).obj (ProEtaleWeilSheaf.adicConstant k₀ l X)
  let P := DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A⟦n⟧)
  let T := ((tateTwist k₀ l X m).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦n⟧
  -- `𝓗om(ℚ̄_ℓ ⊗ 𝓑_c, -)` is the constant twist by `c⁻¹`.
  let τ : ProEtaleWeilSheaf.ihomFunctor k₀ l X A ≅ ProEtaleWeilSheaf.constantTwist k₀ l X c⁻¹ :=
    ProEtaleWeilSheaf.ihomFunctorConstantTwistLeftIso _ c ≪≫
      Functor.isoWhiskerRight (ProEtaleWeilSheaf.ihomFunctorAdicConstantIso k₀ l X) _ ≪≫
      Functor.leftUnitor _
  -- The derived constant twist by `c` is an autoequivalence, with inverse the twist by `c⁻¹`.
  let E : DerivedCategory (ProEtaleWeilSheaf k₀ l X) ≌ DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
    CategoryTheory.Equivalence.mk C (ProEtaleWeilSheaf.constantTwist k₀ l X c⁻¹).mapDerivedCategory
      ((Functor.mapDerivedCategoryIdIso _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((ProEtaleWeilSheaf.constantTwistOneIso k₀ l X).symm ≪≫
            ProEtaleWeilSheaf.constantTwistFunctorCongrIso k₀ l X (mul_inv_cancel c).symm ≪≫
            (ProEtaleWeilSheaf.constantTwistCompConstantTwistIso k₀ l X _ _).symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtaleWeilSheaf.constantTwistCompConstantTwistIso k₀ l X _ _ ≪≫
            ProEtaleWeilSheaf.constantTwistFunctorCongrIso k₀ l X (inv_mul_cancel c) ≪≫
            ProEtaleWeilSheaf.constantTwistOneIso k₀ l X) ≪≫
        Functor.mapDerivedCategoryIdIso _)
  -- `- ⊗ P` and `C(-)[n]` are both left adjoint to `C⁻¹(-)[-n]`.
  let σ : tensorRight P ≅ shiftFunctor _ n ⋙ C :=
    (((ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilClosed.adjunction P)
      |>.ofNatIsoRight (ProEtaleWeilSheaf.nativeHomSingleShiftIso A n _ τ)).leftAdjointUniq
      ((shiftEquiv _ n).trans E).toAdjunction
  -- The Weil complex `ℚ̄_ℓ(m)[n]` is `P`.
  let ε : T.obj ≅ P :=
    (ι.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso ((tateTwistCompιIso m).app _ ≪≫
        ((ProEtaleWeilSheaf.constantTwist k₀ l X c).mapDerivedCategorySingleFunctor 0).app
          (ProEtaleWeilSheaf.adicConstant k₀ l X) ≪≫
        (DerivedCategory.singleFunctorIsoCompQ _ 0).app A) ≪≫
      ((DerivedCategory.Q.commShiftIso n).app _).symm
  let ε' : tensorRight T.obj ≅ tensorRight P :=
    NatIso.ofComponents (fun K ↦ whiskerLeftIso K ε) (fun f ↦ by simp [whisker_exchange])
  let α : ((𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const (WeilComplex k₀ l X)).obj T) ⋙
      nativeConstructibleTensor k₀ l X) ⋙ ι ≅ ι ⋙ tensorRight T.obj :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
      dsimp [nativeConstructibleTensor, ProEtaleWeilSheaf.nativeDerivedTensor,
        WeilConjectures.CoefficientClosedStructure.tensor]
      simp only [Category.comp_id, Category.id_comp]
      exact MonoidalCategory.tensorHom_id f.hom T.obj)
  refine ⟨((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso ?_⟩
  exact α ≪≫
    Functor.isoWhiskerLeft ι (ε' ≪≫ σ ≪≫ C.commShiftIso n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tateTwistCompιIso m).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ι.commShiftIso n).symm ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.WeilComplex
