/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityNativeHomSingle
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula

/-!
# Native tensor with the Tate sheaf

The native tensor and scalar Tate twist have the same right adjoint. The
comparison is therefore natural on the ambient derived category and restricts
to Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Native derived tensor with the Tate sheaf is the derived scalar twist. -/
noncomputable def nativeDerivedTensorTateIso (d : ℤ) :
    Prod.sectR ((DerivedCategory.singleFunctor _ 0).obj
      (WeilSheaf.tateTwistSheaf k₀ l X d).obj) _ ⋙ nativeDerivedTensor k₀ l X ≅
      (constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).mapDerivedCategory := by
  let b := WeilSheaf.cyclotomicUnit k₀ l ^ d
  let F := constantTwist k₀ l X b
  let G := constantTwist k₀ l X b⁻¹
  let ef : F ⋙ G ≅ 𝟭 _ :=
    constantTwistCompConstantTwistIso k₀ l X b b⁻¹ ≪≫
      constantTwistFunctorCongrIso k₀ l X (mul_inv_cancel b) ≪≫ constantTwistOneIso k₀ l X
  let eg : G ⋙ F ≅ 𝟭 _ :=
    constantTwistCompConstantTwistIso k₀ l X b⁻¹ b ≪≫
      constantTwistFunctorCongrIso k₀ l X (inv_mul_cancel b) ≪≫ constantTwistOneIso k₀ l X
  let E : ProEtaleWeilSheaf k₀ l X ≌ ProEtaleWeilSheaf k₀ l X :=
    CategoryTheory.Equivalence.mk F G ef.symm eg
  let adj : F.mapDerivedCategory ⊣ G.mapDerivedCategory := E.mapDerivedCategory.toAdjunction
  let A := (WeilSheaf.tateTwistSheaf k₀ l X d).obj
  let eH : ihomFunctor k₀ l X A ≅ G :=
    ihomFunctorMapIsoLeft (WeilSheaf.tateTwistSheafObjIso k₀ l X d).symm ≪≫
      ihomFunctorConstantTwistLeftIso _ b ≪≫
      Functor.isoWhiskerRight (ihomFunctorAdicConstantIso k₀ l X) G ≪≫ Functor.leftUnitor G
  let C := nativeDerivedClosedComparison k₀ l X
  letI := C.weilClosed.monoidal
  letI := C.weilSymmetry
  let T := (DerivedCategory.singleFunctor _ 0).obj A
  let eT : tensorRight T ≅ Prod.sectR T _ ⋙ nativeDerivedTensor k₀ l X :=
    (BraidedCategory.tensorLeftIsoTensorRight T).symm ≪≫
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦ by
        dsimp [nativeDerivedTensor, WeilConjectures.CoefficientClosedStructure.tensor]
        change T ◁ g ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 T ⊗ₘ g)
        simp)
  exact eT.symm ≪≫
    ((C.weilClosed.adjunction T).ofNatIsoRight
      (nativeHomSingleIso A ≪≫ Functor.rightDerivedFunctorNatIso eH ≪≫
        G.rightDerivedFunctorIsoMapDerivedCategory)).leftAdjointUniq adj

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The native tensor by a Tate sheaf agrees with the existing Tate twist functor. -/
noncomputable def nativeConstructibleTensorTateIso (d : ℤ) :
    Prod.sectR (WeilSheaf.toComplex.obj (WeilSheaf.tateTwistSheaf k₀ l X d)) _ ⋙
      nativeConstructibleTensor k₀ l X ≅ tateTwist k₀ l X d :=
  ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
      (ProEtaleWeilSheaf.nativeDerivedTensorTateIso d) ≪≫ (tateTwistCompιIso d).symm)

end AlgebraicGeometry.WeilComplex
