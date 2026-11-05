/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Pull.NativePullKFlat
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.NativeTensorAcyclicTestComparison
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryKFlatLocalization
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorChain
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AcyclicTransport

/-!
# Pullback of pro-étale Weil sheaves preserves native K-flat complexes

For any morphism `g : Z ⟶ Y` of `k₀`-schemes, the termwise pullback `g^*` of pro-étale Weil
sheaves sends native K-flat complexes (`AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat`) to
native K-flat complexes: forgetting Frobenius, the underlying complex is K-flat, the pullback of
`ℓ`-adic sheaves preserves K-flatness
(`AlgebraicGeometry.ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj`), and the native
acyclic tensor test can be checked after forgetting Frobenius.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
open scoped CategoryTheory.Obj
open ZeroObject

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- A K-flat complex of `ℓ`-adic sheaves passes the ordinary acyclic tensor test. -/
theorem nativeOrdinaryKFlat_of_kFlat (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ Q ⊗ P)
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    NativeOrdinaryKFlat l Y P := by
  intro N hN
  let Z : CochainComplex (ProEtale.AdicSheaf l Y) ℤ := 0
  have hZ : Z.Acyclic := HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
  have hs : QuasiIso (0 : Z ⟶ N) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt _ n (hZ n)).mpr (hN n)
  have ht : QuasiIso ((0 : Z ⟶ N) ▷ P) := hP.2 _ hs
  have hz : (Z ⊗ P).Acyclic := by
    have : (tensorRight P).Additive :=
      inferInstanceAs (((curriedTensor (ProEtale.AdicSheaf l Y)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj P).Additive
    exact HomologicalComplex.acyclic_of_isZero _
      ((tensorRight P).map_isZero (isZero_zero _))
  intro n
  have : QuasiIsoAt ((0 : Z ⟶ N) ▷ P) n := (quasiIso_iff _).mp ht n
  exact ((quasiIsoAt_iff_exactAt _ n (hz n)).mp this).of_iso (κ P N).symm

/-- An ordinary K-flat complex of `ℓ`-adic sheaves is K-flat. -/
theorem kFlat_of_nativeOrdinaryKFlat (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ Q ⊗ P)
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (hP : NativeOrdinaryKFlat l Y P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P :=
  (HomotopyCategory.kFlat_quotient_obj_iff P).1 (nativeOrdinaryKFlat_homotopy l Y κ P hP)

/-- Pullback of `ℓ`-adic sheaves preserves the ordinary acyclic tensor test. -/
theorem nativeOrdinaryKFlat_adicUpperStar (l : ℕ) [Fact l.Prime] {S T : Scheme.{u}}
    (h : S ⟶ T)
    (κS : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l S) ℤ,
      ordinaryTensorTotal l S P Q ≅ Q ⊗ P)
    (κT : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l T) ℤ,
      ordinaryTensorTotal l T P Q ≅ Q ⊗ P)
    (P : CochainComplex (ProEtale.AdicSheaf l T) ℤ) (hP : NativeOrdinaryKFlat l T P) :
    NativeOrdinaryKFlat l S (((ProEtale.adicUpperStar l h).mapHomologicalComplex (.up ℤ)).obj P) :=
  nativeOrdinaryKFlat_of_kFlat l S κS _
    (ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj l h _
      (kFlat_of_nativeOrdinaryKFlat l T κT P hP))

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- Acyclicity of a complex of pro-étale Weil sheaves is detected after forgetting the Weil
structure. -/
theorem acyclic_of_acyclic_forget (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (C : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (h : (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
      |>.mapHomologicalComplex
        (.up ℤ)).obj C).Acyclic) :
    C.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff]
  have hn := h n
  rw [HomologicalComplex.exactAt_iff] at hn
  exact (ShortComplex.exact_map_iff_of_faithful (C.sc n)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).1 hn

/-- Forgetting the Weil structure commutes with pullback, as functors of sheaves. -/
theorem nonempty_upperStar_comp_forget_iso {Z Y : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty (upperStar k₀ l g ⋙ Endofunctor.IsoAlgebra.forget _ ≅
        Endofunctor.IsoAlgebra.forget _ ⋙ ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀))))) :=
  ⟨Iso.refl _⟩

/-- **Pullback preserves native K-flat complexes**: for any morphism `g : Z ⟶ Y` of
`k₀`-schemes, the termwise pullback of a native K-flat complex of pro-étale Weil sheaves is
native K-flat. Forgetting Frobenius, the underlying complex is K-flat, its pullback is K-flat
(`AlgebraicGeometry.ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj`), and the acyclic
tensor test on `Z` holds after forgetting Frobenius. -/
theorem nativeIsKFlat_upperStar [Fact (ringChar k₀ ≠ l)] {Z Y : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hP : NativeIsKFlat k₀ l Y P) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨-, -, -, -, -, κY, -⟩ := (nativeDerivedClosedComparison k₀ l Y).ordinaryTensorModels
  obtain ⟨-, -, -, -, -, κZ, -⟩ := (nativeDerivedClosedComparison k₀ l Z).ordinaryTensorModels
  obtain ⟨e⟩ := nonempty_upperStar_comp_forget_iso k₀ l g
  let UZ := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)
  have h₁ := nativeOrdinaryKFlat_adicUpperStar l
    (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) κZ κY _
    (native_two_sided_kflat_forget k₀ l Y P hP)
  have h₂ : NativeOrdinaryKFlat l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
      ((UZ.mapHomologicalComplex (.up ℤ)).obj
        (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P)) := by
    intro N hN n
    let iso := (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app P).symm
    exact (h₁ N hN n).of_iso
      ((((ordinaryTensorBifunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
        ).map₂CochainComplex).flip.obj N).mapIso iso.symm)
  have : (nativeTensorBifunctor k₀ l Z).Additive :=
    { map_add := fun {_ _ _ _} ↦ by
        apply NatTrans.ext
        funext N
        exact ((nativeTensorBifunctor k₀ l Z).flip.obj N).map_add }
  have (M : ProEtaleWeilSheaf k₀ l Z) : ((nativeTensorBifunctor k₀ l Z).obj M).Additive :=
    (tensorIhomAdjunction k₀ l Z M).left_adjoint_additive
  obtain ⟨chain, -⟩ := native_weil_tensor_chain k₀ l Z
    (nativeTensorBifunctor k₀ l Z) (tensorBifunctorForget k₀ l Z)
  apply native_tensor_acyclic_test_kflat k₀ l Z
  intro N hN
  apply acyclic_of_acyclic_forget
  intro n
  exact (h₂ _ (hN.map UZ) n).of_iso (chain _ N).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
