/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarKFlat
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryKFlatLocalization
import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryCanonicalTensorRepresentatives
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilUnderivedTensor
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.BifunctorFlip

/-!
# The pullback of native Weil complexes preserves K-flatness

For an arbitrary morphism `p : Z ⟶ Y` of `k₀`-schemes, the pullback `p^*` of pro-étale Weil
sheaves, applied degreewise, sends complexes which are K-flat for the native tensor product
(`AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat`) to K-flat complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_mapHomologicalComplex_obj`).

Forgetting the Weil structure identifies the native K-flatness of a complex `P` with the K-flatness
of its underlying complex of `ℓ`-adic sheaves on the geometric fibre:

* if `P` is natively K-flat, then so is its underlying complex
  (`AlgebraicGeometry.ProEtaleWeilSheaf.native_two_sided_kflat_forget`);
* conversely, forgetting is exact, reflects isomorphisms and commutes with the tensor product of
  complexes, so a native tensor test may be checked after forgetting
  (`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_of_kFlat_forget`).

The underlying complex of `p^* P` is the pullback along the geometric fibre `p̄` of the underlying
complex of `P`, and the pullback of `ℓ`-adic sheaves preserves K-flat complexes
(`AlgebraicGeometry.ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u a va b vb

open CategoryTheory CategoryTheory.Limits MonoidalCategory WeilConjectures

namespace AlgebraicGeometry.ProEtaleWeilSheaf

/-- A natural isomorphism of uncurried bifunctors, curried. -/
private def curriedIsoOfUncurried
    {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
    (T : B ⥤ B ⥤ B) (W : A ⥤ A ⥤ A) (F : B ⥤ A)
    (e : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj W) :
    (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ A).obj F).obj F).obj W :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun Q ↦ e.app (P, Q)) (by
    intro Q Q' g
    simpa using e.hom.naturality (X := (P, Q)) (Y := (P, Q')) (𝟙 P, g))) (by
    intro P P' f
    apply NatTrans.ext
    funext Q
    simpa using e.hom.naturality (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q))

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Forget

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The underlying complex of `ℓ`-adic sheaves of a natively K-flat complex is K-flat. -/
theorem kFlat_forget_of_nativeIsKFlat
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hP : NativeIsKFlat k₀ l X P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  obtain ⟨-, -, -, -, -, -, ⟨κ, -, -⟩⟩ := native_ordinary_canonical_tensor_representatives l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  exact (HomotopyCategory.kFlat_quotient_obj_iff _).1
    (nativeOrdinaryKFlat_homotopy l _ κ _ (native_two_sided_kflat_forget k₀ l X P hP))

private instance tensorBifunctor_additive' : (nativeTensorBifunctor k₀ l X).Additive where
  map_add := by
    intro P Q f g
    apply NatTrans.ext
    funext N
    exact ((nativeTensorBifunctor k₀ l X).flip.obj N).map_add

private instance tensorBifunctor_obj_additive' (P : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorBifunctor k₀ l X).obj P).Additive :=
  (tensorIhomAdjunction k₀ l X P).left_adjoint_additive

set_option maxHeartbeats 800000 in
-- the instances on complexes of Weil sheaves and of `ℓ`-adic sheaves are expensive
/-- A complex of pro-étale Weil sheaves whose underlying complex of `ℓ`-adic sheaves is K-flat is
natively K-flat: forgetting the Weil structure is exact, reflects isomorphisms and commutes with
the total tensor product, so both native tensor tests may be checked after forgetting, where they
are the two halves of K-flatness. -/
theorem nativeIsKFlat_of_kFlat_forget (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).obj P)) :
    NativeIsKFlat k₀ l X P := by
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let W := ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let τ := curriedIsoOfUncurried (nativeTensorBifunctor k₀ l X) W F (tensorBifunctorForget k₀ l X)
  -- the forgotten total tensor product is the ordinary one, naturally
  let Γ (A B : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
      Fc.obj (CochainComplex.mapBifunctor A B (nativeTensorBifunctor k₀ l X)) ≅
        CochainComplex.mapBifunctor (Fc.obj A) (Fc.obj B) W :=
    asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) A B)
  have hΓ {A A' B B' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (f : A ⟶ A') (g : B ⟶ B') :
      Fc.map (HomologicalComplex.mapBifunctorMap f g (nativeTensorBifunctor k₀ l X) (.up ℤ)) ≫
        (Γ A' B').hom =
        (Γ A B).hom ≫ HomologicalComplex.mapBifunctorMap (Fc.map f) (Fc.map g) W (.up ℤ) :=
    HomologicalComplex.mapBifunctorComparison_naturality τ.hom (.up ℤ) f g
  -- the ordinary total tensor product is the monoidal one, with the factors swapped
  let O (A B : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :
      CochainComplex.mapBifunctor A B W ≅ B ⊗ A :=
    GenericOrdinaryTensor.ordinaryTotalIso A B
  have hO {A A' B B' : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ} (f : A ⟶ A') (g : B ⟶ B') :
      HomologicalComplex.mapBifunctorMap f g W (.up ℤ) ≫ (O A' B').hom =
        (O A B).hom ≫ (g ⊗ₘ f) :=
    GenericOrdinaryTensor.ordinaryTotalIso_naturality f g
  -- a native map of total tensor products is a quasi-isomorphism as soon as its ordinary
  -- counterpart is
  have key {A A' B B' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (f : A ⟶ A') (g : B ⟶ B')
      (h : QuasiIso (Fc.map g ⊗ₘ Fc.map f)) :
      QuasiIso (HomologicalComplex.mapBifunctorMap f g (nativeTensorBifunctor k₀ l X) (.up ℤ)) := by
    refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).1 ?_
    change QuasiIso (Fc.map (HomologicalComplex.mapBifunctorMap f g
      (nativeTensorBifunctor k₀ l X) (.up ℤ)))
    have hc : Fc.map (HomologicalComplex.mapBifunctorMap f g (nativeTensorBifunctor k₀ l X)
        (.up ℤ)) ≫ (Γ A' B' ≪≫ O _ _).hom = (Γ A B ≪≫ O _ _).hom ≫ (Fc.map g ⊗ₘ Fc.map f) := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [reassoc_of% (hΓ f g), hO]
    rw [← quasiIso_iff_comp_right _ (Γ A' B' ≪≫ O _ _).hom, hc, quasiIso_iff_comp_left]
    exact h
  have hq {A B : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (s : A ⟶ B) (hs : QuasiIso s) :
      HomologicalComplex.quasiIso _ (.up ℤ) (Fc.map s) := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology s F
  constructor
  · intro Q Q' s hs
    have h := key s (𝟙 P) (by
      rw [Fc.map_id, MonoidalCategory.id_tensorHom]
      exact (HomologicalComplex.mem_quasiIso_iff _).1 (hP.1 _ (hq s hs)))
    refine (quasiIso_iff_of_arrow_mk_iso _ _ ?_).2 h
    exact Arrow.isoMk
      (HomologicalComplex.mapBifunctorFlipIso Q P (nativeTensorBifunctor k₀ l X) (.up ℤ))
      (HomologicalComplex.mapBifunctorFlipIso Q' P (nativeTensorBifunctor k₀ l X) (.up ℤ))
      (HomologicalComplex.mapBifunctorFlipIso_hom_naturality s (𝟙 P)
        (nativeTensorBifunctor k₀ l X) (.up ℤ)).symm
  · intro Q Q' s hs
    have h := key (𝟙 P) s (by
      rw [Fc.map_id, MonoidalCategory.tensorHom_id]
      exact (HomologicalComplex.mem_quasiIso_iff _).1 (hP.2 _ (hq s hs)))
    refine (quasiIso_iff_of_arrow_mk_iso _ _ ?_).2 h
    exact Arrow.isoMk
      (HomologicalComplex.mapBifunctorFlipIso P Q (nativeTensorBifunctor k₀ l X) (.up ℤ))
      (HomologicalComplex.mapBifunctorFlipIso P Q' (nativeTensorBifunctor k₀ l X) (.up ℤ))
      (HomologicalComplex.mapBifunctorFlipIso_hom_naturality (𝟙 P) s
        (nativeTensorBifunctor k₀ l X) (.up ℤ)).symm

end Forget

variable
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of pro-étale Weil sheaves along an arbitrary morphism of `k₀`-schemes preserves
native K-flatness. -/
theorem nativeIsKFlat_upperStar_mapHomologicalComplex_obj
    (T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hT : NativeIsKFlat k₀ l Y T) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj T) := by
  have h₁ := kFlat_forget_of_nativeIsKFlat k₀ l Y T hT
  have h₂ := ProEtale.kFlat_adicUpperStar_mapHomologicalComplex_obj l
    (Scheme.Hom.geometricFiberMap p (comp_over p (Spec (CommRingCat.of k₀)))) h₁
  apply nativeIsKFlat_of_kFlat_forget
  refine ObjectProperty.prop_of_iso _
    (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) ?_) h₂
  intro i j _
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
