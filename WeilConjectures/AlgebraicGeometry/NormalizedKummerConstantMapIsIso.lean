/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedKummerGlobalArrows
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars

/-! The normalized constant map is the primitive-root coefficient isomorphism.
(blueprint: new-pur-normalized-kummer-constant-map-isIso).
The private universal-property construction reuses the proof of the existing
RelativeKummerCoefficientNormalization module, specialized to arbitrary A. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private noncomputable def constantsScalarEquiv (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))) ⟶
      F.obj ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) ≃
    (((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A)) ⟶ F.obj) := by
  have hk (W : T.Etaleᵒᵖ) (x : F.obj.obj W) : N • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul A, hA, zero_smul]
  refine {
    toFun := fun f ↦ {
      app := fun W ↦ ModuleCat.ofHom
        (LinearMap.toSpanSingleton A _ ((f.app W).hom (ULift.up 1)))
      naturality := ?_ }
    invFun := fun f ↦ {
      app := fun W ↦
        (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).symm
          ((f.app W).hom (1 : A))
      naturality := ?_ }
    left_inv := ?_
    right_inv := ?_ }
  · rename_i f
    intro W V g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (show A from a) • (show F.obj.obj V from (f.app V).hom (ULift.up 1)) =
      (F.obj.map g).hom ((show A from a) •
        (show F.obj.obj W from (f.app W).hom (ULift.up 1)))
    rw [map_smul]
    congr 1
    exact (ConcreteCategory.congr_hom (f.naturality g) (ULift.up 1))
  · rename_i f
    intro W V g
    apply (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj V)) (hk V)).injective
    change _ = (F.obj.map g).hom _
    change (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj V)) (hk V))
      ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj V)) (hk V)).symm
        ((f.app V).hom (1 : A))) = _
    rw [Equiv.apply_symm_apply]
    change (f.app V).hom (1 : A) = (F.obj.map g).hom
      ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W))
        ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).symm
          ((f.app W).hom (1 : A))))
    rw [Equiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom (f.naturality g) (1 : A)
  · intro f
    apply NatTrans.ext
    funext W
    apply (AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).injective
    rw [Equiv.apply_symm_apply]
    change (1 : A) • (show F.obj.obj W from (f.app W).hom (ULift.up 1)) = _
    exact one_smul A _
  · intro f
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (1 : A) • (show F.obj.obj W from
      ((AddCommGrpCat.zmodHomEquiv (AddCommGrpCat.of (F.obj.obj W)) (hk W)).symm
        ((f.app W).hom (1 : A))).hom (ULift.up 1)) = _
    rw [one_smul]
    exact (AddCommGrpCat.zmodHomEquiv
      (AddCommGrpCat.of (F.obj.obj W)) (hk W)).apply_symm_apply _


private noncomputable def normalizedLineHomEquiv (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ F) ≃
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A) ⟶ F) :=
  (lineHomEquiv T N A hA F).trans
    ((Iso.homCongr ρ.symm (Iso.refl _)).trans
      (((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).trans ((constantsScalarEquiv T N A hA F).trans
          ((sheafificationAdjunction T.smallEtaleTopology
            (ModuleCat.{u + 1} A)).homEquiv _ _).symm)))

private theorem normalizedLineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ F) (W : T.Etaleᵒᵖ) (a : A) :
    (normalizedLineHomEquiv T N A hA ρ F f).hom.app W
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W a) =
      a • f.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1
        (ρ.hom.hom.app W ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1)))) := by
  have he := ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).apply_symm_apply
      ((constantsScalarEquiv T N A hA F)
        (((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
          _ _) (ρ.hom ≫ lineHomEquiv T N A hA F f)))
  have hw := ConcreteCategory.congr_hom (congr_app he W) a
  change (normalizedLineHomEquiv T N A hA ρ F f).hom.app W
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (ModuleCat.of A A))).app W a) = _ at hw
  rw [hw]
  change a • (show F.obj.obj W from (lineHomEquiv T N A hA F f).hom.app W _) = _
  rw [lineHomEquiv_generator]
  rfl


private theorem normalizedLineHomEquiv_comp (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : finiteEtaleTateLine T N A hA ⟶ F) (g : F ⟶ G) :
    normalizedLineHomEquiv T N A hA ρ G (f ≫ g) =
      normalizedLineHomEquiv T N A hA ρ F f ≫ g := by
  apply ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (normalizedLineHomEquiv T N A hA ρ G (f ≫ g)).hom.app W
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app W a) =
    g.hom.app W ((normalizedLineHomEquiv T N A hA ρ F f).hom.app W
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app W a))
  rw [normalizedLineHomEquiv_generator, normalizedLineHomEquiv_generator, map_smul]
  rfl

private noncomputable def normalizedLineIso (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N) :
    (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ≅
      finiteEtaleTateLine T N A hA where
  hom := normalizedLineHomEquiv T N A hA ρ _ (𝟙 _)
  inv := (normalizedLineHomEquiv T N A hA ρ _).symm (𝟙 _)
  hom_inv_id := by
    rw [← normalizedLineHomEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (normalizedLineHomEquiv T N A hA ρ _).injective
    rw [normalizedLineHomEquiv_comp, Equiv.apply_symm_apply, Category.id_comp]

private theorem normalizedLineIso_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (ρ : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅ T.rootsOfUnitySheaf N)
    (W : T.Etaleᵒᵖ) (a : A) :
    (normalizedLineIso T N A hA ρ).hom.hom.app W
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of A A))).app W a) =
      finiteEtaleTateOneGenerator A N T hA W a
        (ρ.hom.hom.app W ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))).app W (ULift.up 1))) := by
  change (normalizedLineHomEquiv T N A hA ρ _ (𝟙 _)).hom.app W _ = _
  rw [normalizedLineHomEquiv_generator]
  change a • finiteEtaleTateOneGenerator A N T hA W 1 _ = _
  exact (finiteEtaleGenerator_smul T N A hA W a _).symm



end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The chosen primitive root trivializes the specified normalized constant map.
Source: blueprint latest, prop-pur-gm-relative-kummer.proof.md, Step 2, opening
primitive-root trivialization and constant normalization.
(blueprint: new-pur-normalized-kummer-constant-map-isIso).

Proof: scalar extension and sheafification give the root-line universal property.
A primitive root identifies the root sheaf with the constant Z/m sheaf. Maps from
the latter into the underlying group of an A-module sheaf correspond to maps
from the constant A sheaf, by evaluation at one and A-linearity. Yoneda gives
an isomorphism sending a to zeta tensor a. Evaluate its constant-sheaf adjoint
at one, using the canonical global-sections/terminal-sections comparison. This
is precisely the section transposed in normalizedKummerConstantMap, so the
specified map equals that isomorphism. -/
theorem normalizedKummerConstantMap_isIso
    (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {k : Type u} [Field k] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    (T : Scheme.{u}) (p : T ⟶ Spec (.of k)) :
    IsIso (normalizedKummerConstantMap A m hm hA hζ T p) := by
  let : NeZero m := ⟨ne_of_gt hm⟩
  let ρ := T.constantZModIsoRootsOfUnitySheaf m p hζ
  let e : kummerExchangeConstant A T ≅ Scheme.finiteEtaleTateLine T m A hA :=
    Scheme.normalizedLineIso T m A hA ρ
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  let adj : constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⊣
      Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
    constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adjT := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A) hT
  let γ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      (sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (Scheme.Etale.mk (𝟙 T))) :=
    Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A) hT
  have hΓ (f : kummerExchangeConstant A T ⟶ Scheme.finiteEtaleTateLine T m A hA) :
      adj.homEquiv _ _ f ≫ γ.hom.app _ = adjT.homEquiv _ _ f := by
    rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Category.assoc,
      γ.hom.naturality f, ← Category.assoc]
    exact congrArg (fun g => g ≫ _) (Adjunction.unit_rightAdjointUniq_hom_app adj adjT _)
  have he : e.hom = normalizedKummerConstantMap A m hm hA hζ T p := by
    rw [normalizedKummerConstantMap]
    apply (adj.homEquiv (ModuleCat.of A A)
      (Scheme.finiteEtaleTateLine T m A hA)).injective
    rw [Equiv.apply_symm_apply]
    have heΓ : adj.homEquiv _ _ e.hom =
        adjT.homEquiv _ _ e.hom ≫ γ.inv.app (Scheme.finiteEtaleTateLine T m A hA) := by
      rw [← hΓ, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [heΓ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply_one]
    change γ.inv.app (Scheme.finiteEtaleTateLine T m A hA) _ =
      γ.inv.app (Scheme.finiteEtaleTateLine T m A hA) _
    congr 1
    change e.hom.hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app _ (1 : A)) =
      Sheaf.H.equiv₀ ((RawModuleScalarComparison.forget A T).obj
        (Scheme.finiteEtaleTateLine T m A hA)) hT
        (relativeKummerConstant A m hm hA hζ T p 1)
    rw [relativeKummerConstant, AddEquiv.apply_symm_apply]
    exact Scheme.normalizedLineIso_generator T m A hA ρ _ 1
  exact he ▸ inferInstance

end AlgebraicGeometry.Etale
