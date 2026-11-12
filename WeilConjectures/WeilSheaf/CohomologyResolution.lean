/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraStr
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSectionsComm
public import WeilConjectures.WeilSheaf.CohomologyProEtale

/-!
# Weil cohomology and its Frobenius from an injective resolution

Let `F` be a Weil sheaf on a `k₀`-scheme `Y` of finite type, with geometric fiber `Ȳ` and
geometric Galois Frobenius `Fr : Ȳ ≅ Ȳ`, and let `I` be an injective resolution of `F` by
pro-étale Weil sheaves. The cohomology `Hʳ(Y ⊗ k̄, F)` is the `r`-th cohomology of the complex
`Γ(Ȳ, I)` of global sections, and its geometric Frobenius is induced by the Frobenius
`Γ(Ȳ, Iⁿ) ≅ Γ(Ȳ, Fr^* Iⁿ) --Γ(φ)--> Γ(Ȳ, Iⁿ)` of the terms of `I`
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_resolution`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]


attribute [local instance 2000] CategoryWithHomology.hasHomology

namespace ProEtaleWeilSheaf

variable (k₀ l) (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]

/-- The global sections of a pro-étale Weil sheaf, as a functor to `ℚ̄_ℓ`-modules. -/
noncomputable abbrev globalSectionsWeilFunctor :
    ProEtaleWeilSheaf k₀ l Y ⥤ WeilCoefficients.{u} l :=
  IsoAlgebra.forget _ ⋙ AdicSheaf.forget _ ⋙ Sheaf.Γ _ _

/-- The Frobenius `Γ(Ȳ, M) ≅ Γ(Ȳ, Fr^* M) --Γ(φ)--> Γ(Ȳ, M)` of the global sections of a
pro-étale Weil sheaf `(M, φ)`. -/
@[simps]
noncomputable def globalSectionsFrobeniusNatTrans :
    globalSectionsWeilFunctor k₀ l Y ⟶ globalSectionsWeilFunctor k₀ l Y where
  app X := (globalSectionsLowerStarIso _
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app X.carrier.X ≫
    (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map X.str.hom)
  naturality X X' φ := by
    have h₁ := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality φ.hom.f.hom
    have h₂ := φ.hom.h
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ ⊢
    erw [reassoc_of% h₁]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2
    exact congrArg Mod.Hom.hom h₂

end ProEtaleWeilSheaf

namespace ProEtale

/-- The underlying morphism of sheaves of the Frobenius exchange isomorphism. -/
lemma adicSheafForget_map_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_app {k : Type u}
    [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)}
    (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) (M : AdicSheaf l f.geometricFiber) :
    ((adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) _ _).hom.app M.X ≫
        (lowerStarCongr (WeilCoefficients.{u} l)
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)).hom.app M.X ≫
          (lowerStarComp (WeilCoefficients.{u} l) _ _).inv.app M.X :=
  rfl

/-- Global sections identify the Frobenius transported through a commuting square of adic
pushforwards with the Frobenius on the source. -/
lemma adicFrobeniusNatTrans_eq_of_comm {Z W : Scheme.{u}} (g : Z ⟶ W)
    (hW : W ⟶ W) (hZ : Z ⟶ Z) (comm : hZ ≫ g = g ≫ hW)
    (e : adicLowerStar l g ⋙ adicLowerStar l hW ≅
      adicLowerStar l hZ ⋙ adicLowerStar l g)
    (he : ∀ M : AdicSheaf l Z, (e.hom.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) g hW).hom.app M.X ≫
        (lowerStarCongr (WeilCoefficients.{u} l) comm.symm).hom.app M.X ≫
          (lowerStarComp (WeilCoefficients.{u} l) hZ g).inv.app M.X)
    (τ : IsoAlgebra.forget (adicLowerStar l hZ) ⋙ AdicSheaf.forget Z ⋙ Sheaf.Γ _ _ ⟶
      IsoAlgebra.forget (adicLowerStar l hZ) ⋙ AdicSheaf.forget Z ⋙ Sheaf.Γ _ _)
    (hτ : ∀ X, τ.app X = (globalSectionsLowerStarIso _ hZ).inv.app X.carrier.X ≫
      (Sheaf.Γ _ _).map X.str.hom.hom) :
    IsoAlgebra.frobeniusNatTrans e (AdicSheaf.forget W ⋙ Sheaf.Γ _ _)
      (AdicSheaf.forget Z ⋙ Sheaf.Γ _ _)
      (Functor.isoWhiskerLeft (AdicSheaf.forget Z) (globalSectionsLowerStarIso _ g))
      (Functor.whiskerLeft (AdicSheaf.forget W) (globalSectionsLowerStarIso _ hW).inv) = τ := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  rw [hτ]
  change (globalSectionsLowerStarIso _ g).inv.app X.carrier.X ≫
    (globalSectionsLowerStarIso _ hW).inv.app ((adicLowerStar l g).obj X.carrier).X ≫
      (Sheaf.Γ _ _).map ((e.hom.app X.carrier).hom ≫
        ((adicLowerStar l g).map X.str.hom).hom) ≫
      (globalSectionsLowerStarIso _ g).hom.app X.carrier.X = _
  rw [he, adicLowerStar_map_hom, Category.assoc, Category.assoc]
  exact globalSectionsLowerStarIso_comm_map (WeilCoefficients.{u} l) g g hW hZ comm
    X.carrier.X X.str.hom.hom

end ProEtale

namespace WeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

set_option profiler true in
set_option maxHeartbeats 1600000 in
-- the kernel unfolds the pushforward of sheaves of modules to its underlying sheaf
omit [Fact (ringChar k₀ ≠ l)] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
variable (k₀ l Y) in
/-- The Frobenius of the global sections of the terms of a resolution, in the form of
`CategoryTheory.Endofunctor.IsoAlgebra.frobeniusNatTrans`, is
`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans`. -/
lemma frobeniusNatTrans_eq_globalSectionsFrobeniusNatTrans :
    IsoAlgebra.frobeniusNatTrans (adicLowerStarGeometricFiberMapCompFrobeniusIso l
        (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (Functor.isoWhiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
          (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))))
      (Functor.whiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv) =
      ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans k₀ l Y := by
  exact adicFrobeniusNatTrans_eq_of_comm
    (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
      (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _).symm _
    (fun M ↦ adicSheafForget_map_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_app
      (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _) M)
    (ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans k₀ l Y) (fun _ ↦ rfl)


set_option profiler true in
-- the kernel unfolds the pushforward of sheaves of modules to its underlying sheaf
/-- **Weil cohomology from an injective resolution.** Let `I` be an injective resolution of a
Weil sheaf `F` by pro-étale Weil sheaves. Then `Hʳ(Y ⊗ k̄, F)` is the `r`-th cohomology of the
complex `Γ(Ȳ, I)`, and its geometric Frobenius is induced by the Frobenius
`Γ(Ȳ, Iⁿ) ≅ Γ(Ȳ, Fr^* Iⁿ) --Γ(φ)--> Γ(Ȳ, Iⁿ)` of the terms of `I`. -/
theorem exists_linearEquiv_cohomology_resolution (F : WeilSheaf k₀ l Y)
    (I : InjectiveResolution F.obj) (r : ℕ) :
    ∃ Θ : (F.cohomology r).carrier ≃ₗ[PadicAlgCl l] (WeilCoefficients.toModuleCat l).obj
        ((I.cocomplex.sc r).map (ProEtaleWeilSheaf.globalSectionsWeilFunctor k₀ l Y)).homology,
      ∀ x, Θ ((F.cohomology r).frobenius x) = ((WeilCoefficients.toModuleCat l).map
        (ShortComplex.homologyMap ((I.cocomplex.sc r).mapNatTrans
          (ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans k₀ l Y)))).hom (Θ x) := by
  have h := IsoAlgebra.frobenius_globalSectionsHomologyIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l
        (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (Functor.isoWhiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
          (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))))
      (Functor.whiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv)
      I r
  rw [frobeniusNatTrans_eq_globalSectionsFrobeniusNatTrans] at h
  refine ⟨WeilCoefficients.linearEquivOfIso (IsoAlgebra.globalSectionsHomologyIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l
        (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (Functor.isoWhiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
          (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _)))) I r), fun x ↦ ?_⟩
  exact congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom x) h
end WeilSheaf

end AlgebraicGeometry
