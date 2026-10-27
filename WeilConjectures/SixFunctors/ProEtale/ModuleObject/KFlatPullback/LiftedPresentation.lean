/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.FullOnBiproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.PulledBackModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.UpperStarFull

/-!
# Finitely presented modules pulled back through a weakly étale scheme

Let `h : S ⟶ V` and `v : V ⟶ Y` be morphisms of schemes with `v` weakly étale, `S` the spectrum
of a w-contractible ring, such that the restriction of global sections of `Λ_V` along `h` is
surjective. Every morphism `T : Λ_S^m ⟶ Λ_S^n` of free module objects is then the pullback of a
morphism `Λ_V^m ⟶ Λ_V^n`, so its cokernel is pulled back from `V`. Hence, for every acyclic K-flat
complex `C` over `Λ_Y`, the global sections of `(h ≫ v)^* C ⊗ coker T` form an acyclic complex
(`AlgebraicGeometry.ProEtale.CondensedRing.acyclic_modSections_tensorRight_cokernel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {S V Y : Scheme.{u}} (h : S ⟶ V)

/-- The pullback of a finite free module object is free: `∐ Λ_S ≅ h^* (⨁ Λ_V)`. -/
noncomputable def coproductUnitIsoUpperStarBiproduct (k : ℕ) :
    (∐ fun _ : Fin k ↦ 𝟙_ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))) ≅
      (h)^*⟦Λ⟧.obj (⨁ fun _ : Fin k ↦
        𝟙_ (Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :=
  Sigma.mapIso (fun _ ↦ Functor.Monoidal.εIso (h)^*⟦Λ⟧) ≪≫
    (PreservesCoproduct.iso (h)^*⟦Λ⟧ _).symm ≪≫
    (h)^*⟦Λ⟧.mapIso (biproduct.isoCoproduct _).symm

/-- If the restriction of global sections of `Λ_V` along `h` is surjective, the cokernel of a
morphism of finite free module objects over `Λ_S` is the pullback of the cokernel of a morphism of
finite free module objects over `Λ_V`. -/
lemma exists_cokernel_iso_upperStar
    (hΛ : Function.Surjective
      ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    {m n : ℕ}
    (T : (∐ fun _ : Fin m ↦ 𝟙_ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
      ⟶ ∐ fun _ : Fin n ↦ 𝟙_ _) :
    ∃ (T' : (⨁ fun _ : Fin m ↦
        𝟙_ (Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) ⟶
          ⨁ fun _ : Fin n ↦ 𝟙_ _),
      Nonempty (cokernel T ≅ (h)^*⟦Λ⟧.obj (cokernel T')) := by
  obtain ⟨T', hT'⟩ := (h)^*⟦Λ⟧.exists_map_eq_biproduct (J := Fin m) (K := Fin n) _ _
    (exists_upperStar_map_eq_of_surjective h Λ hΛ)
    ((coproductUnitIsoUpperStarBiproduct Λ h m).inv ≫ T ≫
      (coproductUnitIsoUpperStarBiproduct Λ h n).hom)
  refine ⟨T', ⟨?_⟩⟩
  refine ?_ ≪≫ (PreservesCokernel.iso (h)^*⟦Λ⟧ T').symm
  rw [hT']
  exact cokernel.mapIso _ _ (coproductUnitIsoUpperStarBiproduct Λ h m)
    (coproductUnitIsoUpperStarBiproduct Λ h n) (by simp)

/-- **Tensoring with finitely presented modules.** Let `v : V ⟶ Y` be weakly étale, `h : S ⟶ V`
with `S ≅ Spec R`, `R` w-contractible, such that the restriction of global sections of `Λ_V` along
`h` is surjective. For `C` acyclic and K-flat over `Λ_Y` and every morphism `T` of finite free
module objects over `Λ_S`, the global sections of `(h ≫ v)^* C ⊗ coker T` form an acyclic
complex. -/
theorem acyclic_modSections_tensorRight_cokernel (v : V ⟶ Y) [WeaklyEtale v]
    {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : S ≅ Spec R)
    (hΛ : Function.Surjective
      ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    (C : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hC : C.Acyclic) (hC' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) {m n : ℕ}
    (T : (∐ fun _ : Fin m ↦ 𝟙_ (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
      ⟶ ∐ fun _ : Fin n ↦ 𝟙_ _) :
    ((((h ≫ v)^*⟦Λ⟧ ⋙ tensorRight (cokernel T) ⋙
      modSections (ProEt.mk (𝟙 S))).mapHomologicalComplex (.up ℤ)).obj C).Acyclic := by
  obtain ⟨T', ⟨eT⟩⟩ := exists_cokernel_iso_upperStar Λ h hΛ T
  let e₁ : tensorRight (cokernel T) ≅ tensorRight ((h)^*⟦Λ⟧.obj (cokernel T')) :=
    NatIso.ofComponents (fun M ↦ whiskerLeftIso M eT) (fun f ↦ (whisker_exchange f eT.hom).symm)
  exact (acyclic_modSections_tensorRight_upperStar_comp Λ h v hR e C hC hC'
    (cokernel T')).of_iso ((NatIso.mapHomologicalComplex
      (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight e₁ _)).symm (.up ℤ)).app C)

end AlgebraicGeometry.ProEtale.CondensedRing
