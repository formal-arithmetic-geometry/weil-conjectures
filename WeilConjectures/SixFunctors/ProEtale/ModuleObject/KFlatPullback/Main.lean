/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatOfTensorSingle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.Presentation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.Reduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.LiftedPresentation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.MapModTransfer
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.PreservesKFlatComplexesCriterion

/-!
# The pullback of an acyclic K-flat complex is K-flat
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The global sections over a w-contractible `S` of `g^* C ⊗ N` form an acyclic complex, for
`C` acyclic and K-flat, provided the global sections of `Λ_S` lift to some weakly étale
`Y`-scheme through which `g` factors. -/
theorem acyclic_modSections_tensorRight_upperStar_of_lift {S Y : Scheme.{u}} {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : S ≅ Spec R) {V : Scheme.{u}} (h : S ⟶ V) (v : V ⟶ Y) [WeaklyEtale v]
    (hΛ : Function.Surjective
      ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    (C : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hC : C.Acyclic) (hC' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C)
    (N : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    ((((h ≫ v)^*⟦Λ⟧ ⋙ tensorRight N ⋙ modSections (ProEt.mk (𝟙 S))).mapHomologicalComplex
      (.up ℤ)).obj C).Acyclic :=
  (HomologicalComplex.acyclic_mapHomologicalComplex_comp₃_iff _ _ _ C).2
    (acyclic_modSections_tensorRight_of_finitelyPresented hR e _ (fun _ _ T ↦
      (HomologicalComplex.acyclic_mapHomologicalComplex_comp₃_iff _ _ _ C).1
        (acyclic_modSections_tensorRight_cokernel Λ h v hR e hΛ C hC hC' T)) N)

/-- The braiding identifies tensoring on the left and on the right with `N`. -/
noncomputable def tensorRightIsoTensorLeft {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (N : C) : tensorRight N ≅ tensorLeft N :=
  NatIso.ofComponents (fun M ↦ β_ M N) (fun f ↦ BraidedCategory.braiding_naturality_left f N)

/-- **The pullback of an acyclic K-flat complex is K-flat**, given that the global sections of the
coefficient ring of a w-contractible affine scheme over `Y` lift to a weakly étale `Y`-scheme. -/
theorem kFlat_upperStar_of_acyclic_of_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hlift : ∀ (S : Scheme.{u}) (R : CommRingCat.{u}) [IsWContractibleRing R] (_ : S ≅ Spec R)
      (g : S ⟶ Y), ∃ (V : Scheme.{u}) (v : V ⟶ Y) (_ : WeaklyEtale v) (h : S ⟶ V), h ≫ v = g ∧
        Function.Surjective
          ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    (C : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hC : C.Acyclic) (hC' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj C) := by
  have hR (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj
        (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj C)).Acyclic := by
    refine acyclic_tensorRight_upperStar_of_forall Λ f C (fun S R _ e g N' ↦ ?_) N
    obtain ⟨V, v, _, h, rfl, hs⟩ := hlift S R e g
    exact acyclic_modSections_tensorRight_upperStar_of_lift Λ
      (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) e h v hs C hC hC' N'
  refine CochainComplex.kFlat_of_forall_acyclic_tensor_single _ hR fun N ↦ ?_
  exact (hR N).of_iso ((NatIso.mapHomologicalComplex (tensorRightIsoTensorLeft N) (.up ℤ)).app _)

/-- **`mapMod(f^*)` sends acyclic K-flat complexes to K-flat complexes**, given the lifting
property of global sections of the coefficient rings of `kFlat_upperStar_of_acyclic_of_lift`. -/
theorem kFlat_mapMod_upperStar_of_acyclic_of_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hlift : ∀ (S : Scheme.{u}) (R : CommRingCat.{u}) [IsWContractibleRing R] (_ : S ≅ Spec R)
      (g : S ⟶ Y), ∃ (V : Scheme.{u}) (v : V ⟶ Y) (_ : WeaklyEtale v) (h : S ⟶ V), h ≫ v = g ∧
        Function.Surjective
          ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    (C : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hC : C.Acyclic) (hC' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex (.up ℤ)).obj C) :=
  kFlat_mapMod_upperStar_of_kFlat_upperStar Λ f C
    (kFlat_upperStar_of_acyclic_of_lift Λ f hlift C hC hC')

/-- `mapMod(f^*)` preserves K-flat complexes, given the lifting property of global sections of
the coefficient rings of `kFlat_upperStar_of_acyclic_of_lift` and K-flat resolutions which
`mapMod(f^*)` sends to K-flat complexes (the reduction of
`CategoryTheory.Functor.preservesKFlatComplexes_of_exists_quasiIso`). -/
theorem preservesKFlatComplexes_mapMod_upperStar_of_lift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hlift : ∀ (S : Scheme.{u}) (R : CommRingCat.{u}) [IsWContractibleRing R] (_ : S ≅ Spec R)
      (g : S ⟶ Y), ∃ (V : Scheme.{u}) (v : V ⟶ Y) (_ : WeaklyEtale v) (h : S ⟶ V), h ≫ v = g ∧
        Function.Surjective
          ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)))
    (hres : ∀ (P : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ℤ), (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      ∃ (Q : CochainComplex _ ℤ) (π : Q ⟶ P), QuasiIso π ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q ∧
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
          ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex
            (.up ℤ)).obj Q)) :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).PreservesKFlatComplexes :=
  Functor.preservesKFlatComplexes_of_exists_quasiIso _ hres
    (fun K hK hK' ↦ kFlat_mapMod_upperStar_of_acyclic_of_lift Λ f hlift K hK hK')

end AlgebraicGeometry.ProEtale.CondensedRing
