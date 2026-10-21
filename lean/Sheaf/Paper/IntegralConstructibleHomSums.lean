/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness
import WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Shifted Hom from integral constructible complexes and countable sums

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12
(blueprint: lem-weil-pbc-integral-constructible-hom-sums).

We use the completed coefficient presentation of the integral category. The scalar
ring is its recorded `ULift` of the valuation ring, canonically ring-isomorphic to
that valuation ring. A colimit cofan supplies the ambient derived coproduct and its
coprojections without choosing a second coproduct object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


set_option backward.isDefEq.respectTransparency false in
open Opposite in
private def integralUnitSectionsEquiv
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : pbcModules X (pbcAdicCompletion X d)) :
    (SheafOfModules.unit
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (pbcAdicCompletion X d)) ⟶ M) ≃+
      (adicGlobalSections X d).obj M where
  toFun f := f.val.app (op (⊤_ X.ProEt))
    (1 : (pbcAdicCompletion X d).obj.obj (op (⊤_ X.ProEt)))
  invFun x := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun U ↦ M.val.map (terminal.from U.unop).op x) (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      have h : (terminal.from U.unop).op ≫ f = (terminal.from V.unop).op := by
        apply Quiver.Hom.unop_inj
        exact terminal.hom_ext _ _
      rw [h]))
  left_inv f := by
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    simp only [Equiv.apply_symm_apply]
    exact (PresheafOfModules.sections_property (M.unitHomEquiv f)
      (terminal.from U.unop).op)
  right_inv x := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm _)).val _ = x
    simp only [Equiv.apply_symm_apply]
    have h : (terminal.from (⊤_ X.ProEt)).op = 𝟙 (op (⊤_ X.ProEt)) := by
      apply Quiver.Hom.unop_inj
      exact terminal.hom_ext _ _
    change M.val.map (terminal.from (⊤_ X.ProEt)).op x = x
    rw [h]
    change M.val.presheaf.map (𝟙 _) x = x
    rw [M.val.presheaf.map_id]
    rfl
  map_add' f g := by
    rfl

set_option backward.isDefEq.respectTransparency false in
open Opposite in
private def integralSectionsIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    adicGlobalSections X d ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat ≅
      preadditiveCoyoneda.obj (op (SheafOfModules.unit
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (pbcAdicCompletion X d)))) :=
  NatIso.ofComponents (fun M ↦ (integralUnitSectionsEquiv X d M).symm.toAddCommGrpIso)
    (by
      intro M N f
      ext x
      change (integralUnitSectionsEquiv X d N).symm
          ((adicGlobalSections X d).map f x) =
        (integralUnitSectionsEquiv X d M).symm x ≫ f
      apply (integralUnitSectionsEquiv X d N).injective
      rw [AddEquiv.apply_symm_apply]
      change f.val.app _ x = f.val.app _
        ((integralUnitSectionsEquiv X d M) ((integralUnitSectionsEquiv X d M).symm x))
      rw [AddEquiv.apply_symm_apply])

set_option backward.isDefEq.respectTransparency false in
open Opposite SheafOfModules in
private theorem integralRHomZeroIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived X d) :
    Nonempty (adicGlobalRHom X d K ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0 ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⋙
        AddCommGrpCat.uliftFunctor.{u + 2, u + 1} ≅
      preadditiveCoyoneda.obj (op K)) := by
  classical
  let C := pbcModules X (pbcAdicCompletion X d)
  let R := pbcAdicCompletion X d
  let Γ := preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
  let : IsGrothendieckAbelian.{u + 1} C :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology X) R).1
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesColimits U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} A
  have : PreservesFiniteColimits U := inferInstance
  let H := (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
    (ProEt.topology X) R)).obj (op K)
  let σ : adicDerivedGlobalSections X d ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0 ⋙ U ≅
      Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0 :=
    Functor.isoWhiskerLeft (adicDerivedGlobalSections X d)
      (Functor.mapDerivedCategoryHomologyFunctorIso
        (C := ModuleCat.{u + 1} A) (D := AddCommGrpCat.{u + 1}) U 0) ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (D := ModuleCat.{u + 1} A) (E := AddCommGrpCat.{u + 1})
        (adicGlobalSections X d) U).symm
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0) ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso (integralSectionsIso X d))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
  obtain ⟨e, he⟩ := rhom_global_sectionsOfUniverses.{u + 1, u, u + 1, u + 2}
    (ProEt.topology X) R
  let L := AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let τ : H ⋙
      ringedSiteZerothHypercohomologyOfUniverses.{u + 1, u, u + 1, u + 2}
        (ProEt.topology X) R ⋙ L ≅
      preadditiveCoyoneda.obj (op K) :=
    NatIso.ofComponents (fun N ↦ (AddEquiv.ulift.trans (e (op K, N))).toAddCommGrpIso) (by
      intro M N f
      ext x
      change e (op K, N)
          ((ringedSiteZerothHypercohomologyOfUniverses.{u + 1, u, u + 1, u + 2}
            (ProEt.topology X) R).map
              ((derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
                (ProEt.topology X) R).map (𝟙 (op K), f)) x.down) =
        e (op K, M) x.down ≫ f
      simpa only [unop_id, Category.id_comp] using
        he (op K, M) (op K, N) (𝟙 (op K), f) x.down)
  exact ⟨Functor.isoWhiskerRight (Functor.isoWhiskerLeft H σ) L ≪≫ τ⟩

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The canonical map from the direct sum of shifted Hom modules is bijective,
and hence is an isomorphism of modules over the integral coefficient ring.
Its component at `i` is postcomposition with the shifted coprojection `s.inj i`.
The countable family may be empty and its common lower bound may be any integer.
The source belongs to the recorded bounded constructible complete category, using
the canonical continuous-coefficient/completed-coefficient identification.

Source: Bhatt--Scholze, Lemma 6.8.12
(blueprint: lem-weil-pbc-integral-constructible-hom-sums).

Proof:
1. Shift the family and its colimiting cofan by q. Its common lower bound becomes n-q.
   Apply integralConstructible_boundedBelow_compactness to this shifted family.
2. Apply derivedModuleHomology_coproduct in degree zero, then forget scalars and lift
   the resulting groups to the universe of derived morphisms. These functors preserve
   the colimiting cofan.
3. Evaluation on the terminal object identifies ordinary scalar-valued sections,
   after forgetting scalars, with maps from the unit sheaf. Exactness of the forgetful
   functor gives the same natural identification after right derivation and homology.
   Apply rhom_global_sectionsOfUniverses to identify these groups naturally with
   Hom(K,N), for every shifted target N.
4. Transport the colimiting cofan through this natural identification. Naturality
   identifies each leg with postcomposition by the shifted coprojection. The forgetful
   functor from modules reflects colimits, so the module-valued Hom cofan is colimiting.
   Its comparison from the concrete module direct sum is precisely DirectSum.toModule
   in the statement and is therefore an isomorphism. The same proof includes the empty
   family and every integer q. -/
theorem integralConstructible_hom_sums
    (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hdim : ∃ N : ℕ, topologicalKrullDim X ≤ (N : WithBot ℕ∞))
    (hℓ : ∀ x : X, IsUnit (ℓ : X.presheaf.stalk x))
    (K : PbcIntegralCategory ℓ E X hdim hℓ)
    (I : Type (u + 1)) [Countable I]
    (M : I → PbcCompletedDerived X (pbcIntegralDatum ℓ E))
    (_hM : ∃ n : ℤ, ∀ i : I, DerivedCategory.IsGE (M i) n)
    (q : ℤ) (s : Cofan M) (_hs : IsColimit s) :
    Function.Bijective
      (DirectSum.toModule (PbcIntegralRing ℓ E) I (K.obj ⟶ s.pt⟦q⟧)
        (fun i : I ↦ Linear.rightComp (PbcIntegralRing ℓ E) K.obj
          ((shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum ℓ E)) q).map
            (s.inj i)))) := by
  classical
  let A := PbcIntegralRing ℓ E
  let d := pbcIntegralDatum ℓ E
  let D := PbcCompletedDerived X d
  let N : I → D := fun i ↦ (M i)⟦q⟧
  let s' : Cofan N := Cofan.mk (s.pt⟦q⟧)
    (fun i ↦ (shiftFunctor D q).map (s.inj i))
  have hs' : IsColimit s' :=
    (isColimitMapCoconeCofanMkEquiv (shiftFunctor D q) M s.inj).1
      (isColimitOfPreserves (shiftFunctor D q) _hs)
  obtain ⟨n, hn⟩ := _hM
  have hN : ∃ b : ℤ, ∀ i, (N i).IsGE b := by
    refine ⟨n - q, fun i ↦ ?_⟩
    have : (M i).IsGE n := hn i
    exact DerivedCategory.TStructure.t.isGE_shift (M i) n q (n - q) (by omega)
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let G := adicGlobalRHom X d K.obj
  let Q := DerivedCategory.Q (C := ModuleCat.{u + 1} A)
  let L := fun i ↦ Q.objPreimage (G.obj (N i))
  let e := fun i ↦ Q.objObjPreimageIso (G.obj (N i))
  let t : Cofan (fun i ↦ G.obj (N i)) := Cofan.mk (Q.obj (∐ L))
    (fun i ↦ (e i).inv ≫ Q.map (Sigma.ι L i))
  have ht : IsColimit t := by
    let a : Discrete.functor (fun i ↦ Q.obj (L i)) ≅
        Discrete.functor (fun i ↦ G.obj (N i)) := Discrete.natIso (fun i ↦ e i.as)
    apply (IsColimit.precomposeHomEquiv a t).1
    apply IsColimit.ofIsoColimit (CategoryTheory.derivedModuleDirectSums A I L).some
    refine Cocone.ext (Iso.refl _) ?_
    intro i
    simp [a, t]
    rfl
  let cG := Cofan.mk (G.obj s'.pt) (fun i ↦ G.map (s'.inj i))
  have : IsIso (ht.desc cG) :=
    integralConstructible_boundedBelow_compactness X ℓ E hdim hℓ K I N hN s' hs' t ht
  have hcG : IsColimit cG :=
    ((ht.nonempty_isColimit_iff_isIso_desc).mpr inferInstance).some
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0
  have hcH : IsColimit (Cofan.mk (H.obj (G.obj s'.pt))
      (fun i ↦ H.map (G.map (s'.inj i)))) :=
    (AlgebraicGeometry.derivedModuleHomology_coproduct A 0 I
      (fun i ↦ G.obj (N i)) (G.obj s'.pt) (fun i ↦ G.map (s'.inj i)) hcG).some
  let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⋙
    AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  have hcU : IsColimit (Cofan.mk (U.obj (H.obj (G.obj s'.pt)))
      (fun i ↦ U.map (H.map (G.map (s'.inj i))))) :=
    (isColimitMapCoconeCofanMkEquiv U _ _).1 (isColimitOfPreserves U hcH)
  let V := forget₂ (ModuleCat.{u + 2} A) AddCommGrpCat.{u + 2}
  let B : I → ModuleCat.{u + 2} A := fun i ↦ ModuleCat.of A (K.obj ⟶ N i)
  let c : Cofan B := Cofan.mk (ModuleCat.of A (K.obj ⟶ s'.pt))
    (fun i ↦ ModuleCat.ofHom (Linear.rightComp A K.obj (s'.inj i)))
  obtain ⟨ε⟩ := integralRHomZeroIso X d K.obj
  let b : Discrete.functor (fun i ↦ U.obj (H.obj (G.obj (N i)))) ≅
      Discrete.functor (fun i ↦ V.obj (B i)) :=
    Discrete.natIso (fun i ↦ ε.app (N i.as))
  have hcAdd : IsColimit (Cofan.mk (V.obj c.pt) (fun i ↦ V.map (c.inj i))) := by
    apply (IsColimit.precomposeHomEquiv b _).1
    apply IsColimit.ofIsoColimit hcU
    refine Cocone.ext (ε.app s'.pt) ?_
    intro i
    exact ε.hom.naturality (s'.inj i.as)
  have hc : IsColimit c := isColimitOfReflects V
    ((isColimitMapCoconeCofanMkEquiv V B c.inj).2 hcAdd)
  let hB := ModuleCat.coproductCoconeIsColimit.{u + 1, u + 1, u + 2} B
  have : IsIso (hB.desc c) := (hB.nonempty_isColimit_iff_isIso_desc).mp ⟨hc⟩
  exact (ConcreteCategory.isIso_iff_bijective (hB.desc c)).mp inferInstance

end AlgebraicGeometry.Scheme
