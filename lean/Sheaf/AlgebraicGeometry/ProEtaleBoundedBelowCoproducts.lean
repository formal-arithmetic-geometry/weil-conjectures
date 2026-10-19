/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# Pro-etale direct image and uniformly bounded-below coproducts

Source: Stacks Project, Tag 09A3, relative rational-algebra module version
(blueprint: lem-weil-pbc-proetale-bounded-below-coproducts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Match the site and section universes before applying the small-site theorem.
private noncomputable def moduleModelEquiv (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ≌
      SheafOfModules.{u + 1}
        (((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj R) := by
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).symm.functor.IsContinuous
      (proEtaleModelTopology T) (ProEt.topology T) :=
    inferInstanceAs ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsContinuous _ _)
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).symm.inverse.IsContinuous
      (ProEt.topology T) (proEtaleModelTopology T) :=
    proEtaleModelUp_isContinuous T
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := T.ProEt)).symm
    (𝟙 _) (𝟙 _) (by
      ext V x
      change (R.obj.map (𝟙 V)) x = x
      simp) (by
      ext V x
      change (R.obj.map (𝟙 (Opposite.op (ULift.down V.unop)))) x = x
      simp)

private theorem moduleEnoughInjectives (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    EnoughInjectives (proEtaleRingModules T R) := by
  let R' := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let S := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj R'
  have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} S) :=
    SheafOfModules.isGrothendieckAbelian S
  exact EnoughInjectives.of_equivalence (moduleModelEquiv T R').functor

-- A bounded-below complex of acyclic objects computes the unbounded derived functor.
private theorem unit_of_acyclic {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (N : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := by
  obtain ⟨J, f, hf, hJ, hJN⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K N
  have : QuasiIso f := hf
  have : J.IsStrictlyGE N := hJN
  have : ∀ n, Injective (J.X n) := hJ
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J N
  have : QuasiIso ((F.mapHomologicalComplex _).map f) :=
    F.quasiIso_map_of_rightAcyclic f N hK (fun n ↦ F.rightAcyclic_of_injective _)
  have hn := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map f)
  dsimp only [Functor.comp_map] at hn
  have hi : IsIso (F.rightDerivedFunctor.map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f))) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (.up ℤ)).map f)) := by
      change IsIso ((HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).map f)
      exact NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) f |>.2 inferInstance
    infer_instance
  have hi' : IsIso ((F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f)) := by
    change IsIso ((HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh).map
      ((F.mapHomologicalComplex _).map f))
    exact NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) _ |>.2 inferInstance
  dsimp only [Functor.comp_map] at hi'
  have : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      F.rightDerivedFunctor.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f))) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f)))

-- Transport a coproduct through the natural comparison from termwise direct image.
private theorem uniformCoproduct
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) [F.Additive] (I : Type (u + 1))
    [HasCoproducts.{u + 1} C] [HasCoproducts.{u + 1} D]
    [PreservesColimitsOfShape (Discrete I) F]
    (E : I → CochainComplex C ℤ)
    [∀ i, (E i).IsKInjective]
    (hunit : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ E)))) :
    PreservesColimit (Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)))
      F.rightDerivedFunctor := by
  let v (K : CochainComplex C ℤ) : DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
    (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)
  have nat {K L : CochainComplex C ℤ} (f : K ⟶ L) :
      DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f) ≫ v L =
        v K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
    have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C (.up ℤ)).map f)
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
    simp only [v, DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
    rw [reassoc_of% h, ← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]
  have hu (i : I) : IsIso (v (E i)) := by dsimp only [v]; infer_instance
  have huP : IsIso (v (∐ E)) := by dsimp only [v]; infer_instance
  have hFc : IsColimit (Cofan.mk
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (∐ E)))
      fun i ↦ DerivedCategory.Q.map ((F.mapHomologicalComplex _).map (Sigma.ι E i))) :=
    DerivedCategory.isColimitCofanMkQObj
      ((isColimitMapCoconeCofanMkEquiv (F.mapHomologicalComplex (.up ℤ)) E (Sigma.ι E)).1
        (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) (coproductIsCoproduct E)))
  refine preservesColimit_of_preserves_colimit_cocone
    (DerivedCategory.isColimitCofanMkQObj (coproductIsCoproduct E))
    ((isColimitMapCoconeCofanMkEquiv _ _ _).2 ?_)
  refine (IsColimit.equivOfNatIsoOfIso (Discrete.natIso fun i ↦ asIso (v (E i.as))) _ _
    (Cocone.ext (asIso (v (∐ E))) fun i ↦ ?_)) hFc
  dsimp
  rw [Category.assoc, nat]
  simp

/-- Ordinary derived direct image for a qcqs morphism commutes with every small,
uniformly bounded-below family over the inverse-image coefficient sheaf.
Source: Stacks Project, Tag 09A3, relative module version
(blueprint: lem-weil-pbc-proetale-bounded-below-coproducts).

Coproducts are expressed by their universal cocones: `s` and `t` are coproducts of
`K` and its direct images. The final morphism is their canonical comparison, obtained
by descending the images of the coprojections of `s` along the universal cocone `t`.
Thus existence of both coproducts is asserted, rather than assumed. In these derived
module categories they are represented by sheafified termwise direct sums. The rational
algebra structure on each section is unique, so every restriction is automatically linear.

Proof:
1. Transport module sheaves along the small-site model equivalence. The source
   library's Grothendieck theorem gives enough injectives on that model; transport
   them back to the original pro-etale site.
2. By lem-weil-pbc-dplus-injective-representative, choose complexes E_i of injectives,
   all zero below N, and isomorphisms Q(E_i) to K_i. The common bound also bounds
   the termwise coproduct, since evaluation preserves coproducts.
3. Apply lem-weil-pbc-proetale-module-cohomology-coproducts to every classical higher
   direct-image functor. Degree zero identifies with underived direct image, so
   underived direct image preserves coproducts. In positive degree the image of
   each injective term is zero. Preservation of coproducts therefore makes each
   term of the sum E_i acyclic for direct image.
4. Resolve the bounded-below sum by a complex J of injectives with the same bound.
   The quasi-isomorphism to J remains a quasi-isomorphism after direct image, by
   lem-weil-pbc-leray-acyclicity-quasi-iso. Naturality of the derived unit, and its
   invertibility at J, make the unit at the sum invertible too.
5. Termwise coproducts represent derived coproducts. Transport the coproduct of the
   termwise direct images through the invertible units at each E_i and at their sum.
   Naturality identifies the resulting legs with derived direct image of the
   original legs. Transport along Q(E_i) isomorphic to K_i proves preservation for K.
6. Take the image of a coproduct cocone as the target coproduct cocone. Its canonical
   comparison to itself is the identity, by uniqueness in the coproduct property,
   and is therefore invertible. This also covers an empty indexing type. -/
theorem proEtaleRingDerivedDirectImage_boundedBelow_coproducts
    {T U : Scheme.{u}} (h : T ⟶ U) [QuasiCompact h] [QuasiSeparated h]
    (R : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    [∀ V : U.ProEtᵒᵖ, Algebra ℚ (R.obj.obj V)]
    (I : Type (u + 1)) (N : ℤ)
    (K : I → DerivedCategory
      (proEtaleRingModules T ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)))
    (hK : ∀ (i : I) (n : ℤ), n < N →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ s : Cofan K, ∃ _ : IsColimit s,
      ∃ t : Cofan (fun i ↦ (proEtaleRingDerivedDirectImage h R
        ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj (K i)),
      ∃ ht : IsColimit t,
        IsIso (ht.desc (Cofan.mk
          ((proEtaleRingDerivedDirectImage h R
            ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj s.pt)
          (fun i ↦ (proEtaleRingDerivedDirectImage h R
            ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)
              (Iso.refl _)).map (s.inj i)))) := by
  classical
  let S := (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R
  let C := proEtaleRingModules T S
  let D := proEtaleRingModules U R
  let F := proEtaleRingModuleDirectImage h R S (Iso.refl _)
  have : EnoughInjectives C := moduleEnoughInjectives T S
  let adj := (proEtaleRingModuleOperations_properties h R S (Iso.refl _)).2.2.2.2.some
  have : PreservesLimitsOfSize.{0, 0} F := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits F := inferInstance
  have hpres (q : ℕ) : PreservesColimitsOfShape (Discrete I) (F.rightDerived q) :=
    proEtaleRingModuleDirectImage_rightDerived_preservesCoproducts h R I q
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory D) := derived_hasCoproducts
  have representatives (i : I) : ∃ E : CochainComplex C ℤ,
      E.IsStrictlyGE N ∧ (∀ n, Injective (E.X n)) ∧
        Nonempty (DerivedCategory.Q.obj E ≅ K i) := by
    have : (K i).IsGE N := (DerivedCategory.isGE_iff (K i) N).2 (hK i)
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (K i) N
    obtain ⟨E, a, ha, hE, hEN⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L N
    have : QuasiIso a := ha
    exact ⟨E, hEN, hE, ⟨(asIso (DerivedCategory.Q.map a)).symm ≪≫ e.symm⟩⟩
  choose E hEN hE he using representatives
  have : ∀ i, (E i).IsStrictlyGE N := hEN
  have : ∀ (i : I) (n : ℤ), Injective ((E i).X n) := hE
  have : ∀ i, (E i).IsKInjective := fun i ↦
    CochainComplex.isKInjective_of_injective (E i) N
  have : PreservesColimitsOfShape (Discrete I) (F.rightDerived 0) := hpres 0
  have : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  have heval (n : ℤ) : (∐ E).X n ≅ ∐ (fun i ↦ (E i).X n) :=
    PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) E
  have : (∐ E).IsStrictlyGE N := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    apply IsZero.of_iso _ (heval n)
    apply (coproductIsCoproduct (fun i ↦ (E i).X n)).isZero_pt
    exact Functor.isZero _ (fun i ↦ (E i.as).isZero_of_isStrictlyGE N n hn)
  have hacyclic (n : ℤ) : F.rightAcyclic ((∐ E).X n) := by
    apply F.rightAcyclic.prop_of_iso (heval n).symm
    intro q
    have : PreservesColimitsOfShape (Discrete I) (F.rightDerived (q + 1)) := hpres _
    exact (isColimitOfPreserves (F.rightDerived (q + 1))
      (coproductIsCoproduct (fun i ↦ (E i).X n))).isZero_pt
        (Functor.isZero _ fun i ↦ F.isZero_rightDerived_obj_injective_succ q ((E i.as).X n))
  have : PreservesColimit (Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)))
      F.rightDerivedFunctor := uniformCoproduct F I E
        (unit_of_acyclic F (∐ E) N hacyclic)
  let e : Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)) ≅ Discrete.functor K :=
    Discrete.natIso (fun i ↦ (he i.as).some)
  have : PreservesColimit (Discrete.functor K) F.rightDerivedFunctor :=
    preservesColimit_of_iso_diagram F.rightDerivedFunctor e
  let s : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  let t : Cofan (fun i ↦ F.rightDerivedFunctor.obj (K i)) :=
    Cofan.mk (F.rightDerivedFunctor.obj s.pt)
      (fun i ↦ F.rightDerivedFunctor.map (s.inj i))
  have ht : IsColimit t :=
    (isColimitMapCoconeCofanMkEquiv F.rightDerivedFunctor K s.inj).1
      (isColimitOfPreserves F.rightDerivedFunctor (coproductIsCoproduct K))
  refine ⟨s, coproductIsCoproduct K, t, ht, ?_⟩
  change IsIso (ht.desc t)
  have hid : ht.desc t = 𝟙 t.pt := ht.hom_ext (by simp)
  rw [hid]
  infer_instance

end AlgebraicGeometry.Scheme
