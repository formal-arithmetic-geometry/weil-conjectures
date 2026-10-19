/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.Topology.OpenModuleDerivedSections
import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Derived sections of a derived direct image

Source: Stacks Project, Derived Categories of Schemes, Tag 08D5, proof of (2), and
Cohomology, Tag 0D5T (blueprint: lem-pc-derived-sections-pushforward-comparison).
-/

@[expose] public section

universe u wX wV wU wAb

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

-- Exact forgetting to abelian groups transports invertibility of the derived unit.
private theorem unit_isIso_comp_of_exact
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (J : HomotopyCategory C (ComplexShape.up ℤ))
    [IsIso (F.rightDerivedFunctorUnit.app J)] :
    IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J) := by
  let β := Functor.rightDerivedFunctorCompUnit F G
  have := Functor.isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact F G
  let δ := (F ⋙ G).rightDerivedFunctor.rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β
  have : IsIso δ :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (F ⋙ G).rightDerivedFunctor
      (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) β).mp inferInstance
  have hβ : IsIso (β.app J) := by
    dsimp [β, Functor.rightDerivedFunctorCompUnit]
    infer_instance
  have h : (F ⋙ G).rightDerivedFunctorUnit.app J ≫ δ.app (DerivedCategory.Qh.obj J) =
      β.app J := Functor.rightDerived_fac_app _ _ _ _ _ _
  have : IsIso ((F ⋙ G).rightDerivedFunctorUnit.app J ≫
      δ.app (DerivedCategory.Qh.obj J)) := by rw [h]; exact hβ
  exact IsIso.of_isIso_comp_right ((F ⋙ G).rightDerivedFunctorUnit.app J)
    (δ.app (DerivedCategory.Qh.obj J))

-- Right-derived uniqueness needs only acyclicity, not preservation of K-injectivity.
private theorem derivedSectionsCompositionOfAcyclic
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H = F ⋙ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))) :
    Nonempty (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor) := by
  subst H
  let β := Functor.rightDerivedFunctorCompUnit F G
  have : (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
        _ (fun J ↦ ?_)
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
    change IsIso (β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
    have := h I
    dsimp [β, Functor.rightDerivedFunctorCompUnit]
    infer_instance
  exact ⟨(Functor.rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit β (HomotopyCategory.quasiIso C (.up ℤ))).symm⟩

/-- For an open `U` of the target of `f`, derived global sections of the derived
pushforward of `E` restricted to `f⁻¹(U)` agree naturally with derived global sections
on that inverse image. The isomorphism is in the unbounded derived category of abelian
 groups, so it compares complexes up to quasi-isomorphism, not strict complexes.
Source: Stacks, Tag 08D5, proof of (2), displayed derived-sections identity, with the
composition mechanism of Tag 0D5T
(blueprint: lem-pc-derived-sections-pushforward-comparison).

Proof: (1) Put `V = f⁻¹(U)`. The definition of module direct image gives the natural
identity Γ(U, (f_U)_*G) = Γ(V, G) on module sheaves.
(2) Map the ringed spaces U and V to the one-point ringed space with ring ℤ.
Uniqueness of ring maps out of ℤ makes the map from V the composite of f_U and the
map from U. Direct image along these maps is global sections, and its K-injective
computation is therefore RΓ. This uses def-weil-locally-ringed-space-morphism and
 def-pc-ringed-spaces-derived-direct-image; the point is a ringed space, not Spec ℤ.
(3) Apply lem-pc-ringed-spaces-derived-direct-image-composition to V → U → (pt, ℤ).
The composition isomorphism identifies RΓ(U,-) after R(f_U)_* with RΓ(V,-).
Whisker by exact restriction from X to V (def-pc-derived-open-restriction-maps).
This yields a natural isomorphism in E; the construction also commutes with restriction
 to smaller opens. No quasi-coherence or boundedness hypothesis is used. -/
theorem derivedSectionsPushforwardComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV}
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U).toScheme.toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wAb} AddCommGrpCat.{u}] :
    Nonempty
      (((schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory ⋙
          schemeDerivedDirectImage (morphismRestrict f U) ⋙
          RingedSpace.openModuleDerivedSections U.toScheme.toRingedSpace ⊤) ≅
        ((schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory ⋙
          RingedSpace.openModuleDerivedSections (f ⁻¹ᵁ U).toScheme.toRingedSpace ⊤)) := by
  let V := (f ⁻¹ᵁ U).toScheme
  let g := morphismRestrict f U
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let G := RingedSpace.openModuleSections U.toScheme.toRingedSpace ⊤
  let H := RingedSpace.openModuleSections V.toRingedSpace ⊤
  let M := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let A := forget₂
    (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
    AddCommGrpCat.{u}
  let _ := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
  have h : ∀ (I : CochainComplex (SheafOfModules.{u} (moduleRings V.toRingedSpace)) ℤ)
      [I.IsKInjective], IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
    intro I hI
    let J := (F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I)
    let _ : IsIso (M.rightDerivedFunctorUnit.app J) :=
      isIso_directImage_globalSections_unit_on_kInjective g I
    exact unit_isIso_comp_of_exact M A J
  have e₀ : H = F ⋙ G := rfl
  obtain ⟨e⟩ := derivedSectionsCompositionOfAcyclic F G H e₀ h
  exact ⟨Functor.isoWhiskerLeft (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory e⟩

end AlgebraicGeometry
