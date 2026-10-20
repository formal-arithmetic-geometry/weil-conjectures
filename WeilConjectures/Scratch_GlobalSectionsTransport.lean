module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

@[expose] public section

universe u

open CategoryTheory Abelian Limits Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory

lemma Sheaf.ΓNatIsoSheafSections_inv_app_comp_hom_app {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A] [HasWeakSheafify J A] [HasTerminal C]
    {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).inv.app F ≫
        (Sheaf.ΓNatIsoSheafSections J A hT').hom.app F =
      F.obj.map (hT.from T').op := by
  rw [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓNatIsoSheafSections, Adjunction.rightAdjointUniq_inv_app,
    Adjunction.rightAdjointUniq_trans_app]
  apply ((constantSheafAdj J A hT').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Adjunction.homEquiv_counit]
  sorry

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

lemma upperStarRestrictScalarsIso_hom_app_comp_upperStarInvIsoLowerStarHom {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalarsIso ρ e.inv).hom.app F ≫
        (Sheaf.restrictScalars _ ρ).map
          ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).hom.app F) =
      (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e).hom.app
        ((Sheaf.restrictScalars _ ρ).obj F) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e.inv).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  sorry

variable {k : Type u} [Field k] [IsSepClosed k]

variable (Λ) in
/-- The sheaf-level transport `Γ(pt, F) ≅ Γ(pt, h^* F)` along an automorphism `h` of `Spec k`. -/
noncomputable def sectionsPointTransportIso (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] :
    (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k)) ≅
      (h)^*[ModuleCat.{u + 1} Λ] ⋙
        (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (etalePoint k)) :=
  sectionsTransportIso (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) (asIso h).symm)
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) (inv h))
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint)

lemma restrictScalars_map_sectionsPointTransportIso_hom_app (h : Spec (.of k) ⟶ Spec (.of k))
    [IsIso h] (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (ModuleCat.restrictScalars ρ).map ((sectionsPointTransportIso Λ' h).hom.app F) =
      (sectionsPointTransportIso Λ h).hom.app ((Sheaf.restrictScalars _ ρ).obj F) ≫
        ((sheafSections _ _).obj (op (etalePoint k))).map
          ((upperStarRestrictScalarsIso ρ h).hom.app F) := by
  sorry

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

lemma globalSectionsTransport_hom_app_comp_rightDerivedGlobalSectionsIsoOfIsSepClosed
    (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (M : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (globalSectionsTransport Λ h).hom.app M ≫
        (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.app
          ((L((h)^*[ModuleCat.{u + 1} Λ])).obj M) =
      (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.app M ≫
        (Functor.mapDerivedCategoryTriangleIso (sectionsPointTransportIso Λ h)).hom.app M ≫
        ((sheafSections _ _).obj (op (etalePoint k))).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory _ h).inv.app M) := by
  have : PreservesFiniteLimits (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    preservesFiniteLimits_of_natIso (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).symm
  have : PreservesFiniteColimits
      (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    preservesFiniteColimits_of_natIso (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).symm
  have h₁ := rightDerivedFunctorCompIso'_inv_app_comp_sectionsTransportIso
    (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) (asIso h).symm)
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) (inv h))
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint) M
  simp only [globalSectionsTransport, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  rw [(rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.naturality]
  exact reassoc_of% h₁ _

lemma derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app
    (M' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app M' =
      (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj M') ≫
        (Functor.mapDerivedCategorySquareIso
          (G₁ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
            (op (etalePoint k)))
          (G₂ := ModuleCat.restrictScalars.{u + 1} ρ) (Iso.refl _)).hom.app M' ≫
        (ModuleCat.derivedRestrictScalars ρ).map
          ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ').inv.app M') := by
  simp [derivedRestrictScalarsCompRightDerivedGlobalSectionsIso]

lemma main
    (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (M' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app M' ≫
        (ModuleCat.derivedRestrictScalars ρ).map ((globalSectionsTransport Λ' h).hom.app M') =
      (globalSectionsTransport Λ h).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj M') ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          ((leftDerivedUpperStarRestrictScalarsIso ρ h).hom.app M') ≫
        (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app
          ((L((h)^*[ModuleCat.{u + 1} Λ'])).obj M') := by
  have key := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (r₀ := Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ)
    (r₁ := Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ)
    (r₂ := ModuleCat.restrictScalars.{u + 1} ρ)
    (p₁ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (etalePoint k)))
    (p₁₂ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op (etalePoint k)))
    (P₁ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
      (op (etalePoint k)))
    (P₁₂ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
      (op (etalePoint k)))
    (upperStarRestrictScalarsIso ρ h) (Iso.refl _) (Iso.refl _)
    (sectionsPointTransportIso Λ h) (sectionsPointTransportIso Λ' h)
    (fun F ↦ by simpa using restrictScalars_map_sectionsPointTransportIso_hom_app ρ h F) M'
  have hT' := globalSectionsTransport_hom_app_comp_rightDerivedGlobalSectionsIsoOfIsSepClosed
    (Λ := Λ') h M'
  have hT := globalSectionsTransport_hom_app_comp_rightDerivedGlobalSectionsIsoOfIsSepClosed
    (Λ := Λ) h ((Sheaf.derivedRestrictScalars _ ρ).obj M')
  sorry

end AlgebraicGeometry.Etale
