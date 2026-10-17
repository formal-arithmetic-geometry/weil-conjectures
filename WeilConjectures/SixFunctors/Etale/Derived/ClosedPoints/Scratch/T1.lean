module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.GlobalGeneration

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Opens)

noncomputable def supportedSections' (U : X.Opens) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  kernel ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).unit.app F)

noncomputable def supportedSectionsι' (U : X.Opens) : supportedSections' F U ⟶ F :=
  kernel.ι _

lemma supportedSectionsι_comp_unit' (U : X.Opens) :
    supportedSectionsι' F U ≫
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).unit.app F = 0 :=
  kernel.condition _

instance (U : X.Opens) : Mono (supportedSectionsι' F U) := by
  dsimp [supportedSectionsι']
  infer_instance

example (U : X.Opens) : IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj (supportedSections' F U)) := by
  let η : F ⟶ (U.ι)_*[ModuleCat.{u + 1} Λ].obj
      ((openImmersionRestriction (ModuleCat.{u + 1} Λ) U.ι).obj F) :=
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).unit.app F
  have hc : supportedSectionsι' F U ≫ η = 0 := supportedSectionsι_comp_unit' F U
  let P := (U.ι)^*[ModuleCat.{u + 1} Λ]
  have : IsIso (P.map η) := sorry
  have hmono : Mono (P.map (supportedSectionsι' F U)) := Functor.map_mono P _
  have hm : Mono (P.map η) := IsIso.mono_of_iso _
  have h1 : P.map (supportedSectionsι' F U) ≫ P.map η = 0 ≫ P.map η := by
    rw [← P.map_comp, hc, P.map_zero, zero_comp]
  have h0 : P.map (supportedSectionsι' F U) = 0 := (@cancel_mono _ _ _ _ _ (P.map η) hm _ _).1 h1
  exact @IsZero.of_mono_eq_zero _ _ _ _ _ _ hmono h0
end AlgebraicGeometry.Etale
