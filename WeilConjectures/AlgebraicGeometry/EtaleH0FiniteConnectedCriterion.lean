/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-!
# A finite-cover connectedness criterion for étale module sections

## References

* Stacks Project, Tags 09ZG and 09ZF
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Restriction of étale module sections to a closed subscheme is an isomorphism if
all irreducible closed subsets of every finite cover meet that subscheme in a
nonempty connected subset (Stacks, Tags 09ZG and 09ZF). -/
theorem isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hconn : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      ∀ C : Set X', IsClosed C → IsIrreducible C →
        IsConnected (C ∩ h ⁻¹' Set.range i))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let G := (sheafCompose X.smallEtaleTopology U).obj F
  have hG :=
    isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections
      i hconn G
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F
  let θ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G
  have hθ : IsIso (θ.hom.app (Opposite.op (⊤_ X.Etale))) := by
    unfold globalSectionsUpperStarMap at hG
    have h' : IsIso (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op (⊤_ X.Etale))).map θ) := by
      simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hG
    exact h'
  let H := (sheafCompose Z.smallEtaleTopology U).obj
    ((i)^*[ModuleCat.{u + 1} Λ].obj F)
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i
  let c := (adj.homEquiv G H).symm
    ((sheafCompose X.smallEtaleTopology U).map η)
  have : IsIso c := isIso_moduleAbelianInverseImageComparison i Λ F
  have hw : θ ≫ (i)_*[AddCommGrpCat.{u + 1}].map c =
      (sheafCompose X.smallEtaleTopology U).map η := by
    exact ((adj.homEquiv G H).apply_symm_apply
      ((sheafCompose X.smallEtaleTopology U).map η) : _).trans rfl
  have hw' := congrArg (fun f ↦ f.hom.app (Opposite.op (⊤_ X.Etale))) hw
  change θ.hom.app (Opposite.op (⊤_ X.Etale)) ≫
    ((i)_*[AddCommGrpCat.{u + 1}].map c).hom.app
      (Opposite.op (⊤_ X.Etale)) = U.map (η.hom.app (Opposite.op (⊤_ X.Etale))) at hw'
  have : IsIso (U.map (η.hom.app (Opposite.op (⊤_ X.Etale)))) := by
    rw [← hw']
    infer_instance
  have : IsIso (η.hom.app (Opposite.op (⊤_ X.Etale))) :=
    isIso_of_reflects_iso _ U
  have : IsIso (((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (Opposite.op (⊤_ X.Etale))).map η) := ‹IsIso (η.hom.app _)›
  have : IsIso (((i)^*[ModuleCat.{u + 1} Λ].obj F).obj.map
      (PreservesTerminal.iso i.Etale).inv.op) := by infer_instance
  unfold globalSectionsUpperStarMap
  infer_instance

end AlgebraicGeometry.Etale
