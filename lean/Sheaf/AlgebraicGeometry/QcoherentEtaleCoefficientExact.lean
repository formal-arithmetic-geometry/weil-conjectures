/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsFunctorExact

/-! # Exact sequences of the associated lifted quasi-coherent sheaves

Source: Stacks Project, Tags 03P2 and 03DW.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coefficient_map_sheafify (X : Scheme.{u})
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (etaleTensorSectionsFunctor X).map φ ≫ (etaleTensorSectionsFunctorObjIso G).hom =
      (etaleTensorSectionsFunctorObjIso F).hom ≫ coherentEtaleMap F G φ := by
  have h : Functor.whiskerRight (etaleTensorSectionsMap φ)
      AddCommGrpCat.uliftFunctor.{u + 1, u} = (coherentEtaleMap F G φ).hom := by
    apply NatTrans.ext
    funext U
    exact (congrArg AddCommGrpCat.uliftFunctor.map
      ((Classical.choose_spec (etale_zariski_qcoh_comparison X)).1 F G φ U.unop)).symm
  change (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (etaleTensorSectionsMap φ) AddCommGrpCat.uliftFunctor) ≫ _ = _
  rw [h]
  exact (sheafificationNatIso X.smallEtaleTopology AddCommGrpCat.{u + 1}).inv.naturality
    (coherentEtaleMap F G φ)

/-- A short exact sequence of quasi-coherent modules is short exact after
passing to its lifted associated etale sheaves.
Source: Stacks Project, Tags 03P2 and 03DW.
(blueprint: lem-weil-pbc-qcoherent-etale-coefficient-exact)

Proof: The tensor-section sheafification functor is exact. For quasi-coherent
modules its values are naturally isomorphic to the recorded lifted associated
sheaves: the components of coherentEtaleMap give this naturality. Transport the
image short exact sequence through these three coefficient isomorphisms. The
zero composite follows by the same naturality and cancellation of the source
isomorphism. All arguments include zero objects and empty schemes. -/
theorem coherentEtaleMap_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    ∃ hz : coherentEtaleMap S.X₁ S.X₂ S.f ≫ coherentEtaleMap S.X₂ S.X₃ S.g = 0,
      (ShortComplex.mk (coherentEtaleMap S.X₁ S.X₂ S.f)
        (coherentEtaleMap S.X₂ S.X₃ S.g) hz).ShortExact := by
  let T := etaleTensorSectionsFunctor X
  let : T.Additive := by dsimp [T, etaleTensorSectionsFunctor]; infer_instance
  let : PreservesFiniteLimits T := (etaleTensorSectionsFunctor_exact X).1
  let : PreservesFiniteColimits T := (etaleTensorSectionsFunctor_exact X).2
  have h₁ := coefficient_map_sheafify X S.X₁ S.X₂ S.f
  have h₂ := coefficient_map_sheafify X S.X₂ S.X₃ S.g
  have hz : coherentEtaleMap S.X₁ S.X₂ S.f ≫ coherentEtaleMap S.X₂ S.X₃ S.g = 0 := by
    apply (cancel_epi (etaleTensorSectionsFunctorObjIso S.X₁).hom).mp
    rw [← Category.assoc, ← h₁, Category.assoc, ← h₂,
      ← Category.assoc, ← T.map_comp, S.zero, T.map_zero, zero_comp, comp_zero]
  let R := ShortComplex.mk (coherentEtaleMap S.X₁ S.X₂ S.f)
    (coherentEtaleMap S.X₂ S.X₃ S.g) hz
  let e : S.map T ≅ R := ShortComplex.isoMk
    (etaleTensorSectionsFunctorObjIso S.X₁)
    (etaleTensorSectionsFunctorObjIso S.X₂)
    (etaleTensorSectionsFunctorObjIso S.X₃) h₁.symm h₂.symm
  exact ⟨hz, ShortComplex.shortExact_of_iso e (hS.map_of_exact T)⟩

end
end AlgebraicGeometry.Scheme.Modules
