/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small

/-! # Quasi-coherent coefficients under restriction to an open etale site

Source: Stacks Project, Sites, Section 00XZ; Descent, Tags 03DR and 03DU.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Restriction along an open immersion for the small coefficient universe.
The continuous localization functor is used directly, without changing coefficient data.
Source: Stacks Sites 00XZ. -/
noncomputable def etaleOpenSmallRestriction {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u} := by
  letI : (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).IsContinuous
      U.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (inferInstance : Etale j) le_rfl
  exact (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).sheafPushforwardContinuous
    AddCommGrpCat.{u} U.smallEtaleTopology X.smallEtaleTopology

/-- The canonical sectionwise identification of the restricted quasi-coherent etale sheaf.
We use sheafPushforwardContinuous directly so that coefficients remain in the original
universe of etaleTensorSectionsSheaf. The formula pins down the sheaf isomorphism and
its naturality in the module: it is inverse normalized pullback composition followed by
pullback of the canonical tensor-pullback/restriction comparison.
Source: Stacks Project, Sites, Section 00XZ; Descent, Tag 03DR, equation (35.8.1),
and Tag 03DU, item 4; module restriction and pullback along an open immersion. -/
theorem etaleTensorSectionsSheaf_openIdentification {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ e : (etaleOpenSmallRestriction j).obj
          (Scheme.Modules.etaleTensorSectionsSheaf F) ≅
        Scheme.Modules.etaleTensorSectionsSheaf ((Scheme.Modules.restrictFunctor j).obj F),
      ∀ v : U.Etale, e.hom.hom.app (Opposite.op v) =
        ((Scheme.Modules.tensorSectionsComp v.hom j).inv.app F).app ⊤ ≫
          ((Scheme.Modules.tensorPullback v.hom).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).leftAdjointUniq
              (Scheme.Modules.restrictAdjunction j)).hom.app F)).app ⊤ := by
  let c := fun v : U.Etale ↦ etaleOpenTensorSectionsComponentIso j F v
  let e : ((etaleOpenSmallRestriction j).obj
      (Scheme.Modules.etaleTensorSectionsSheaf F)).obj ≅
      (Scheme.Modules.etaleTensorSectionsSheaf
        ((Scheme.Modules.restrictFunctor j).obj F)).obj :=
    NatIso.ofComponents (fun v ↦ c v.unop)
      (fun g ↦ etaleOpenTensorSectionsComponent_naturality j F g.unop)
  refine ⟨ObjectProperty.isoMk _ e, ?_⟩
  intro v
  rfl

end AlgebraicGeometry
