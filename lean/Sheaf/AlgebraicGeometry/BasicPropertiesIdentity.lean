/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.IdentityResolutionHomology
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives

/-! # Identity property of module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-identity).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private instance schemeEnoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules :=
  enoughInjectives X

private instance sectionsAdditive (X : Scheme.{u}) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
  inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)

noncomputable section

open Opposite

set_option maxHeartbeats 400000 in
-- Resolution transports compare both module-valued and additive-group-valued homology.
set_option backward.isDefEq.respectTransparency.types false in
/-- Identity property of the cohomology map induced by an h-map.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB;
Derived Categories, Tags 013P, 013S, 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-identity).

Proof (agent argument specialized from the parent node):
Steps 1--3 are packaged in `moduleCohomologyFMap_identity_resolution_homology`;
the Lean proof combines that factorization with cancellation and Step 4.
1. For the choices D defining the identity-scheme map, take the ordinary resolution
   descent alpha of psi from D.J to D.I. The pushforward-identity natural isomorphism
   identifies the source of D.lambda with D.I; call the resulting map l.
2. The augmentation equations say that D.beta and alpha followed by l agree after
   D.J.ι. Extend by zero to integer indices and apply uniqueness of maps into a bounded
   below injective complex after a quasi-isomorphism (Stacks Tag 013S). Restrict the
   resulting homotopy to natural indices. Applying additive global sections gives the
   same map on homology for beta and alpha followed by l.
3. The pinned sections comparison D.a is the global-sections map of the inverse
   pushforward-identity comparison. Consequently homology of l is the invertible
   vertical map in the definition. Cancel it against its inverse.
4. Naturality of the forgetful homology comparison and of isoRightDerivedObj identifies
   the remaining composite with the underlying map of H^p(Z,psi). This argument uses
   the arbitrary choices defining the map and needs no independence theorem.
-/
theorem moduleCohomologyFMap_basic_identity {Z : Scheme.{u}}
    (GZ FZ : SheafOfModules.{u} Z.ringCatSheaf) (ψ : GZ ⟶ FZ) (p : ℕ) :
    moduleCohomologyFMap (𝟙 Z) ψ p =
        (forget₂ _ AddCommGrpCat).map ((Z.toRingedSpace.moduleCohomology p).map ψ) := by
  unfold moduleCohomologyFMap
  generalize Classical.choice _ = D
  let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  let U := forget₂ (ModuleCat.{u}
    ((moduleRings Z.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let Γc := (Γ ⋙ U).mapHomologicalComplex (ComplexShape.up ℕ)
  let α := InjectiveResolution.desc ψ D.I D.J
  have hsplit := moduleCohomologyFMap_identity_resolution_homology GZ FZ ψ D p
  change H.map (Γc.map D.β) = H.map (Γc.map α) ≫
    H.map (D.a.hom ≫ Γc.map D.lambda) at hsplit
  have hn := D.J.isoRightDerivedObj_hom_naturality ψ D.I α
    (InjectiveResolution.desc_commutes_zero ψ D.I D.J) Γ p
  dsimp only [Functor.comp_map] at hn
  have hs := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).map α)) U
  change U.map ((Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).map α) ≫
      (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso U).inv =
    (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso U).inv ≫
      H.map (Γc.map α) at hs
  change D.map p = _
  dsimp only [ModuleCohomologyFMapData.map]
  change U.map (D.J.isoRightDerivedObj Γ p).hom ≫
    (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso U).inv ≫
    H.map (Γc.map D.β) ≫ inv (I := D.invertible p) (H.map (D.a.hom ≫ Γc.map D.lambda)) ≫
    (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso U).hom ≫
    U.map (D.I.isoRightDerivedObj Γ p).inv = _
  have := D.invertible p
  rw [hsplit]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hs, Iso.inv_hom_id_assoc, ← U.map_comp_assoc, ← hn]
  rw [← U.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl


end

end AlgebraicGeometry.Scheme.Modules
