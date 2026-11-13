/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Underlying abelian direct-image acyclicity of module K-injectives

## References

* Stacks Project, Cohomology on Sites, Tags 0D6J and 0D6E.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Abelian replacement of a module K-injective remains a quasi-isomorphism after direct image.
This asserts acyclicity for the indicated direct image, without asserting that forgetting
preserves K-injectivity (Stacks, Tags 0D6J and 0D6E). -/
theorem moduleAbelianForget_kInjective_directImage_quasiIso
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B)
    (I : CochainComplex (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective]
    (J : CochainComplex (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [J.IsKInjective]
    (j : ((moduleAbelianForget Λ A).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso ((((v)_*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).map j) := by
  obtain ⟨C, D, hC, hD, T, S, R, Z, W, eM, eA, eB, r, p, ⟨α⟩, ⟨β⟩⟩ :=
    etaleModuleAbelianRingedPresentation Λ v
  let := hC
  let := hD
  have : eM.functor.Additive := eM.functor.additive_of_preserves_binary_products
  have : eA.functor.Additive := eA.functor.additive_of_preserves_binary_products
  have : eB.functor.Additive := eB.functor.additive_of_preserves_binary_products
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      ((sheafCompose S (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj W))
  let Mc := eM.functor.mapHomologicalComplex (.up ℤ)
  let Ac := eA.functor.mapHomologicalComplex (.up ℤ)
  let Bc := eB.functor.mapHomologicalComplex (.up ℤ)
  let rc := r.modules.mapHomologicalComplex (.up ℤ)
  let pc := p.modules.mapHomologicalComplex (.up ℤ)
  let vc := ((v)_*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)
  let αc := NatIso.mapHomologicalComplex α (.up ℤ)
  let βc := NatIso.mapHomologicalComplex β (.up ℤ)
  let j' : rc.obj (Mc.obj I) ⟶ Ac.obj J := αc.hom.app I ≫ Ac.map j
  have : QuasiIso j' := by dsimp [j', Ac]; infer_instance
  obtain ⟨Rf, Rg, Rgf, ηf, ηg, ηgf, hf, hg, hgf, hIf, hIg, κ, hκ, _⟩ :=
    ringedToposDerivedPushforwardComposition T T S R Z W r p
  have : QuasiIso (pc.map j') :=
    (hκ.2 (Mc.obj I) inferInstance (Ac.obj J) inferInstance j').1
  have : QuasiIso (pc.map (Ac.map j)) := by
    have : QuasiIso (pc.map (αc.hom.app I) ≫ pc.map (Ac.map j)) := by
      rw [← pc.map_comp]
      exact inferInstanceAs (QuasiIso (pc.map j'))
    exact quasiIso_of_comp_left (pc.map (αc.hom.app I)) _
  have : QuasiIso (βc.hom.app _ ≫ Bc.map (vc.map j)) := by
    have hn : pc.map (Ac.map j) ≫ βc.hom.app J =
        βc.hom.app _ ≫ Bc.map (vc.map j) := βc.hom.naturality j
    rw [← hn]
    exact quasiIso_comp (pc.map (Ac.map j)) (βc.hom.app J)
  have : QuasiIso (Bc.map (vc.map j)) :=
    quasiIso_of_comp_left (βc.hom.app _) _
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (vc.map j) eB.functor).mp inferInstance

end AlgebraicGeometry.Etale
