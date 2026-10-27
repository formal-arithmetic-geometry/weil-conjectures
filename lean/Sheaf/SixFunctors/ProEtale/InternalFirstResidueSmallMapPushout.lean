/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IntegralModelsStacksData

/-! # Transport of pushouts to the coefficient-sized small site -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Section-ring reconstruction and passage to the equivalent small site
transport pushout squares of commutative ring sheaves.

Source: Stacks Tags 00YV and 09A5; the section-ring reconstruction step in
the integral-models proof.
(blueprint: lem-sfb-internal-first-residue-small-map-pushout).

Proof: section-ring reconstruction is an equivalence on commutative ring
objects, and the coefficient-sized `AsSmall` passage is an equivalence of
sites. Apply the pushout universal property through these equivalences and
use the canonical comparison maps on the four corners. The lower map remains
the identity under both transports.
-/
theorem internal_first_residue_smallMap_pushout
    (X : Scheme.{u})
    {R B S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj B] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj B] [IsCommMonObj S]
    (f : R ⟶ B) [IsMonHom f] (q : R ⟶ S) [IsMonHom q]
    (p : B ⟶ S) [IsMonHom p]
    (h : IsPushout f q p (𝟙 _)) :
    IsPushout (IntegralModelsStacks.smallMap X f)
      (IntegralModelsStacks.smallMap X q)
      (IntegralModelsStacks.smallMap X p) (𝟙 _) := by
  have hf : Epi f := Preadditive.epi_of_cancel_zero f (fun g hg ↦ by
    let d := h.desc g 0 (by simpa using hg)
    have hd : d = 0 := by
      simpa only [Category.id_comp] using h.inr_desc g 0 (by simpa using hg)
    calc
      g = p ≫ d := (h.inl_desc g 0 (by simpa using hg)).symm
      _ = 0 := by rw [hd, comp_zero])
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hs : Epi (IntegralModelsStacks.sectionMap X f) :=
    U.epi_of_epi_map (by exact hf)
  let F := (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  have : e.inverse.IsContinuous (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).IsContinuous _ _)
  have : e.functor.IsContinuous (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : e.symm.functor.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs (e.inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X))
  have : e.symm.inverse.IsContinuous (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    inferInstanceAs (e.functor.IsContinuous (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X))
  have : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (e.symm.toAdjunction.sheafPushforwardContinuous
        (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X))
  have : Epi (IntegralModelsStacks.smallMap X f) :=
    inferInstanceAs (Epi (F.map (IntegralModelsStacks.sectionMap X f)))
  apply IsPushout.of_horiz_isIso_epi
  constructor
  have hc : f ≫ p = q := by simpa using h.w
  change F.map (IntegralModelsStacks.sectionMap X f) ≫
    F.map (IntegralModelsStacks.sectionMap X p) =
      F.map (IntegralModelsStacks.sectionMap X q) ≫ 𝟙 _
  rw [Category.comp_id, ← F.map_comp]
  congr 1
  ext Z x
  exact ConcreteCategory.congr_hom (congr_app (congrArg (fun k : R ⟶ S ↦ k.hom) hc) Z) x

end AlgebraicGeometry.ProEtale

