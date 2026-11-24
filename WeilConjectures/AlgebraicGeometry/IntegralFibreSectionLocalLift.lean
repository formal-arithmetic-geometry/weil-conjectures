/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux

/-! # Local sections of an integral geometric fibre

## References

* Stacks Project, Tag 0EYP.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Every section on the geometric fibre of an integral morphism is the restriction
of a section over some pointed etale neighbourhood of the geometric point.
(Stacks, Tag 0EYP) -/
theorem integralFibreSection_localLift
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X')))) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (z : F.obj.obj (op (f.Etale.obj V))),
      (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z = t := by
  classical
  obtain ⟨e, he⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  obtain ⟨b, hb⟩ := exists_integralStrictLocalFibreComparison Λ sq F
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  let : N.Initial := (strictHenselizationAffineProperties s).1
  let := (strictHenselizationAffineProperties s).2.1
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let P := ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj
  let c := ((pointSmallEtale s).presheafFiberCocone P).whisker N.op
  have hc : CategoryTheory.Limits.IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((pointSmallEtale s).isColimitPresheafFiberCocone P)
  obtain ⟨j, z, hz⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
    (CategoryTheory.Limits.isColimitOfPreserves (forget (ModuleCat.{u + 1} Λ)) hc) (e.inv (b.inv t))
  refine ⟨((AffineEtale.Spec Y).obj
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1),
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2,
    z, ?_⟩
  have h := congrArg (fun a ↦ b.hom (e.hom a)) hz
  have hformula := congrArg (fun a ↦ a z)
    ((congrArg (fun a ↦ a ≫ b.hom) (he j.unop)).trans (hb j.unop))
  have hh := hformula.symm.trans h
  simp only [Iso.inv_hom_id_apply] at hh
  convert hh using 1

end AlgebraicGeometry.Etale
