/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure


public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Local sections of an integral geometric fibre

## References

* Stacks Project, Tag 0EYP.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- A neighbourhood section whose restriction to an integral geometric fibre is
zero becomes zero on a pointed etale refinement of that neighbourhood.
(Stacks, Tag 0EYP) -/
theorem integralFibreSection_localZero
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
    (z : F.obj.obj (op (f.Etale.obj V)))
    (hz : (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z = 0) :
    ∃ (W : Y.Etale) (w : (pointSmallEtale s).fiber.obj W) (a : W ⟶ V),
      (pointSmallEtale s).fiber.map a w = v ∧
        (F.obj.map (f.Etale.map a).op).hom z = 0 := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨hlocal, hstrict⟩ := (show ∃ (_ : IsLocalRing (Scheme.strictHenselization s)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization s) from
      ⟨inferInstance, ⟨inferInstance⟩⟩)
  let := hlocal
  let := hstrict
  obtain ⟨t, ht, hclosed, i, hsq, hi, Θ, b, hformula⟩ :=
    strictHenselizationModuleFibre_factorization Λ sq F
  have hintegral : IsIntegralHom (Limits.pullback.snd f
      (strictLocalizationToBase s)) := inferInstance
  let := hintegral
  have hinj := strictHenselianIntegralSections_injective Λ (strictHenselization s)
    (Limits.pullback.snd f (strictLocalizationToBase s)) t hclosed i f' hsq
    ((Limits.pullback.fst f (strictLocalizationToBase s))^*[ModuleCat.{u + 1} Λ].obj F)
  let germ := (pointSmallEtale s).toPresheafFiber V v
    ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj
  have hzero : germ.hom z = 0 := by
    apply (ConcreteCategory.bijective_of_isIso Θ.hom).1
    apply hinj
    apply (ConcreteCategory.bijective_of_isIso b.hom).1
    simpa only [map_zero] using (hformula V v z).trans hz
  have heq : germ z = germ 0 := by simpa only [map_zero] using hzero
  obtain ⟨W, a, w, hw, ha⟩ :=
    ((pointSmallEtale s).toPresheafFiber_eq_iff'
      (P := ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj) V v z 0).mp heq
  refine ⟨W, w, a, hw, ?_⟩
  change (F.obj.map (f.Etale.map a).op).hom z =
    (F.obj.map (f.Etale.map a).op).hom 0 at ha
  simpa only [map_zero] using ha

end AlgebraicGeometry.Etale
