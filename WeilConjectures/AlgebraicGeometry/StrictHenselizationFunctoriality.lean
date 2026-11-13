/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists

/-! # Strict henselization functoriality

## Main results

* `strictHenselizationResidue` (clause (1)): the strict henselization at a geometric point is
  strictly henselian, with residue field uniquely identified with a separable closure.
* `strictHenselizationFunctoriality` (clauses (2)–(4)): a morphism of pointed schemes induces
  a unique local map of strict henselizations compatible with residue fields and
  neighbourhoods.

## Implementation details

Clause (1) is stated for every scheme and geometric point in
`strictHenselizationResidue`. The canonical map `j_Y` is the existing
`Scheme.strictLocalizationToBase`, and the canonical maps `c_V` are the legs of
`Scheme.strictHenselizationAffineCone` followed by `isoSpec.inv`,
over the chosen representatives of the affine pointed neighbourhoods. The functoriality theorem
takes the residue identifications of clause (1) as data tied by their characterizing equations.
The algebra structures on Ω are required to be exactly the geometric-point embeddings.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 08HV](https://stacks.math.columbia.edu/tag/08HV)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Clause (1): the strict henselization at a geometric point `ȳ` is a strictly henselian local
ring whose closed point maps to the image of `ȳ`, and there is a unique identification of its
residue field with the separable closure of `κ(y)` in `Ω` through which `ȳ` and the pointed
étale neighbourhoods factor. -/
theorem strictHenselizationResidue
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselization barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) ∧
      Scheme.strictLocalizationToBase barY
          (IsLocalRing.closedPoint (Scheme.strictHenselization barY)) =
        barY (IsLocalRing.closedPoint Ω) ∧
      IsSepClosed (separableClosure
        (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω) ∧
      ∃! σ : IsLocalRing.ResidueField (Scheme.strictHenselization barY) ≃+*
          separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
        (∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
          Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σ.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barY)))) ≫
            (Scheme.strictHenselizationAffineCone barY).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
            ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left) ∧
        Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σ.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barY)))) ≫
          Scheme.strictLocalizationToBase barY = barY := by
  have hlocal : IsLocalRing (Scheme.strictHenselization barY) := inferInstance
  have hstrict : IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) :=
    ⟨inferInstance⟩
  let := hlocal
  obtain ⟨ψ, hsurj, hker, hpoint⟩ := strictHenselizationPointedMap barY hΩ
  let σ : IsLocalRing.ResidueField (Scheme.strictHenselization barY) ≃+*
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
    (Ideal.quotEquivOfEq hker.symm).trans (ψ.quotientKerEquivOfSurjective hsurj)
  have hσ : σ.toRingHom.comp
      (IsLocalRing.residue (Scheme.strictHenselization barY)) = ψ := by
    ext x
    rfl
  have hpointσ : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
      Spec.map (CommRingCat.ofHom
        (((IntermediateField.val
          (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σ.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barY)))) ≫
        (Scheme.strictHenselizationAffineCone barY).π.app (Opposite.op (Opposite.op j)) ≫
        (Spec (Opposite.unop ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
    simpa only [RingHom.comp_assoc, hσ] using hpoint
  let pointLift := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY))))
  have hbase : pointLift ≫ Scheme.strictLocalizationToBase barY = barY := by
    have hn := (Scheme.strictHenselizationAffineProperties barY).2.1
    let := hn
    let j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY) :=
      Classical.choice IsCofiltered.nonempty
    have hj := Scheme.strictHenselizationStructuralMap_eq barY j
    have hp := hpointσ j
    have hw := ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.w
    change pointLift ≫ Scheme.strictLocalizationToBase barY = barY
    rw [← hj]
    simpa only [pointLift, Scheme.isoSpec_Spec_inv, Category.assoc] using!
      (congrArg (fun f ↦ f ≫ ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1).hom) hp).trans hw
  have hclosed : pointLift (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (Scheme.strictHenselization barY) := by
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  refine ⟨hlocal, hstrict, ?_, IsSepClosure.sep_closed
    (Y.residueField (barY (IsLocalRing.closedPoint Ω))), σ, ⟨hpointσ, hbase⟩, ?_⟩
  · simpa only [Scheme.Hom.comp_apply, hclosed] using!
      congrArg (fun f ↦ f (IsLocalRing.closedPoint Ω)) hbase
  · intro σ' hσ'
    let f := CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY)))
    let f' := CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ'.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY)))
    have hmaps : Spec.map f' = Spec.map f := by
      obtain ⟨hl⟩ := (Scheme.strictHenselizationAffineProperties barY).2.2
      apply hl.hom_ext
      intro j
      apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj
          j.unop.unop).1.left)).isoSpec.inv).1
      exact (hσ'.1 j.unop.unop).trans (hpointσ j.unop.unop).symm
    have hrings := congrArg CommRingCat.Hom.hom (Spec.map_injective hmaps)
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := Scheme.strictHenselization barY) x
    exact congrArg (fun q ↦ q r) hrings

/-- Functoriality of strict henselizations (clauses (2)–(4)): for `g : T ⟶ S` and geometric
points with `s̄ = t̄ ≫ g`, the separable closure of `κ(s)` in `Ω` lies in that of `κ(t)`, and
there is a unique local map `𝒪^sh_{S,s̄} → 𝒪^sh_{T,t̄}` over `g` inducing this inclusion on
residue fields; it is compatible with the canonical maps to pointed étale neighbourhoods. -/
theorem strictHenselizationFunctoriality
    {S T : Scheme.{v}} (g : T ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
    (hbar : barS = barT ≫ g)
    [Algebra (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω]
    [Algebra (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω]
    (hΩS : algebraMap (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barS)).hom)
    (hΩT : algebraMap (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barT)).hom)
    [IsLocalRing (Scheme.strictHenselization barS)]
    [IsLocalRing (Scheme.strictHenselization barT)]
    (σS : IsLocalRing.ResidueField (Scheme.strictHenselization barS) ≃+*
      separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)
    (σT : IsLocalRing.ResidueField (Scheme.strictHenselization barT) ≃+*
      separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)
    (hσS : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σS.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barS)))) ≫
          (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).2.left)
    (hσT : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σT.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barT)))) ≫
          (Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).2.left) :
    (∀ x : Ω,
      x ∈ separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω →
      x ∈ separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω) ∧
    ∃ h : Scheme.strictHenselization barS ⟶ Scheme.strictHenselization barT,
      IsLocalHom h.hom ∧
      Spec.map h ≫ Scheme.strictLocalizationToBase barS =
        Scheme.strictLocalizationToBase barT ≫ g ∧
      (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barS))) =
        ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barT)))).comp h.hom ∧
      (∀ h' : Scheme.strictHenselization barS ⟶ Scheme.strictHenselization barT,
        IsLocalHom h'.hom →
        Spec.map h' ≫ Scheme.strictLocalizationToBase barS =
          Scheme.strictLocalizationToBase barT ≫ g →
        (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barS))) =
          ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barT)))).comp h'.hom →
        h' = h) ∧
      (∀ (a : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS)) (b : SmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barT))
         (w : ((Scheme.AffineEtale.Spec T).obj ((equivSmallModel.{v}
           (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1).left ⟶
           ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{v}
             (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1).left),
        w ≫ ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1).hom =
          ((Scheme.AffineEtale.Spec T).obj ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1).hom ≫ g →
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).2.left ≫ w =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).2.left →
        ((Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op b)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1.left)).isoSpec.inv)
            ≫ w =
          Spec.map h ≫
            (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op a)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1.left)).isoSpec.inv)
    := by
  obtain ⟨h, hhlocal, hhbase, hhres⟩ :=
    strictHenselizationMapExists g barT barS hbar hΩS hΩT σS σT hσS hσT
  let ψS := (((IntermediateField.val
    (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σS.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barS)))
  let ψT := (((IntermediateField.val
    (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σT.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barT)))
  have hres : ψS = ψT.comp h.hom := hhres
  have hspec : Spec.map (CommRingCat.ofHom ψT) ≫ Spec.map h =
      Spec.map (CommRingCat.ofHom ψS) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hres.symm
  let cS := fun a : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) ↦
    (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op a)) ≫
      (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1.left)).isoSpec.inv
  let cT := fun b : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT) ↦
    (Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op b)) ≫
      (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1.left)).isoSpec.inv
  let pS := fun a : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) ↦
    ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1).hom
  let pT := fun b : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT) ↦
    ((Scheme.AffineEtale.Spec T).obj ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1).hom
  have hcS : ∀ a, cS a ≫ pS a = Scheme.strictLocalizationToBase barS := by
    intro a
    simpa only [cS, pS, Scheme.isoSpec_Spec_inv] using!
      Scheme.strictHenselizationStructuralMap_eq barS a
  have hcT : ∀ b, cT b ≫ pT b = Scheme.strictLocalizationToBase barT := by
    intro b
    simpa only [cT, pT, Scheme.isoSpec_Spec_inv] using!
      Scheme.strictHenselizationStructuralMap_eq barT b
  have hψS : ∀ a, Spec.map (CommRingCat.ofHom ψS) ≫ cS a =
      ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).2.left := hσS
  have hψT : ∀ b, Spec.map (CommRingCat.ofHom ψT) ≫ cT b =
      ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).2.left := hσT
  have hlocalψT : IsLocalHom ψT := inferInstance
  let := hlocalψT
  refine ⟨?_, h, hhlocal, hhbase, hhres, ?_, ?_⟩
  · intro x hx
    let z : separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω := ⟨x, hx⟩
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective
      (R := Scheme.strictHenselization barS) (σS.symm z)
    have heq : ψS r = x := by
      change (σS (IsLocalRing.residue _ r)).val = x
      rw [hr]
      exact congrArg Subtype.val (σS.apply_symm_apply z)
    have heqT : ψT (h.hom r) = x :=
      (congrArg (fun q ↦ q r) hres).symm.trans heq
    exact heqT ▸ (σT (IsLocalRing.residue _ (h.hom r))).property
  · intro h' _ hh'base hh'res
    have hspec' : Spec.map (CommRingCat.ofHom ψT) ≫ Spec.map h' =
        Spec.map (CommRingCat.ofHom ψS) := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hh'res.symm
    apply Spec.map_injective
    obtain ⟨hl⟩ := (Scheme.strictHenselizationAffineProperties barS).2.2
    apply hl.hom_ext
    intro j
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv).1
    change Spec.map h' ≫ cS j.unop.unop = Spec.map h ≫ cS j.unop.unop
    apply etalePointedMapRigidity ψT (pS j.unop.unop)
    · simpa only [Category.assoc, hcS] using hh'base.trans hhbase.symm
    · simpa only [Category.assoc] using!
        (congrArg (fun q ↦ q ≫ cS j.unop.unop) hspec').trans
          (congrArg (fun q ↦ q ≫ cS j.unop.unop) hspec).symm
  · intro a b w hw hp
    change cT b ≫ w = Spec.map h ≫ cS a
    apply etalePointedMapRigidity ψT (pS a)
    · calc
        (cT b ≫ w) ≫ pS a = (cT b ≫ pT b) ≫ g := by
          simpa only [Category.assoc] using congrArg (fun q ↦ cT b ≫ q) hw
        _ = Scheme.strictLocalizationToBase barT ≫ g := by rw [hcT]
        _ = Spec.map h ≫ Scheme.strictLocalizationToBase barS := hhbase.symm
        _ = (Spec.map h ≫ cS a) ≫ pS a := by rw [Category.assoc, hcS]
    · calc
        Spec.map (CommRingCat.ofHom ψT) ≫ cT b ≫ w =
            ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).2.left ≫ w := by
          rw [← Category.assoc, hψT]
        _ = ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).2.left := hp
        _ = Spec.map (CommRingCat.ofHom ψS) ≫ cS a := (hψS a).symm
        _ = Spec.map (CommRingCat.ofHom ψT) ≫ Spec.map h ≫ cS a := by
          simpa only [Category.assoc] using!
            (congrArg (fun q ↦ q ≫ cS a) hspec).symm

end AlgebraicGeometry
