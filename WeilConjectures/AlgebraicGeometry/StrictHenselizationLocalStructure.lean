/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples

/-! # Local structure of the affine pointed-neighbourhood colimit

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The chosen coordinate-ring colimit is strictly henselian.
-/
theorem strictHenselizationLocalStructure
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselizationRing barY) := by
  classical
  obtain ⟨A, i, hi, hx, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := barY (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hrange : Set.range barY ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hx
  let xU := IsOpenImmersion.lift i barY hrange
  have hfac : xU ≫ i = barY := IsOpenImmersion.lift_fac i barY hrange
  let p := (Scheme.SpecToEquivOfField Ω (Spec A) xU).1
  let F := (Spec A).residueField p
  let e := (Scheme.SpecToEquivOfField Ω (Spec A) xU).2
  let : Algebra F Ω := e.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, _, _, _, E, δ, _, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩, r, s, _, _⟩ :=
    Scheme.etale_local_ring_triples Y Ω A i xU
  obtain ⟨_, c, ⟨hc⟩, hlocal, ρ, ψ, _, _, _, _, _, _, _, hstrict⟩ :=
    Scheme.strictHenselization_triples A p K
  let := hlocal
  let := hstrict
  let Nall := (Scheme.pointSmallEtale (xU ≫ i)).fiber.Elements
  let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
  let D := (P.ι ⋙ Functor.Elements.π (Scheme.pointSmallEtale (xU ≫ i)).fiber ⋙
    Scheme.Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
  let : HasColimit D := ⟨⟨cn, hcn⟩⟩
  let incl := Scheme.strictHenselizationAffineInclusion (xU ≫ i)
  let : incl.IsEquivalence :=
    Scheme.strictHenselizationAffineInclusion_isEquivalence (xU ≫ i)
  let rep := (equivSmallModel.{v}
    (Scheme.strictHenselizationNeighbourhoods (xU ≫ i))).inverse
  let q := (rep ⋙ incl).op
  let cmp : Scheme.strictHenselizationRing (xU ≫ i) ≅ cn.pt :=
    (HasColimit.isoOfEquivalence q.asEquivalence (Iso.refl _)) ≪≫
      colimit.isoColimitCocone ⟨cn, hcn⟩
  let ringIso : Scheme.strictHenselizationRing (xU ≫ i) ≅ c.pt :=
    cmp ≪≫ s ≪≫ hct.coconePointUniqueUpToIso hc
  let ringEquiv := ringIso.symm.commRingCatIsoToRingEquiv
  have hl := ringEquiv.isLocalRing
  have hs := IsStrictlyHenselianLocalRing.of_ringEquiv ringEquiv
  exact hfac ▸ (show ∃ (_ : IsLocalRing
    (Scheme.strictHenselizationRing (xU ≫ i))),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselizationRing (xU ≫ i)) from ⟨hl, hs⟩)

end AlgebraicGeometry
