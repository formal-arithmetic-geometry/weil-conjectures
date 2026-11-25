/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselizationCore

/-! # Local-base presentation of a residue-triple colimit

Any realization of the colimit of pointed étale triples over `R` at a prime `p` is an
algebraic strict henselization of the localization `R_p`.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Any realization `C` of the colimit of pointed étale triples over `(R, p, K)` is an
algebraic strict henselization of the prime localization `R_p`, for an `R_p`-algebra structure
on `C` extending the given structural map `b : R ⟶ C`. -/
theorem etaleResidueTriples_localized_isStrictHenselization
    (R : CommRingCat.{u}) (p : Spec R)
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField p) K] [IsSepClosure ((Spec R).residueField p) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R p K
      (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K))))
    (hc : IsColimit c) (C : CommRingCat.{u}) (e : c.pt ≅ C) (b : R ⟶ C)
    (hbase : ∀ t, t.α ≫ c.ι.app t ≫ e.hom = b) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : Algebra (Localization.AtPrime p.asIdeal) L)
      (_ : IsScalarTower (Localization.AtPrime p.asIdeal)
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L)
      (_ : Algebra (Localization.AtPrime p.asIdeal) C),
      (∀ r : R, algebraMap (Localization.AtPrime p.asIdeal) C
        (algebraMap R (Localization.AtPrime p.asIdeal) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime p.asIdeal) L C := by
  obtain ⟨L, iFL, iAL, iSL, iLA, iST, iAC, hmap, hstrict⟩ :=
    etaleResidueTriples_localized_core R p K c hc C e
  let : Field L := iFL
  let : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L := iAL
  let : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L := iSL
  let : Algebra (Localization.AtPrime p.asIdeal) L := iLA
  let : IsScalarTower (Localization.AtPrime p.asIdeal)
      (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) L := iST
  let : Algebra (Localization.AtPrime p.asIdeal) C := iAC
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · intro r
    let t0 : EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)) :=
      ⟨R, 𝟙 R, inferInstance, p, by simp,
        CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K), by simp⟩
    rw [hmap r]
    exact congrArg (fun f : R ⟶ C ↦ f.hom r)
      (hbase t0)
  · exact hstrict

end AlgebraicGeometry.Scheme
