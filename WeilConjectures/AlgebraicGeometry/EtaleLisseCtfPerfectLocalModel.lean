/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedFiniteTorPerfect
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricStalkTensorConstantSingle
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Etale lisse finite-Tor perfect local model

## References

* Stacks Project, Tag 09BI
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A bounded constructible etale complex `L` over a finite commutative ring `A`, with finite Tor
amplitude and finite locally constant cohomology sheaves on a connected scheme `S`, is etale
locally isomorphic to the termwise constant complex of one bounded complex `P` of finitely
generated projective `A`-modules, the same `P` on every member of a jointly surjective etale
family. No Noetherian hypothesis on `S` is made. -/
theorem etale_lisse_ctf_perfect_local_model
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {S : Scheme.{u}} [ConnectedSpace S]
    (L : DerivedCategoryModule A S)
    (hL : DerivedCategory.isBoundedConstructible A S L)
    (hLisse : ∀ q : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj L))
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A S a b L) :
    ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n : ℤ, Module.Projective A (P.X n) ∧ Module.Finite A (P.X n)) ∧
      ∃ (I : Type u) (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ S),
        (∀ i, Etale (f i)) ∧
        Function.Surjective (fun p : Σ i, (U i : Type u) ↦ (f p.1).base p.2) ∧
        ∀ i : I,
          Nonempty (((Etale.upperStar (ModuleCat.{u + 1} A) (f i)).mapDerivedCategory).obj L ≅
            _root_.DerivedCategory.Q.obj
              (((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
  classical
  obtain ⟨c, d, _, hbound⟩ := hL.2
  obtain ⟨hmodels, _, _, hconnected⟩ :=
    finiteRing_derived_local_constancy S A L ⟨c, d, hbound⟩ hLisse
  obtain ⟨𝒱, h𝒱⟩ := hmodels
  obtain ⟨j, y, _⟩ := 𝒱.exists_eq (Classical.choice (inferInstance : Nonempty S))
  obtain ⟨E, ⟨c, d, hEbound⟩, hEfin, ⟨e⟩⟩ := h𝒱 j
  let Ω := AlgebraicClosure ((𝒱.X j).residueField y)
  let t : Spec (.of Ω) ⟶ 𝒱.X j := (𝒱.X j).algClosurePoint y
  let x : Spec (.of Ω) ⟶ S := t ≫ 𝒱.f j
  let F := (Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)
  have : F.Additive := (Scheme.pointSmallEtale x).sheafFiber_additive
  let G := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)
  have : G.Additive := (Scheme.pointSmallEtale t).sheafFiber_additive
  let C := constantSheaf (𝒱.X j).smallEtaleTopology (ModuleCat.{u + 1} A)
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let eC : (C ⋙ G).mapDerivedCategory.obj (_root_.DerivedCategory.Q.obj E) ≅
      _root_.DerivedCategory.Q.obj E :=
    (Functor.mapDerivedCategoryNatIso
      ((Scheme.pointSmallEtale t).constantSheafCompSheafFiberIso _ _)).app _ ≪≫
      (Functor.mapDerivedCategoryIdIso (ModuleCat.{u + 1} A)).app _
  let eF : F.mapDerivedCategory.obj L ≅ _root_.DerivedCategory.Q.obj E :=
    ((Functor.mapDerivedCategoryNatIso
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) (𝒱.f j) t)).app L).symm ≪≫
      ((Functor.mapDerivedCategoryCompIso _ G).app L).symm ≪≫ G.mapDerivedCategory.mapIso
        (e ≪≫ (C.mapDerivedCategoryFactors.app E).symm) ≪≫
      (Functor.mapDerivedCategoryCompIso C G).app _ ≪≫ eC
  obtain ⟨a, b, hTor⟩ := hTor
  have hTor' : DerivedCategory.hasTorAmplitudeIn A S (min a b) b L := by
    intro N q hq
    exact hTor N q (hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id)
  have hEt : _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A)
      (min a b) b (_root_.DerivedCategory.Q.obj E) := by
    intro N
    have hz (q : ℤ) (hq : q < min a b ∨ b < q) :
        IsZero ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj
          (_root_.DerivedCategory.Q.obj E ⊗
            (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj N)) := by
      have h := hTor' ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)
        q hq
      have hs := (F.map_isZero h).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app _).symm
      let eTensor := (geometricStalk_tensor_constant_single A x L N).some ≪≫
        (MonoidalCategory.tensorRight
          ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj N)).mapIso eF
      exact hs.of_iso
        ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).mapIso eTensor).symm
    exact ⟨(_root_.DerivedCategory.isGE_iff _ _).2 (fun q hq ↦ hz q (Or.inl hq)),
      (_root_.DerivedCategory.isLE_iff _ _).2 (fun q hq ↦ hz q (Or.inr hq))⟩
  have hE : ∃ c d : ℤ, E.IsStrictlyGE c ∧ E.IsStrictlyLE d ∧
      ∀ n : ℤ, Module.Finite A (E.X n) := by
    refine ⟨c, d, (E.isStrictlyGE_iff c).2 (fun n hn ↦ hEbound n (Or.inl hn)),
      (E.isStrictlyLE_iff d).2 (fun n hn ↦ hEbound n (Or.inr hn)), ?_⟩
    intro n
    have := hEfin n
    exact Module.Finite.of_finite
  obtain ⟨⟨P, hPbound, hPfin, ⟨eP⟩⟩, _⟩ :=
    _root_.DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn
      A E hE (min a b) b (min_le_right _ _) hEt
  let F' := ((Scheme.pointSmallEtale x).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} A)
  have : F'.Additive := Functor.additive_of_preserves_binary_products _
  let eF' : F'.mapDerivedCategory.obj L ≅ _root_.DerivedCategory.Q.obj P :=
    (Functor.mapDerivedCategoryNatIso
      ((Scheme.pointSmallEtale x).uliftSheafFiberIso (ModuleCat.{u + 1} A))).app L ≪≫
      eF ≪≫ eP.symm
  obtain ⟨𝒰, h𝒰⟩ := hconnected inferInstance Ω x
  refine ⟨P, min a b, b,
    (P.isStrictlyGE_iff _).2 (fun n hn ↦ hPbound n (Or.inl hn)),
    (P.isStrictlyLE_iff _).2 (fun n hn ↦ hPbound n (Or.inr hn)), hPfin,
    𝒰.I₀, 𝒰.X, 𝒰.f, fun i ↦ inferInstance, ?_, ?_⟩
  · intro s
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq s
    exact ⟨⟨i, z⟩, hz⟩
  · intro i
    let C := constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} A)
    exact ⟨(h𝒰 i).some ≪≫ C.mapDerivedCategory.mapIso eF' ≪≫
      C.mapDerivedCategoryFactors.app P⟩

end AlgebraicGeometry.Etale
