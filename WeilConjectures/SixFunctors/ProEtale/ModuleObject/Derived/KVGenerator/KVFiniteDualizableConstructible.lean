/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

import all WeilConjectures.CategoryTheory.FiniteAdmissibleBrownFromCD
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Finite coefficient dualizable objects are constructible of finite Tor amplitude

Source: the generator calculation, step 1, of sk-thm-sf-kunneth-verdier;
Stacks Project, Tag 08JJ, and the finite-discrete coefficient encoding.
(blueprint: lem-sf-kv-finite-dualizable-constructible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator

/-- Over finite discrete coefficients, every dualizable complex on a Noetherian scheme
has bounded constant-model constructible cohomology and finite Tor amplitude.
Source: sk-thm-sf-kunneth-verdier.proof.md, generator calculation, step 1;
Stacks Project, Tag 08JJ
(blueprint: lem-sf-kv-finite-dualizable-constructible).

Proof: lift the finite coefficient ring to the scheme universe and restrict scalars
along its specified isomorphism. This is an exact strong monoidal equivalence, so it
preserves dualizability. Apply the normalized finite-discrete encoding, another exact
strong monoidal equivalence. The ordinary finite-coefficient perfectness theorem puts
its image in Dctf. The encoding's constructibility and Tor comparisons reflect this
membership. Finally restrict along the inverse coefficient isomorphism and use the
composition isomorphism of scalar restriction to return to the original complex.
No positive rank, nonzero coefficient ring, or nonempty scheme is assumed. -/
theorem finite_dualizable_mem
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (A₀ : Type) [CommRing A₀] [Finite A₀] [TopologicalSpace A₀]
    [DiscreteTopology A₀] [IsTopologicalRing A₀]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} A₀))
    (X : Scheme.{u}) [IsNoetherian X]
    (K : _root_.DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : IsDualizable K) :
    (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) K := by
  classical
  obtain ⟨j⟩ := CategoryTheory.finiteCoefficientLiftIso.{u} A₀
  let e' := e ≪≫ j
  let B := ULift.{u} A₀
  let Λ' := Profinite.continuousCoefficientRingObj B
  let φ : condensedRingObj Λ' X ⟶ condensedRingObj Λ X :=
    (upperStarFromPoint X).map e'.inv.hom
  let ψ : condensedRingObj Λ X ⟶ condensedRingObj Λ' X :=
    (upperStarFromPoint X).map e'.hom.hom
  have : IsIso e'.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e'.inv))
  have : IsIso φ := inferInstanceAs (IsIso ((upperStarFromPoint X).map e'.inv.hom))
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ψ
  have : F.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso φ).functor.IsEquivalence
  let : F.mapDerivedCategory.Monoidal :=
    ExactMonoidalEquivalenceDerived.derivedEquivalenceMonoidal F
  have hFK : IsDualizable (F.mapDerivedCategory.obj K) := hK.map F.mapDerivedCategory
  obtain ⟨E, hE, _⟩ := FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence B
  obtain ⟨hm, _, _, _, hc, _⟩ := hE X
  obtain ⟨hm⟩ := hm
  let := hm
  have hfixed := hFK.map (E X).fixedDerived.functor
  have hord := ProEtale.DerivedCategory.constructibleFiniteTor_of_isDualizable
    (ULift.{u + 1} B) hfixed
  have hctf := (hc _).mpr ((CategoryTheory.ordinary_ctf_iff B X _).mpr hord)
  have hback := constantModelCtf_coefficientIso e'.symm X
    ⟨F.mapDerivedCategory.obj K, hctf⟩
  have he : ψ ≫ φ = 𝟙 _ := by
    dsimp only [ψ, φ]
    rw [← Functor.map_comp]
    change (upperStarFromPoint X).map ((Mon.forget _).map (e'.hom ≫ e'.inv)) = _
    simp only [Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  let c : F ⋙ G ≅ 𝟭 _ :=
    (Mod.comapComp ψ φ).symm ≪≫ Mod.comapCongr he ≪≫ Mod.comapId _
  let d : G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅ K :=
    (Functor.mapDerivedCategoryCompIso F G).symm.app K ≪≫
      (Functor.mapDerivedCategoryNatIso c).app K ≪≫
      (Functor.mapDerivedCategoryIdIso _).app K
  let : (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  exact ⟨(constantModelBoundedConstructible Λ X).prop_of_iso d hback.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso d hback.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator
