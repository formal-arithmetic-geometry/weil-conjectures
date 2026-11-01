/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementData
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-! # ProjectionRefinementInputs -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ProjectionRefinementDescent

/-- Every bounded constructible first input admits a retained origin; tensoring it
with the pullback of the finite-Tor second input remains bounded constructible.
Source: lem-sf-projection-refinement-descent, steps 1--3; Stacks 09AK, 09AL,
06YQ, 0G7E, 06YU, 07A4 and 09BQ.
(blueprint: lem-sf-projection-refinement-inputs).

Proof: extract a vanishing interval from the bounded cohomological support of K.
The finite-ring constructible-derived-origin theorem gives a bounded constructible
etale complex G and its actual comparison isomorphism. Regard G as bounded below,
retain its comparison as an EtaleOriginWitness, and use the canonical comparison
composition and the coefficient-realization unit to obtain fixed(O) isomorphic to K.
For tensor closure, realize K and L in the intrinsic coefficient category. The
proved CompactSupportFiniteProjection.domains theorem preserves the finite-Tor
predicate under the recorded pullback and gives bounded constructibility of the
tensor with that pullback. The operation datum's finitePullback comparison and
mapDerivedCategoryCompIso identify this pullback with the canonical exact pullback.
The realization units and leftDerivedUpperStarIsoMapDerivedCategory then give an
actual isomorphism from that intrinsic tensor to the realization of tensorInput.
Transport constructibility along this isomorphism. No Tor hypothesis is imposed on
K. The same interval argument works for zero objects and empty schemes. -/
theorem tensor_and_origins
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (n : ℕ) (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ K : (boundedConstructible C.l E n X).FullSubcategory,
      ∃ O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X,
        Nonempty (refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X O ≅
          K.obj)) ∧
    ∀ (K : (boundedConstructible C.l E n X).FullSubcategory)
      (L : (finiteTor C.l E n Y).FullSubcategory),
      boundedConstructible C.l E n X (tensorInput C.l E n f K.obj L.obj) := by
  classical
  let A := Padic.coefficientExtensionRing C.l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing C.l E (n + 1) (Nat.succ_pos n)
  let : TopologicalSpace (Coefficient C.l E n) := ⊥
  let : DiscreteTopology (Coefficient C.l E n) := discreteTopology_bot _
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  constructor
  · intro K
    have hK := K.property
    change intrinsicFiniteTorsionConstructible C.l E (n + 1) (Nat.succ_pos n) X
      (RX.functor.obj K.obj) at hK
    obtain ⟨lo, hlo⟩ := hK.1.bddBelow
    obtain ⟨hi, hhi⟩ := hK.1.bddAbove
    have hvan (i : ℤ) (hi' : i < min lo hi ∨ max lo hi < i) :
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (RX.functor.obj K.obj)) := by
      by_contra hz
      rcases hi' with hi' | hi'
      · exact (not_lt_of_ge (hlo hz)) (hi'.trans_le (min_le_left _ _))
      · exact (not_lt_of_ge (hhi hz)) ((le_max_right _ _).trans_lt hi')
    obtain ⟨G, ⟨eG⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1
      (RX.functor.obj K.obj)).mpr ⟨hK.2, min lo hi, max lo hi, min_le_max, hvan⟩
    obtain ⟨r, s, _, hv⟩ := G.property.2
    let Gplus : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coefficient C.l E n))) :=
      ⟨G.obj, r, (DerivedCategory.isGE_iff G.obj r).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
    let O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X :=
      ⟨(finiteCoefficientComparison X (Coefficient C.l E n)).mapDerivedCategoryPlus.obj Gplus,
        ⟨Gplus, Iso.refl _⟩⟩
    refine ⟨O, ⟨RX.functor.preimageIso ?_⟩⟩
    exact RX.functor.mapIso (refinementFixedWitnessIso X (Coefficient C.l E n) O).symm ≪≫
      ((Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} (Coefficient C.l E n)) X)
        (sfIntrinsicModuleEquivalence X A).functor).app G.obj).symm ≪≫ eG
  · intro K L
    let X' : SixFunctorSpace D :=
      ⟨Over.mk (X ↘ Spec (.of D.k)), inferInstanceAs (LocallyOfFiniteType
        (X ↘ Spec (.of D.k))), inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))⟩
    let Y' : SixFunctorSpace D :=
      ⟨Over.mk (Y ↘ Spec (.of D.k)), inferInstanceAs (LocallyOfFiniteType
        (Y ↘ Spec (.of D.k))), inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))⟩
    let f' : X' ⟶ Y' := ObjectProperty.homMk (Over.homMk f (comp_over f _))
    let Ki : sixFunctorFiniteCategory D C E (n + 1) (Nat.succ_pos n) X' :=
      ⟨RX.functor.obj K.obj, K.property⟩
    let Li : finiteTorConstructibleCategory C.l E (n + 1) (Nat.succ_pos n) Y :=
      ⟨RY.functor.obj L.obj, L.property⟩
    let P := (S.finite.pull f').obj ⟨Li.obj, Li.property.1⟩
    have hP := (CompactSupportFiniteProjection.domains S.toSixFunctorFiniteOperations).2 f' Li
    have ht := (CompactSupportFiniteProjection.domains S.toSixFunctorFiniteOperations).1
      X' Ki ⟨P.obj, hP⟩
    let U := AlgebraicGeometry.ProEtale.upperStar
      (ModuleCat.{u + 1} (Coefficient C.l E n)) f
    let e : P.obj ≅ RX.functor.obj
        (U.mapDerivedCategory.obj (RY.inverse.obj Li.obj)) :=
      (S.finitePullback f').app ⟨Li.obj, Li.property.1⟩ ≪≫
        ((Functor.mapDerivedCategoryCompIso
          (sfIntrinsicModuleEquivalence Y A).inverse
          (U ⋙ (sfIntrinsicModuleEquivalence X A).functor)) ≪≫
            Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)).app Li.obj
    let eP : RX.inverse.obj P.obj ≅ (ProperOpenPull (Coefficient C.l E n) f).obj L.obj :=
      RX.inverse.mapIso e ≪≫ RX.unitIso.symm.app _ ≪≫
        U.mapDerivedCategory.mapIso (RY.unitIso.symm.app L.obj) ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (Coefficient C.l E n)) f).symm.app L.obj
    let eT := RX.functor.mapIso
      (((ProperOpenTensor (Coefficient C.l E n) X).mapIso
        (RX.unitIso.symm.app K.obj)).app (RX.inverse.obj P.obj) ≪≫
          ((ProperOpenTensor (Coefficient C.l E n) X).obj K.obj).mapIso eP)
    exact (finiteTorsionConstructible D C.l C.different E (n + 1) (Nat.succ_pos n) X).prop_of_iso
      eT ht

end WeilConjectures.ProjectionRefinementDescent
