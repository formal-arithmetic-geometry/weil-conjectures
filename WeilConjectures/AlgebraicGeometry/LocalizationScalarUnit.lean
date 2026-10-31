/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteClosedShriek
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import all WeilConjectures.AlgebraicGeometry.FiniteCompactSupportConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage

/-! # Scalar transport of the support triangle and the open unit

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-finite-closed-shriek, proof paragraphs 1–2
(blueprint: lem-coef-localization-scalar-unit).

The fixed-coefficient presentation is the actual small pro-etale derived category.
The previously defined scalar, counit, and pullback-comparison constructions are reused.
No closed-shriek coefficient-change theorem is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem scalarPullback_comparison
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {V X : Scheme.{u}} (j : V ⟶ X) :
    finiteClosedScalarPullIso φ j = ProEtale.scalarPullbackProEtaleIso.{u} φ j := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} V.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let a := ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let b := ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let x := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology X) φ)
  let v := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology V) φ)
  let k := ProEtale.scalarPullbackReverseProEtale.{u} φ j
  have hk : IsIso k := (ProEtale.scalarPullbackReverse_isIso.{u} φ j).1
  have h : (conjugateIsoEquiv (x.comp b) (a.comp v)) (asIso k) =
      (ProEtale.fixedScalarRestrictionDirectImage.{u} φ j).symm := by
    apply Iso.ext
    change conjugateEquiv (x.comp b) (a.comp v) k =
      ProEtale.fixedScalarRestrictionDirectImageMap.{u} φ j
    rw [← iterated_mateEquiv_conjugateEquiv]
    change (mateEquiv b a ((mateEquiv x v)
      ((mateEquiv x v).symm
        (TwoSquare.mk _ _ _ _ (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ j).hom)))).natTrans
      = _
    rw [Equiv.apply_symm_apply]
    rfl
  have he : (conjugateIsoEquiv (x.comp b) (a.comp v)).symm
      (ProEtale.fixedScalarRestrictionDirectImage.{u} φ j).symm = asIso k := by
    rw [← h, Equiv.symm_apply_apply]
  suffices (finiteClosedScalarPullIso φ j).symm =
      (ProEtale.scalarPullbackProEtaleIso.{u} φ j).symm by
    simpa using congrArg Iso.symm this
  change (conjugateIsoEquiv (x.comp b) (a.comp v)).symm
      (ProEtale.fixedScalarRestrictionDirectImage.{u} φ j).symm = asIso k
  exact he

private theorem closed_localization
    (A : Type u) [CommRing A] [Finite A] {k : Type u} [Field k]
    {Z U X : Scheme.{u}} [CompactSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (N : ℕ) (hN : (N : k) ≠ 0)
    (hA : (N : ULift.{u + 1, u} A) = 0)
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : finiteClosedDerived X A)
    (hM : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X M) :
    ∃ δ, Triangle.mk (finiteClosedCounit A i M)
      ((ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app M) δ ∈
      distTriang (finiteClosedDerived X A) := by
  let : HasCompactification i := (Compactification.ofIsProper i).hasCompactification
  let adj := ProEtale.derivedLowerStarClosedUpperShriekAdjunction
    (R := ULift.{u + 1, u} A) i j hij
  have hE := (ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj
    i j N hN hA s hij hM).plusEtaleOrigin
  have hE' := ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj i hM.plusEtaleOrigin.plus
  let q := fun {P} (hP : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z P) ↦
    ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek
      i j hij hP hM.plusEtaleOrigin.plus
  let e : (ProEtale.closedUpperShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i j).rightDerivedFunctor.obj M ≅
      (ProEtale.rightDerivedUpperShriek (ULift.{u + 1, u} A) i).obj M :=
    ⟨q hE (𝟙 _), (q hE').symm (𝟙 _), by
      apply (q hE).injective
      rw [ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek_naturality
        i j hij hE hE', Equiv.apply_symm_apply, Category.comp_id], by
      rw [← ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek_naturality
        i j hij hE' hE, Category.comp_id]
      exact Equiv.apply_symm_apply (q hE') _⟩
  have hc : (finiteClosedPush A i).map e.hom ≫ finiteClosedCounit A i M =
      adj.counit.app M := by
    let θ := ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i
    have he : (ProEtale.rightDerivedLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).map e.hom ≫
          ProEtale.rightDerivedUpperShriekCounit i M hM.plusEtaleOrigin.plus =
        θ.hom.app _ ≫ adj.counit.app M := by
      change (ProEtale.rightDerivedUpperShriekHomEquiv
        i hE hM.plusEtaleOrigin.plus).symm ((q hE) (𝟙 _)) = _
      dsimp only [q, ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek,
        Equiv.trans_apply]
      rw [Equiv.symm_apply_apply]
      simp only [Iso.homFromEquiv_symm_apply, Adjunction.homEquiv_counit,
        CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    simp only [finiteClosedCounit, dif_pos (inferInstance : CompactSpace X),
      dif_pos hM.plusEtaleOrigin.plus]
    erw [← Category.assoc, θ.inv.naturality e.hom, Category.assoc, he]
    simp
  obtain ⟨δ, hδ⟩ :=
    ProEtale.exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit i j hij M
  refine ⟨δ ≫ (shiftFunctor _ (1 : ℤ)).map ((finiteClosedPush A i).map e.hom), ?_⟩
  apply isomorphic_distinguished _ hδ _
  refine Triangle.isoMk _ _ ((finiteClosedPush A i).mapIso e).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change finiteClosedCounit A i M ≫ 𝟙 M =
      (finiteClosedPush A i).map e.inv ≫ adj.counit.app M
    rw [← hc]
    erw [← Category.assoc, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · simp
  · dsimp
    change (δ ≫ _) ≫ _ = 𝟙 _ ≫ δ
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

private theorem coefficient_localization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ)
    {k : Type u} [Field k] (hl : IsUnit (l : k))
    {Z U X : Scheme.{u}} [CompactSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (M : finiteClosedDerived X (finiteClosedCoefficient l E m))
    (hM : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X M) :
    ∃ δ, Triangle.mk (finiteClosedCounit (finiteClosedCoefficient l E m) i M)
      ((ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m))) j).unit.app M)
      δ ∈ distTriang (finiteClosedDerived X (finiteClosedCoefficient l E m)) := by
  have hbc := (intrinsic_bc_realization_iff l E (m + 1) (Nat.succ_pos m) X M).1 hM.1
  let := coefficient_has_invertible_exponent l E k hl (m + 1) (Nat.succ_pos m)
  obtain ⟨N, _, hA, hN⟩ := HasInvertibleExponent.exists_isUnit_natCast
    (Λ := ULift.{u + 1, u} (finiteClosedCoefficient l E m)) (X := Spec (.of k))
  have hNk : (N : k) ≠ 0 := by
    have h := hN.map (Scheme.ΓSpecIso (.of k)).hom.hom
    simpa only [map_natCast] using h.ne_zero
  have hic : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hij]
    exact isCompl_compl
  exact closed_localization _ i j N hNk hA s hic M hbc

/-- Derived scalar extension transports the localization triangle, and the specified
ordinary coefficient comparison preserves the open unit.

Source: Weil blueprint, lem-coef-finite-closed-shriek, proof paragraphs 1–2
(blueprint: lem-coef-localization-scalar-unit).

Proof: Finite type over the field makes X and U Noetherian. Use the proved
fixed-module finite-stage localization theorem. Its support adjoint is identified
with the specified exceptional functor by the natural Hom bijection; the comparison
is constructed from identities, and the inverse-transpose formula proves that it
preserves the exceptional counit. Transport the support triangle along this
comparison. The intrinsic realization equivalence supplies bounded constructibility,
and the coefficient ring has an exponent invertible in the base field.

Derived restriction of scalars is triangulated. Give its left adjoint the induced
shift comparison and apply the triangulated-left-adjoint theorem to transport the
A-triangle. Apply the finite direct-image theorem to the stipulated etale origins,
then transport its isomorphisms along the given object isomorphisms.

Finally, the conjugate-adjunction and iterated-mate identities identify the published
pullback comparison with the fixed-module comparison used to define the coefficient
map. Apply unit_mateEquiv and cancel the comparison with its inverse -/
theorem coefficientLocalizationScalarUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (finiteClosedCoefficient l E m) →+*
      ULift.{u + 1, u} (finiteClosedCoefficient l L n))
    (X Z U : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    (_hij : Set.range j.left.base = (Set.range i.left.base)ᶜ)
    (M : finiteClosedDerived X.left (finiteClosedCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X.left M)
    (_hMB : finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) X.left
      ((finiteClosedScalar φ X.left).obj M))
    (_hNAB : finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) Z.left
      ((finiteClosedScalar φ Z.left).obj
        ((finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M)))
    (_hNB : finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) Z.left
      ((finiteClosedExceptional (finiteClosedCoefficient l L n) i.left).obj
        ((finiteClosedScalar φ X.left).obj M)))
    (_hNA : ∃ K : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (finiteClosedCoefficient l E m)) Z.left,
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) Z.left K ∧
      Nonempty (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
          Z.left).mapDerivedCategory.obj K) ≅
        (finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M))
    (_hJM : ∃ K : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (finiteClosedCoefficient l E m)) U.left,
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) U.left K ∧
      Nonempty (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
          U.left).mapDerivedCategory.obj K) ≅
        (finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)) :
    IsNoetherian U.left ∧ QuasiCompact j.left ∧ IsSeparated j.left ∧
    LocallyOfFiniteType j.left ∧
    (∃ δ,
      Triangle.mk
        ((finiteClosedScalar φ X.left).map
          (finiteClosedCounit (finiteClosedCoefficient l E m) i.left M))
        ((finiteClosedScalar φ X.left).map
          ((ProEtale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
              j.left).unit.app M)) δ ∈
        distTriang (finiteClosedDerived X.left (finiteClosedCoefficient l L n))) ∧
    (∃ δ,
      Triangle.mk
        (finiteClosedCounit (finiteClosedCoefficient l L n) i.left
          ((finiteClosedScalar φ X.left).obj M))
        ((ProEtale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l L n)))
            j.left).unit.app ((finiteClosedScalar φ X.left).obj M)) δ ∈
        distTriang (finiteClosedDerived X.left (finiteClosedCoefficient l L n))) ∧
    IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
      ((finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M)) ∧
    IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ j.left
      ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)) ∧
    (finiteClosedScalar φ X.left).map
        ((ProEtale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
            j.left).unit.app M) ≫
      ProEtale.finiteCoefficientChangeDirectImageMap φ j.left
        ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M) ≫
      (finiteClosedPush (finiteClosedCoefficient l L n) j.left).map
        ((finiteClosedScalarPullIso φ j.left).inv.app M) =
      (ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l L n)))
          j.left).unit.app ((finiteClosedScalar φ X.left).obj M) := by
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  have : IsNoetherian U.left := ⟨⟩
  have : QuasiCompact j.left := inferInstance
  have : IsSeparated j.left := inferInstance
  have : LocallyOfFiniteType j.left := inferInstance
  have hlk : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have hc : Fintype.card D.k₀ = D.p ^ D.a := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
    have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    apply Ne.isUnit
    intro h
    have hp : D.p ∣ l := (CharP.cast_eq_zero_iff D.k D.p l).1 h
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hp).symm
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · let : EssentiallySmall.{u + 1} X.left.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    obtain ⟨δ, hδ⟩ := coefficient_localization l E m hlk i.left j.left X.hom _hij M _hM
    let r : finiteClosedDerived X.left (finiteClosedCoefficient l L n) ⥤
        finiteClosedDerived X.left (finiteClosedCoefficient l E m) :=
      Sheaf.derivedRestrictScalars.{u} (ProEt.topology X.left) φ
    let a : finiteClosedScalar φ X.left ⊣ r := Adjunction.ofIsRightAdjoint _
    let := a.leftAdjointCommShift ℤ
    have := a.commShift_of_rightAdjoint ℤ
    have : (finiteClosedScalar φ X.left).IsTriangulated := a.isTriangulated_leftAdjoint
    let T : Triangle (finiteClosedDerived X.left (finiteClosedCoefficient l E m)) :=
      Triangle.mk (finiteClosedCounit (finiteClosedCoefficient l E m) i.left M)
        ((ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
            j.left).unit.app M) δ
    have hT : T ∈ distTriang (finiteClosedDerived X.left (finiteClosedCoefficient l E m)) := hδ
    exact ⟨_, (finiteClosedScalar φ X.left).map_distinguished T hT⟩
  · exact coefficient_localization l L n hlk i.left j.left X.hom _hij _ _hMB
  · let : Algebra (ULift.{u + 1, u} (finiteClosedCoefficient l E m))
        (ULift.{u + 1, u} (finiteClosedCoefficient l L n)) := φ.toAlgebra
    have : Module.Finite (ULift.{u + 1, u} (finiteClosedCoefficient l E m))
        (ULift.{u + 1, u} (finiteClosedCoefficient l L n)) := Module.Finite.of_finite
    obtain ⟨K, hK, ⟨e⟩⟩ := _hNA
    have h := ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso
      D l _hl E (m + 1) (Nat.succ_pos m)
      (ULift.{u + 1, u} (finiteClosedCoefficient l L n)) Z X i K hK.1 hK.2
    have : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
            Z.left).mapDerivedCategory.obj K)) :=
      IsIso.of_isIso_comp_right _
        ((finiteClosedPush (finiteClosedCoefficient l L n) i.left).map
          ((ProEtale.pbcComparisonReduction Z.left φ).hom.app K))
    have hn := ProEtale.finiteCoefficientDirectImageMap_naturality φ i.left e.hom
    have : IsIso ((finiteClosedScalar φ X.left).map
        ((finiteClosedPush (finiteClosedCoefficient l E m) i.left).map e.hom) ≫
          ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
            ((finiteClosedExceptional (finiteClosedCoefficient l E m) i.left).obj M)) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((finiteClosedScalar φ X.left).map
        ((finiteClosedPush (finiteClosedCoefficient l E m) i.left).map e.hom)) _
  · let : Algebra (ULift.{u + 1, u} (finiteClosedCoefficient l E m))
        (ULift.{u + 1, u} (finiteClosedCoefficient l L n)) := φ.toAlgebra
    have : Module.Finite (ULift.{u + 1, u} (finiteClosedCoefficient l E m))
        (ULift.{u + 1, u} (finiteClosedCoefficient l L n)) := Module.Finite.of_finite
    obtain ⟨K, hK, ⟨e⟩⟩ := _hJM
    have h := ProEtale.finiteCoefficientDirectImageMap_etaleOrigin_isIso
      D l _hl E (m + 1) (Nat.succ_pos m)
      (ULift.{u + 1, u} (finiteClosedCoefficient l L n)) U X j K hK.1 hK.2
    have : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ j.left
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m)))
            U.left).mapDerivedCategory.obj K)) :=
      IsIso.of_isIso_comp_right _
        ((finiteClosedPush (finiteClosedCoefficient l L n) j.left).map
          ((ProEtale.pbcComparisonReduction U.left φ).hom.app K))
    have hn := ProEtale.finiteCoefficientDirectImageMap_naturality φ j.left e.hom
    have : IsIso ((finiteClosedScalar φ X.left).map
        ((finiteClosedPush (finiteClosedCoefficient l E m) j.left).map e.hom) ≫
          ProEtale.finiteCoefficientChangeDirectImageMap φ j.left
            ((finiteClosedPull (finiteClosedCoefficient l E m) j.left).obj M)) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((finiteClosedScalar φ X.left).map
        ((finiteClosedPush (finiteClosedCoefficient l E m) j.left).map e.hom)) _
  · rw [scalarPullback_comparison]
    rw [ProEtale.finiteCoefficientDirectImageMap_eq_mate]
    have h := unit_mateEquiv
      (ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l E m))) j.left)
      (ProEtale.derivedUpperStarLowerStarAdjunction.{u + 2, u}
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (finiteClosedCoefficient l L n))) j.left)
      (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso.{u} φ j.left).hom) M
    rw [← Category.assoc, h]
    simp only [TwoSquare.mk, Functor.id_obj, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    change _ ≫ (finiteClosedPush (finiteClosedCoefficient l L n) j.left).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end WeilConjectures
