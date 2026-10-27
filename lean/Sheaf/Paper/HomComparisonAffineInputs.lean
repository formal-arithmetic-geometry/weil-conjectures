/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NI and J8
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Affine charts with unchanged constructible finite-Tor inputs

Source: blueprint `thm-sf-hom-comparison-constructible.proof.md`, sentences 1--2;
Stacks Project, Tags 01T1, 01S7, 095A, 095E and 05VD
(blueprint: lem-sf-hom-comparison-affine-inputs).

The coefficient ring is canonically lifted to the established etale module universe.
Finite locally constant module sheaves use the existing stalkwise predicate; over the
finite coefficient ring its equivalence with finite constant values is the theorem
`Scheme.finite_locally_constant_module_values_iff` in `FiniteLocallyConstantModuleValues`.
Empty strata are removed by the displayed equivalence with the nonempty fibre products.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem pullback_boundedFlat {A : Type (u + 1)} [CommRing A]
    {X Y : Scheme.{u}} (j : Y ⟶ X) {a b : ℤ}
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : IsBoundedFlatComplex A a b P) :
    IsBoundedFlatComplex A a b
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact ⟨fun q hq ↦ (upperStar (ModuleCat.{u + 1} A) j).map_isZero (hP.1 q hq),
    fun q ↦ Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A) j)
      (hP.2 q)⟩

private theorem pullback_homology_zero {A : Type (u + 1)} [CommRing A]
    {X Y : Scheme.{u}} (j : Y ⟶ X) (N : DerivedCategoryModule A X) (h : ℤ)
    (hz : IsZero ((_root_.DerivedCategory.homologyFunctor _ h).obj N)) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ h).obj
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N)) := by
  exact ((upperStar (ModuleCat.{u + 1} A) j).map_isZero hz).of_iso
    (((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryHomologyFunctorIso h).app N).symm

private theorem boundedConstructible_source {A : Type (u + 1)} [CommRing A] [Finite A]
    {X : Scheme.{u}} {N : DerivedCategoryModule A X}
    (hN : DerivedCategory.isBoundedConstructible A X N) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X N := by
  obtain ⟨c, d, -, hcd⟩ := hN.2
  refine ⟨⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩, fun q ↦ ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hcd q (.inl hq)
  · exact (_root_.DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hcd q (.inr hq)
  · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hN.1 q)

private theorem pullback_boundedConstructible {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : Y ⟶ X) {N : DerivedCategoryModule A X}
    (hN : DerivedCategory.isBoundedConstructible A X N) :
    DerivedCategory.isBoundedConstructible A Y
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) := by
  constructor
  · intro q
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj N) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hN.1 q)
    have := Scheme.IsConstructibleSheaf.upperStar j
      ((_root_.DerivedCategory.homologyFunctor _ q).obj N)
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso
        (F := (upperStar (ModuleCat.{u + 1} A) j).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj N))
        (((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryHomologyFunctorIso q).app N))
  · obtain ⟨c, d, hcd, hz⟩ := hN.2
    exact ⟨c, d, hcd, fun q hq ↦ pullback_homology_zero j N q (hz q hq)⟩

private theorem finite_affine_cover (X : Scheme.{u})
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (m : ℕ) (U : Fin m → Scheme.{u}) (j : ∀ i, U i ⟶ X),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ x : X, ∃ i y, j i y = x) ∧ (IsEmpty X → m = 0) ∧
      (∀ i, IsAffine (U i) ∧ IsSeparated (j i ≫ f) ∧
        LocallyOfFiniteType (j i ≫ f) ∧ QuasiCompact (j i ≫ f)) := by
  classical
  by_cases hX : IsEmpty X
  · exact ⟨0, Fin.elim0, fun i ↦ Fin.elim0 i, (fun i ↦ Fin.elim0 i),
      fun x ↦ (hX.false x).elim, fun _ ↦ rfl, fun i ↦ Fin.elim0 i⟩
  · have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let C := X.affineCover.finiteSubcover
    let e := Fintype.equivFin C.I₀
    refine ⟨Fintype.card C.I₀, fun i ↦ C.X (e.symm i), fun i ↦ C.f (e.symm i),
      fun i ↦ inferInstance, ?_, fun h ↦ (hX h).elim, fun i ↦ ?_⟩
    · intro x
      obtain ⟨i, y, hy⟩ := C.exists_eq x
      refine ⟨e i, ?_⟩
      change ∃ y : C.X (e.symm (e i)), C.f (e.symm (e i)) y = x
      rw [e.symm_apply_apply]
      exact ⟨y, hy⟩
    · exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem pullback_stratification {A : Type (u + 1)} [CommRing A]
    {X Y : Scheme.{u}} (j : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (c : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G)
    (S : X.FiniteLocallyClosedStratification)
    (hc : ∀ k, Topology.IsConstructible (S.stratum k))
    (hF : ∀ k, Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion k)).obj F)) :
    ∃ (R : Y.FiniteLocallyClosedStratification)
      (e : Fin R.n ≃ {k : Fin S.n // Nonempty ↥(pullback (S.immersion k) j : Scheme.{u})}),
      (∀ k, R.domain k = pullback (S.immersion (e k).1) j) ∧
      (∀ k, HEq (R.immersion k) (pullback.snd (S.immersion (e k).1) j)) ∧
      (∀ k, R.stratum k = j ⁻¹' S.stratum (e k).1) ∧
      (∀ k, Topology.IsConstructible (R.stratum k)) ∧
      (∀ k, Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (R.immersion k)).obj G)) := by
  classical
  let I := {k : Fin S.n // Nonempty ↥(pullback (S.immersion k) j : Scheme.{u})}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have : ∀ k, IsImmersion (S.immersion k) := S.isImmersion
  let R : Y.FiniteLocallyClosedStratification := {
    n := Fintype.card I
    stratum := fun k ↦ j ⁻¹' S.stratum (e k).1
    isLocallyClosed_stratum := fun k ↦
      (S.isLocallyClosed_stratum (e k).1).preimage j.continuous
    iUnion_stratum_eq_univ := by
      apply Set.eq_univ_of_forall
      intro y
      have hy : j y ∈ ⋃ k, S.stratum k := by rw [S.iUnion_stratum_eq_univ]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
      have hr : y ∈ Set.range (pullback.snd (S.immersion k) j) := by
        rw [Scheme.Pullback.range_snd, S.range_immersion]
        exact hk
      obtain ⟨z, -⟩ := hr
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨k, ⟨z⟩⟩, ?_⟩
      change j y ∈ S.stratum (e (e.symm ⟨k, ⟨z⟩⟩)).1
      rw [e.apply_symm_apply]
      exact hk
    pairwise_disjoint_stratum := by
      intro i k hik
      exact (S.pairwise_disjoint_stratum (by
        intro h
        exact hik (e.injective (Subtype.ext h)))).preimage j
    domain := fun k ↦ pullback (S.immersion (e k).1) j
    immersion := fun k ↦ pullback.snd (S.immersion (e k).1) j
    isImmersion := fun k ↦ inferInstance
    range_immersion := fun k ↦ by rw [Scheme.Pullback.range_snd, S.range_immersion] }
  refine ⟨R, e, fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ ↦ rfl,
    fun k ↦ j.isConstructible_preimage (hc (e k).1), fun k ↦ ?_⟩
  have := hF (e k).1
  let p := pullback.fst (S.immersion (e k).1) j
  let q := pullback.snd (S.immersion (e k).1) j
  have := Scheme.IsFiniteLocallyConstantSheaf.upperStar p
    ((upperStar (ModuleCat.{u + 1} A) (S.immersion (e k).1)).obj F)
  apply Scheme.IsFiniteLocallyConstantSheaf.of_iso
    (F := (upperStar (ModuleCat.{u + 1} A) p).obj
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion (e k).1)).obj F))
  exact ((upperStarComp (ModuleCat.{u + 1} A) p (S.immersion (e k).1)).app F).symm ≪≫
    eqToIso (congrArg (fun m ↦ (upperStar (ModuleCat.{u + 1} A) m).obj F)
      (pullback.condition (f := S.immersion (e k).1) (g := j))) ≪≫
    (upperStarComp (ModuleCat.{u + 1} A) q j).app F ≪≫
    (upperStar (ModuleCat.{u + 1} A) q).mapIso c

/-- Finite affine charts preserve the stated input bounds, every chosen stratification,
and every bounded flat representative, with its specified induced isomorphism.
Source: blueprint Hom-comparison proof, sentences 1--2; Stacks 01T1, 01S7, 095A,
095E and 05VD (blueprint: lem-sf-hom-comparison-affine-inputs).

Proof:
1. Quasi-compactness over the affine base makes X compact. Reindex a finite subcover of
its affine open cover by Fin m. Each chart is affine over the affine base, hence separated
and quasi-compact; local finite type is preserved by the open immersion. If X is empty,
use Fin 0 explicitly.
2. Exact inverse image commutes with derived cohomology, by
`mapDerivedCategoryHomologyFunctorIso`. It preserves zero sheaves, so the given
cohomological intervals are unchanged. Convert finite-value constructibility to the
source predicate, apply `IsConstructibleSheaf.upperStar`, and transport back along the
same cohomology isomorphism.
3. For any chosen stratification, index the new strata by the nonempty fibre products,
using Fintype.equivFin. Their images are the inverse images of the old strata by
Scheme.Pullback.range_snd. They cover because every point in a stratum preimage lifts
to that fibre product. Local closedness, constructibility and disjointness pull back.
Use upperStarComp and pullback.condition to identify the stratum restrictions; finite
locally constant sheaves pull back and are invariant under these isomorphisms.
4. Convert bounded constructibility to the source-library predicate and apply
`hasTorAmplitudeIn_iff_exists_flatModel` to obtain the global model. This general
etale-site equivalence needs no invertibility hypothesis. Flatness of inverse image
follows from the geometric-stalk criterion, and zero terms stay zero. For every model
isomorphism e, take mapIso e followed by mapDerivedCategoryFactors.app P, exactly as
specified in the conclusion.
5. Apply the reverse flat-model equivalence on each chart, using its bounded
constructibility from step 2 and the restricted model from step 4. This gives precisely
the original Tor interval. -/
theorem homComparisonAffineInputs
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of D.k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (K M : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @DerivedCategory.isBoundedConstructible.{u} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) inferInstance ((Equiv.ulift : (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) ≃ Padic.coefficientExtensionRing l E
          n).finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) X K)
    (_hM : @DerivedCategory.isBoundedConstructible.{u} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) inferInstance ((Equiv.ulift : (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) ≃ Padic.coefficientExtensionRing l E
          n).finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) X M)
    (r s t v a b : ℤ) (_hab : a ≤ b)
    (_hKr : ∀ h : ℤ, h < r ∨ s < h → IsZero ((_root_.DerivedCategory.homologyFunctor (Sheaf
          X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l
          E n)))) h).obj K))
    (_hMt : ∀ h : ℤ, h < t ∨ v < h → IsZero ((_root_.DerivedCategory.homologyFunctor (Sheaf
          X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l
          E n)))) h).obj M))
    (_hTor : DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n)) X a b K) :
    (∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)))) ℤ,
      IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P ∧ Nonempty
          (K ≅ (_root_.DerivedCategory.Q).obj P)) ∧
    ∃ (m : ℕ) (U : Fin m → Scheme.{u}) (j : ∀ i : Fin m, U i ⟶ X),
      (∀ i : Fin m, IsOpenImmersion (j i)) ∧
      (∀ x : X, ∃ (i : Fin m) (y : U i), j i y = x) ∧
      (IsEmpty X → m = 0) ∧
      (∀ i : Fin m, IsAffine (U i) ∧ IsSeparated (j i ≫ f) ∧
        LocallyOfFiniteType (j i ≫ f) ∧ QuasiCompact (j i ≫ f)) ∧
      (∀ i : Fin m,
        (@DerivedCategory.isBoundedConstructible.{u} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) inferInstance ((Equiv.ulift : (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) ≃ Padic.coefficientExtensionRing l E
          n).finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) (U i)
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n))) (j i)).mapDerivedCategory.obj K)) ∧
        (@DerivedCategory.isBoundedConstructible.{u} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) inferInstance ((Equiv.ulift : (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)) ≃ Padic.coefficientExtensionRing l E
          n).finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)) (U i)
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n))) (j i)).mapDerivedCategory.obj M)) ∧
        (∀ h : ℤ, h < r ∨ s < h → IsZero ((_root_.DerivedCategory.homologyFunctor (Sheaf (U
          i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing
          l E n)))) h).obj ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) (j i)).mapDerivedCategory.obj K))) ∧
        (∀ h : ℤ, h < t ∨ v < h → IsZero ((_root_.DerivedCategory.homologyFunctor (Sheaf (U
          i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing
          l E n)))) h).obj ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) (j i)).mapDerivedCategory.obj M))) ∧
        DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))
          (U i) a b ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) (j i)).mapDerivedCategory.obj K)) ∧
      (∀ (i : Fin m) (N : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n)) X),
        N = K ∨ N = M → ∀ (h : ℤ) (S : X.FiniteLocallyClosedStratification),
        (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) →
        (∀ k : Fin S.n, Scheme.IsFiniteLocallyConstantSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n))) (S.immersion k)).obj
            ((_root_.DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u +
          1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) h).obj N))) →
        ∃ (R : (U i).FiniteLocallyClosedStratification)
          (e : Fin R.n ≃
            {k : Fin S.n // Nonempty ↥(pullback (S.immersion k) (j i) : Scheme.{u})}),
          (∀ k : Fin R.n,
            R.domain k = pullback (S.immersion (e k).1) (j i)) ∧
          (∀ k : Fin R.n,
            HEq (R.immersion k) (pullback.snd (S.immersion (e k).1) (j i))) ∧
          (∀ k : Fin R.n, R.stratum k = (j i) ⁻¹' S.stratum (e k).1) ∧
          (∀ k : Fin R.n, Topology.IsConstructible (R.stratum k)) ∧
          (∀ k : Fin R.n, Scheme.IsFiniteLocallyConstantSheaf
            ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l
          E n))) (R.immersion k)).obj
              ((_root_.DerivedCategory.homologyFunctor (Sheaf (U i).smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))) h).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n))) (j i)).mapDerivedCategory.obj N))))) ∧
      (∀ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n)))) ℤ,
        IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b P → ∀ (e :
          K ≅ (_root_.DerivedCategory.Q).obj P) (i : Fin m),
        ∃ eU : ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing
          l E n))) (j i)).mapDerivedCategory.obj K) ≅
            (_root_.DerivedCategory.Q).obj (((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) (j i)).mapHomologicalComplex (ComplexShape.up
          ℤ)).obj P),
          IsBoundedFlatComplex (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) a b
          (((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E
          n))) (j i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          eU = (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing
          l E n))) (j i)).mapDerivedCategory.mapIso e ≪≫
            ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l
          E n))) (j i)).mapDerivedCategoryFactors.app P)) := by
  classical
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  have : Finite A := Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n hn)
  have hmodel := (hasTorAmplitudeIn_iff_exists_flatModel A a b _hab K
    (boundedConstructible_source _hK)).mp _hTor
  obtain ⟨m, U, j, hj, hcover, hempty, hU⟩ := finite_affine_cover X f
  refine ⟨hmodel, m, U, j, hj, hcover, hempty, hU, ?_, ?_, ?_⟩
  · intro i
    have hK := pullback_boundedConstructible (j i) _hK
    have hM := pullback_boundedConstructible (j i) _hM
    refine ⟨hK, hM, fun h hh ↦ pullback_homology_zero (j i) K h (_hKr h hh),
      fun h hh ↦ pullback_homology_zero (j i) M h (_hMt h hh), ?_⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hmodel
    apply (hasTorAmplitudeIn_iff_exists_flatModel A a b _hab _
      (boundedConstructible_source hK)).mpr
    exact ⟨_, pullback_boundedFlat (j i) P hP,
      ⟨(upperStar (ModuleCat.{u + 1} A) (j i)).mapDerivedCategory.mapIso e ≪≫
        (upperStar (ModuleCat.{u + 1} A) (j i)).mapDerivedCategoryFactors.app P⟩⟩
  · intro i N _ h S hc hF
    exact pullback_stratification (j i) _ _
      (((upperStar (ModuleCat.{u + 1} A) (j i)).mapDerivedCategoryHomologyFunctorIso h).app N)
      S hc hF
  · intro P hP e i
    exact ⟨_, pullback_boundedFlat (j i) P hP, rfl⟩

end AlgebraicGeometry.Etale
