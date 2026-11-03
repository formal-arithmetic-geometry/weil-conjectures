/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Triangulated bounded constructibility

Source: current blueprint, internal-Hom stability proof, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing

namespace AdmissibleTriangulated

private instance pointMod_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : ((upperStarFromPoint X).mapMod Λ).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts ((upperStarFromPoint X).mapMod Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

-- Zero is represented by the rank-zero presentation on the identity cover.
private theorem localModel_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

private theorem constructible_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : IsConstantModelConstructible Λ X (0 : Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  have hstrat (T : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
      (hM : IsZero M) : IsFiniteConstantStratified Λ T M := by
    refine ⟨Scheme.Stratification.trivial T, fun a ↦ ?_⟩
    exact localModel_zero Λ _ _ ((upperStar Λ _).map_isZero hM)
  classical
  unfold IsConstantModelConstructible
  split
  · exact hstrat X _ (isZero_zero _)
  · exact fun U _ ↦ hstrat _ _ ((upperStar Λ U.ι).map_isZero (isZero_zero _))

-- Apply the weak Serre cohomology theorem to this precise constructibility predicate.
private theorem triangulated_of_serre
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (hk : ∀ M N, ∀ f : M ⟶ N, IsConstantModelConstructible Λ X M →
      IsConstantModelConstructible Λ X N →
      IsConstantModelConstructible Λ X (kernel f) ∧
      IsConstantModelConstructible Λ X (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), S.ShortExact → IsConstantModelConstructible Λ X S.X₁ →
      IsConstantModelConstructible Λ X S.X₃ → IsConstantModelConstructible Λ X S.X₂) :
    (constantModelBoundedConstructible Λ X).IsTriangulated := by
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  have : P.ContainsZero := ⟨0, isZero_zero _, constructible_zero Λ X⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hlim)
      (hk _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hlim)
      (hk _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ he _ hS h1 h3⟩
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (cohomology_in_weak_serre_subcategory P).1
  change (DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
    ).IsTriangulated
  infer_instance

-- Cover index universes are the only difference between these fixed-scalar predicates.

private theorem ordinary_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryConstructible A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [FiniteDiscreteOrdinary.ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

-- This scalar-universe comparison is also used in FiniteCoefficientSerreIndHeart.

/-- Lifting a finite discrete coefficient carrier preserves its condensed ring object. -/
private theorem finiteCoefficientLiftIso (A : Type) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} A))) := by
  let ei : A ≃+* ULift.{u} A := ULift.ringEquiv.symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨Mon.mkIso ea⟩

private theorem finite_case (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X
      ).IsTriangulated := by
  classical
  let e := (FiniteDiscreteOrdinary.encoding_exists A X).some
  let F := e.fixedDerived.functor
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))) := IsConstructible (ULift.{u + 1} A)
  have : P.IsClosedUnderIsomorphisms := ⟨fun i h ↦ isConstructible_of_iso i h⟩
  let Z := (HasZeroObject.zero
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))).choose
  have hz : IsZero Z := (HasZeroObject.zero (C :=
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))).choose_spec
  have : IsConstructibleSheaf Z := IsConstructibleSheaf.of_isZero hz
  have : P.ContainsZero := ⟨(comparisonUpperStar _ X).obj Z,
    Functor.map_isZero _ hz, isConstructible_comparisonUpperStar_obj Z⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hlim)
      (Scheme.CoefficientSerre.fixed_kernel_cokernel X _ _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hlim, hFG⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hlim)
      (Scheme.CoefficientSerre.fixed_kernel_cokernel X _ _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions :=
    ⟨fun hS h1 h3 ↦ Scheme.CoefficientSerre.fixed_extension X _ _ hS h1 h3⟩
  have : (DerivedCategory.homologyProperty P).IsTriangulated :=
    (cohomology_in_weak_serre_subcategory P).1
  let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have : Q.IsTriangulated := inferInstance
  have : Q.IsClosedUnderIsomorphisms := inferInstance
  have hQ : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj A) X =
      Q.inverseImage F := by
    funext K
    apply propext
    rw [(FiniteDiscreteOrdinary.encoding_constructibility A X e).2 K]
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr Iff.rfl
    exact forall_congr' fun n ↦ ordinary_iff A X _
  have : F.IsTriangulated := by
    change (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  rw [hQ]
  infer_instance

private theorem coefficient_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (h : (constantModelBoundedConstructible Λ' X).IsTriangulated) :
    (constantModelBoundedConstructible Λ X).IsTriangulated := by
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).isEquivalence_functor
  have : (constantModelBoundedConstructible Λ' X).IsTriangulated := h
  have : (constantModelBoundedConstructible Λ' X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
  have heq : constantModelBoundedConstructible Λ X =
      (constantModelBoundedConstructible Λ' X).inverseImage F.mapDerivedCategory := by
    funext K
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    refine and_congr
      ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩ ?_
    apply forall_congr'
    intro n
    exact (constantModel_comap_iff φ X _).symm.trans
      ⟨constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K),
        constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm⟩
  rw [heq]
  infer_instance

/-- Bounded constant-model constructibility is triangulated for every admissible coefficient.
Source: internal-Hom stability proof, Step 2
(blueprint: lem-sfb-admissible-bounded-constructible-triangulated).

Proof: A finite coefficient ring is Noetherian. Its constructible sheaves form a weak
Serre subcategory, and the bounded derived cohomology property is triangulated.
For integral coefficients use their constant-model weak Serre closure, and for rational finite
extensions and the finite-subextension-valued algebraic closure use the coefficient-heart
triangulated theorem. The base rings are the cases E = Q_l. Transport these assertions
through the monoid-object coefficient isomorphism in admissibility: scalar restriction
along an isomorphism is an exact equivalence, preserves finite constant presentations,
and commutes with homology, shifts and triangles. This gives precisely the original
coefficient ring, including its actual multiplication. The zero object and the empty
scheme are included; no nonzero coefficient or nonempty scheme is required. -/
theorem admissible_boundedConstructible_isTriangulated
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (constantModelBoundedConstructible Λ X).IsTriangulated  := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  have hi (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X
        ).IsTriangulated := by
    obtain ⟨hk, he⟩ := isConstantModelConstructible_serre_padicIntegers X ℓ E
    exact AdmissibleTriangulated.triangulated_of_serre _ X hk he
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ℓ
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
    have : Finite A := hfin
    obtain ⟨j⟩ := AdmissibleTriangulated.finiteCoefficientLiftIso.{u} A
    exact AdmissibleTriangulated.coefficient_iso (e ≪≫ j) X
      (AdmissibleTriangulated.finite_case (ULift.{u} A) X)
  · obtain ⟨e⟩ := h
    exact AdmissibleTriangulated.coefficient_iso (e ≪≫ zIso) X (hi E₀)
  · obtain ⟨e⟩ := h
    exact AdmissibleTriangulated.coefficient_iso (e ≪≫ qIso) X
      ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E₀).2.1
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact AdmissibleTriangulated.coefficient_iso e X
      ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).2.1
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact AdmissibleTriangulated.coefficient_iso e X (hi E)
  · obtain ⟨e⟩ := h
    exact AdmissibleTriangulated.coefficient_iso e X
      (constantModelBoundedConstructible_field_triangulated ℓ X).2.2.1

end AdmissibleTriangulated

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
