/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Paper.ProEtaleConstructibleExactClosure
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Data.Int.Interval
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Bounded constructible pro-etale complexes form a triangulated subcategory

Source: Stacks Project, Tags 09AL, 09B5 and 06UQ; Weil blueprint,
`def-weil-finite-torsion-constructibility`
(blueprint: lem-weil-proetale-dbc-triangulated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical constant-coefficient inverse-image comparison is invertible.
Source: Stacks Project, Tag 0H7J, uniqueness of the constant-sheaf adjunction
(blueprint: lem-pur-proetale-constant-coefficient-comparison). -/
theorem constantComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : IsIso (proEtaleCoefficientInverseImageMap f A) := by
  let D := CommRingCat.{u + 1}
  let J := ProEt.topology Y
  let K := ProEt.topology X
  let G := proEtaleBaseChange f
  let T := ⊤_ Y.ProEt
  have hT : IsTerminal T := terminalIsTerminal
  have hGT : IsTerminal (G.obj T) := hT.isTerminalObj G T
  let adj := ((constantSheafAdj J D hT).comp (proEtaleSheafAdjunction f D)).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso D J K (Opposite.op T))
  let adj' := constantSheafAdj K D hGT
  let B := CommRingCat.of (ULift.{u + 1, u} A)
  have h : (adj.leftAdjointUniq adj').hom.app B =
      proEtaleCoefficientInverseImageMap f A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj, Adjunction.homEquiv_ofNatIsoRight_apply]
    change adj'.unit.app B =
      (constantSheafAdj J D hT).homEquiv B _
        ((proEtaleSheafAdjunction f D).homEquiv _ _
          (proEtaleConstantInverseImageMap f D B)) ≫ _
    change _ = (constantSheafAdj J D hT).homEquiv B _
      ((proEtaleSheafAdjunction f D).homEquiv _ _
        (((proEtaleSheafAdjunction f D).homEquiv _ _).symm
          (proEtaleConstantDirectImageMap f D B))) ≫ _
    rw [Equiv.apply_symm_apply]
    rw [constantSheafAdj_homEquiv_apply]
    have hu : adj'.unit.app B =
        (toSheafify K ((Functor.const X.ProEtᵒᵖ).obj B)).app
          (Opposite.op (G.obj T)) := by
      simp [adj', constantSheafAdj, Adjunction.comp]
      rfl
    rw [hu]
    change _ = (toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj B)).app (Opposite.op T) ≫
      (proEtaleConstantDirectImageMap f D B).hom.app (Opposite.op T) ≫ 𝟙 _
    rw [Category.comp_id]
    let C := (proEtaleSheafDirectImage f D).obj ((constantSheaf K D).obj B)
    let q : (Functor.const Y.ProEtᵒᵖ).obj B ⟶ C.obj :=
      Functor.whiskerLeft G.op (toSheafify K ((Functor.const X.ProEtᵒᵖ).obj B))
    have eq := ((sheafificationAdjunction J D).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj B) C).apply_symm_apply q
    change toSheafify J _ ≫ (proEtaleConstantDirectImageMap f D B).hom = q at eq
    exact (congrArg (fun η ↦ η.app (Opposite.op T)) eq).symm
  rw [← h]
  infer_instance

private noncomputable def constantModulePullbackFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) := by
  have := constantComparison_isIso f A
  exact proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))

private theorem pullback_isZero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsZero (proEtaleConstantModulePullback f A F) := by
  have := constantComparison_isIso f A
  exact (proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))).map_isZero hF

private theorem constantPresheaf_zero (C : Type (u + 1)) [Category* C]
    (A : Type u) [CommRing A] :
    IsZero (proEtaleConstantModulePresheaf C A
      ((HasZeroObject.zero
        (C := ModuleCat.{u + 1} (ULift.{u + 1, u} A))).choose)) := by
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro U
  exact (isZero_zero _).eq_of_src _ _

theorem locallyConstant_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheaf Y A F := by
  let : Zero (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) := HasZeroObject.zero' _
  let U : PUnit.{u + 2} → Y.ProEt := fun _ ↦ ProEt.mk (𝟙 Y)
  let a : ∀ i : PUnit.{u + 2}, U i ⟶ ProEt.mk (𝟙 Y) := fun _ ↦ 𝟙 _
  refine ⟨PUnit.{u + 2}, U, a, ?_, fun i ↦ ?_⟩
  · rw [Presieve.ofArrows_of_unique]
    exact Precoverage.mem_coverings_of_isIso (𝟙 (ProEt.mk (𝟙 Y)))
  · refine ⟨0, ⟨?_⟩⟩
    have hz : IsZero (proEtaleConstantModuleSheafOver Y A (U i) 0) := by
      have := (proEtaleConstantRingUnit_over_locallyBijective Y A (U i)).1
      have := (proEtaleConstantRingUnit_over_locallyBijective Y A (U i)).2
      unfold proEtaleConstantModuleSheafOver
      exact (PresheafOfModules.sheafification _).map_isZero (constantPresheaf_zero _ A)
    let E := SheafOfModules.overFunctor
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)) (U i)
    have : E.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    exact (E.map_isZero hF).iso hz

private theorem locallyConstant_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheaf Y A F) :
    IsLocallyConstantProEtaleModuleSheaf Y A G := by
  obtain ⟨I, U, f, hc, ht⟩ := hF
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  obtain ⟨M, ⟨hM⟩⟩ := ht i
  exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e.symm ≪≫ hM⟩⟩

theorem finite_stalk_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    [Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)] :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) G) := by
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      ModuleCat.{u + 1} (proEtaleGeometricStalkRing y (proEtaleConstantRing Y A)) :=
    (SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y) _ ⋙
    PresheafOfModules.colimitFunctor (C := ProEtaleGeometricNeighbourhood y)
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y (proEtaleConstantRing Y A))))
  have : Finite (E.obj F) :=
    ‹Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)›
  change Finite (E.obj G)
  exact Finite.of_injective (E.mapIso e.symm).toLinearEquiv
    (E.mapIso e.symm).toLinearEquiv.injective

theorem finite_stalk_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) := by
  let D := PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
    ((proEtaleConstantRing Y A).obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let L := PresheafOfModules.colimitFunctor (C := ProEtaleGeometricNeighbourhood y)
    (colimit.isColimit (proEtaleGeometricStalkRingDiagram y (proEtaleConstantRing Y A)))
  have : D.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have : L.IsLeftAdjoint := (PresheafOfModules.colimitAdjunction _).isLeftAdjoint
  have hz := (SheafOfModules.forget _ ⋙ D ⋙ L).map_isZero hF
  have : Subsingleton (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) :=
    ModuleCat.subsingleton_of_isZero hz
  infer_instance

/-- The single stratum equal to the whole scheme witnesses constructibility of zero. -/
private theorem constructibleProEtale_of_isZero (Y : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsZero F) : IsConstructibleProEtaleModuleSheaf Y A F := by
  let S : Stratification Y :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ IsOpen.isLocallyClosed isOpen_univ
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := by
        ext x
        exact ⟨fun _ ↦ Set.mem_univ _, fun _ ↦ Set.mem_iUnion.mpr ⟨0, Set.mem_univ _⟩⟩
      pairwise_disjoint_stratum := fun i j h ↦ (h (Subsingleton.elim i j)).elim
      domain := fun _ ↦ Y
      immersion := fun _ ↦ 𝟙 Y
      range_immersion := fun _ ↦ Set.range_id }
  refine ⟨S, by change 0 < (1 : ℕ); exact Nat.zero_lt_succ 0, fun i ↦ ?_⟩
  have hz := pullback_isZero (S.immersion i) A F hF
  exact ⟨locallyConstant_of_isZero _ A _ hz, fun Ω _ _ y ↦
    finite_stalk_of_isZero _ A _ hz y⟩

/-- Transport a constructibility witness through a module-sheaf isomorphism. -/
private theorem constructibleProEtale_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' : proEtaleConstantModulePullback (S.immersion i) A F ≅
      proEtaleConstantModulePullback (S.immersion i) A G :=
    (constantModulePullbackFunctor (S.immersion i) A).mapIso e
  refine ⟨locallyConstant_of_iso _ A e' (hS i).1, ?_⟩
  intro Ω _ _ y
  have := (hS i).2 Ω y
  exact finite_stalk_of_iso _ A e' y


private theorem finite_homology_support_iff_bounded
    (Y : Scheme.{u}) (A : Type u) [CommRing A] (K : proEtaleDerivedCategory Y A) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ↔
      DerivedCategory.TStructure.t.bounded K := by
  rw [Set.finite_iff_bddBelow_bddAbove]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ by
      by_contra h
      exact (not_le_of_gt hi) (ha h)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ by
        by_contra h
        exact (not_le_of_gt hi) (hb h)⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, fun i hi ↦ le_of_not_gt fun h ↦ hi ((DerivedCategory.isGE_iff K a).1 ha i h)⟩,
      ⟨b, fun i hi ↦ le_of_not_gt fun h ↦ hi ((DerivedCategory.isLE_iff K b).1 hb i h)⟩⟩

/-- Bounded globally constructible cohomology is invariant under isomorphisms and
cuts out a full triangulated subcategory. Source: Stacks Project, Tags 09AL,
09B5 and 06UQ; Weil blueprint, `def-weil-finite-torsion-constructibility`
(blueprint: lem-weil-proetale-dbc-triangulated).

Proof:
1. A zero sheaf is constructible using the single stratum equal to the whole scheme.
The canonical constant-ring comparison is invertible by uniqueness of the
constant-sheaf left adjoint, with its normalization checked on constant sections.
The specified pullback is therefore the existing exact operations functor and preserves zero
objects.
Localization and geometric stalks preserve zero objects as well. The identity covering
therefore trivializes its restriction with the zero module, and its geometric stalks have
singleton underlying
sets. An isomorphism transports the same stratification, local trivializations and stalk
finiteness, because module pullback, localization and geometric stalks are functorial.
2. `constructibleProEtale_exactClosure` gives kernels, cokernels and extensions in the
constructible class. The universal-property isomorphisms identify arbitrary limiting
kernels and colimiting cokernels with the selected ones, yielding the ObjectProperty
closure classes required by `cohomology_in_weak_serre_subcategory`.
3. Its bounded clause supplies the triangulation of `homologyProperty P` intersected
with the bounded standard derived class. A set of integers is finite exactly when it is
bounded above and below. `DerivedCategory.isGE_iff` and `isLE_iff` turn those bounds for
nonzero homology into the standard derived bounds. Thus the displayed predicate equals
that intersection, up to commutation of its two conjuncts. Substitute this equality to
obtain both isomorphism closure and triangulation. -/
theorem proEtale_bounded_constructible_isTriangulated
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : proEtaleDerivedCategory Y A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)) ∧
    ObjectProperty.IsTriangulated (fun K : proEtaleDerivedCategory Y A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)) := by
  let P : ObjectProperty (proEtaleRingModules Y (proEtaleConstantRing Y A)) :=
    IsConstructibleProEtaleModuleSheaf Y A
  let : Zero (proEtaleRingModules Y (proEtaleConstantRing Y A)) := HasZeroObject.zero' _
  obtain ⟨hkc, hext⟩ := constructibleProEtale_exactClosure Y A
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ constructibleProEtale_of_iso Y A e h⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, constructibleProEtale_of_isZero Y A _ (isZero_zero _)⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ hext _ hS h1 h3⟩
  have htri := (cohomology_in_weak_serre_subcategory P).2.2
  let Q : ObjectProperty (proEtaleDerivedCategory Y A) := fun K ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, P ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)
  have hQ : Q = DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded := by
    funext K
    apply propext
    change (_ ∧ _) ↔ (_ ∧ DerivedCategory.TStructure.t.bounded K)
    rw [finite_homology_support_iff_bounded]
    exact and_comm
  change ObjectProperty.IsClosedUnderIsomorphisms Q ∧ ObjectProperty.IsTriangulated Q
  rw [hQ]
  exact ⟨inferInstance, htri⟩


end AlgebraicGeometry.Scheme
