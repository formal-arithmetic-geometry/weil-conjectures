/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFieldGeneration
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import all WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
import all WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Integral generation from locally free resolutions

Source: blueprint latest, scalar-six-ctf proof (1), integral coefficients.
(blueprint: lem-sfb-native-integral-scalar-generation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem nonfiniteFiniteHull_closed
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (G : ObjectProperty C) :
    let H : ObjectProperty C := ⨆ n : ℕ, (G.shiftClosure ℤ).extensionProductIter n
    H.IsClosedUnderIsomorphisms ∧ H.IsStableUnderShift ℤ ∧
      H.IsTriangulatedClosed₁ ∧ H.IsTriangulatedClosed₂ ∧ H.IsTriangulatedClosed₃ := by
  let B := G.shiftClosure ℤ
  let H : ObjectProperty C := ⨆ n : ℕ, B.extensionProductIter n
  have : ∀ n, (B.extensionProductIter n).IsClosedUnderIsomorphisms := by
    intro n
    cases n with
    | zero => exact inferInstanceAs B.IsClosedUnderIsomorphisms
    | succ n => rw [B.extensionProductIter_succ]; infer_instance
  have : H.IsClosedUnderIsomorphisms := inferInstanceAs
    (⨆ n : ℕ, B.extensionProductIter n).IsClosedUnderIsomorphisms
  have : H.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX
    obtain ⟨m, hm⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hX
    exact (ObjectProperty.prop_iSup_iff _ _).mpr
      ⟨m, (B.extensionProductIter m).le_shift n X hm⟩⟩⟩
  have : H.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃
    obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₁
    obtain ⟨m, hm⟩ := (ObjectProperty.prop_iSup_iff _ _).mp h₃
    apply (ObjectProperty.prop_iSup_iff _ _).mpr
    refine ⟨n + 1 + m, ?_⟩
    rw [B.extensionProductIter_add (show n + 1 = n + 1 from rfl)]
    exact ⟨_, _, _, _, _, hT, hn, hm⟩)
  have : H.IsTriangulatedClosed₁ := .mk' (by
    intro T hT h₂ h₃
    exact H.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.inv_rot_of_distTriang _ hT) (H.le_shift _ _ h₃) h₂)
  have : H.IsTriangulatedClosed₃ := .mk' (by
    intro T hT h₁ h₂
    exact H.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.rot_of_distTriang _ hT) h₂ (H.le_shift _ _ h₁))
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem factorization_extension_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} [IsNoetherian X]
    {a : S ⟶ X} (A B : GeneratorFactorization a)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    Nonempty ((generatorExtension Λ A).obj M ≅ (generatorExtension Λ B).obj M) := by
  have hr := generatorRestriction_isIso Λ A
  obtain ⟨e⟩ := generatorExtension_reconstruct Λ B ((generatorExtension Λ A).obj M)
    (fun g hg ↦ generatorExtension_support Λ A g hg M)
  exact ⟨e ≪≫ (generatorExtension Λ B).mapIso ((asIso (generatorRestriction Λ A)).app M)⟩

private theorem resolution_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U : Scheme.{u}}
    (M : ModuleRingedComparison.internalModules Λ U)
    (hM : ResolutionLF (condensedRingObj Λ U) M) : IsLisseCoefficientModule Λ M := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun b ↦ ?_⟩
  let α := condensedPullbackHom Λ (C.f b)
  exact free_of_iso (free_comap (inv α) (hC b))
    ((Mod.extendScalarsIsoComapInv α).app _).symm

private theorem factorization_canonical_extension_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z U : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ Z) [IsOpenImmersion j]
    (M : ModuleRingedComparison.internalModules Λ U) :
    Nonempty ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ j).obj M) ≅
      (coefficientHeartLocallyClosedExtension Λ (j ≫ i) (by infer_instance)).obj M) := by
  have : IsImmersion (j ≫ i) := inferInstance
  have : TopologicalSpace.NoetherianSpace U :=
    (j ≫ i).isEmbedding.isInducing.noetherianSpace
  let A : GeneratorFactorization (j ≫ i) :=
    .inr ⟨Z, j, i, rfl, inferInstance, inferInstance⟩
  let B : GeneratorFactorization (j ≫ i) :=
    .inr ⟨(j ≫ i).image, (j ≫ i).toImage, (j ≫ i).imageι,
      (j ≫ i).toImage_imageι, inferInstance, inferInstance⟩
  have hA : generatorExtension Λ A = openImmersionLowerShriek Λ j ⋙ lowerStar Λ i := rfl
  have hB : generatorExtension Λ B =
      coefficientHeartLocallyClosedExtension Λ (j ≫ i) (by infer_instance) := rfl
  change Nonempty ((openImmersionLowerShriek Λ j ⋙ lowerStar Λ i).obj M ≅ _)
  rw [← hA, ← hB]
  exact factorization_extension_iso Λ A B M

private theorem scalarGenerator_of_iso (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {K L : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)}
    (e : K ≅ L) (hL : sfbPerfectScalarGenerator Λ X L) : sfbPerfectScalarGenerator Λ X K := by
  obtain ⟨S, a, ha, P, hP, ⟨q⟩⟩ := hL
  exact ⟨S, a, ha, P, hP, ⟨e ≪≫ q⟩⟩

private theorem free_factorization_generator (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsNoetherian X.left]
    {Z U : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j]
    (M : ModuleRingedComparison.internalModules Λ.X U)
    (hM : ResolutionLF (condensedRingObj Λ.X U) M) :
    sfbPerfectScalarGenerator Λ X ((DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj M))) := by
  obtain ⟨e⟩ := factorization_canonical_extension_iso Λ.X i j M
  apply scalarGenerator_of_iso Λ X ((DerivedCategory.singleFunctor _ 0).mapIso e)
  exact single_extension_generator Λ X U (j ≫ i) inferInstance M (resolution_lisse Λ.X M hM)

/-- Bounded constant-model integral complexes have finite scalar-perfect extension
witnesses. Source: scalar-six-ctf proof (1), integral tensor-shriek generation proof.
(blueprint: lem-sfb-native-integral-scalar-generation).

Proof: finite constant local models are locally finitely presented. The finite
open/closed extension tower reduces constructible sheaves to locally finitely
presented stratum modules. Their existing two-term locally free resolutions reduce
these pieces to locally free modules in degree zero. On a free chart use the
single complex on the finite free scalar module; zero terms use rank zero. Support
and restriction identify each open/closed factorization with the canonical image
factorization. Exact extension preserves the short exact resolution triangle.
The union of finite extensions of shifts is closed under all three triangle
operations. Bounded derived devissage therefore gives the same assertion for each
bounded constructible complex. Take its identity retract. -/
theorem sfbNativeIntegralGeneration
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (k : Type u) [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (K : ConstantModelConstructibleFiniteTor (CondensedRing.integralCoefficientRing ell E)
      X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator
        ⟨(CondensedRing.integralCoefficientRing ell E)⟩ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by
  classical
  let Λ : ScalarSixRing.{u} := ⟨(CondensedRing.integralCoefficientRing ell E)⟩
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  let P : ObjectProperty (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :=
    ⨆ n : ℕ, ((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
  obtain ⟨hi, hs, ht₁, ht₂, ht₃⟩ := nonfiniteFiniteHull_closed
    (sfbPerfectScalarGenerator Λ X)
  have : P.IsClosedUnderIsomorphisms := hi
  have : P.IsStableUnderShift ℤ := hs
  have : P.IsTriangulatedClosed₁ := ht₁
  have : P.IsTriangulatedClosed₂ := ht₂
  have : P.IsTriangulatedClosed₃ := ht₃
  have hgen : sfbPerfectScalarGenerator Λ X ≤ P := by
    intro M hM
    apply (ObjectProperty.prop_iSup_iff _ _).mpr
    exact ⟨0, (ObjectProperty.le_shiftClosure (A := ℤ) _) M hM⟩
  have hpiece : condensedLocallyClosedPiece Λ.X X.left ≤ P := by
    intro L hL
    obtain ⟨Z, U, i, j, hi, hj, hqc, M, hM, ⟨eL⟩⟩ := hL
    have := hi
    have := hj
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : IsNoetherian Z := ⟨⟩
    have : TopologicalSpace.NoetherianSpace U :=
      j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let V : X.left.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨hex, _⟩ := condensed_open_closed_recollement Λ.X i V.ι V.range_ι
    have := hex
    let F := (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
      (lowerStar Λ.X i).mapDerivedCategory
    have hfree (N : ModuleRingedComparison.internalModules Λ.X U)
        (hN : ResolutionLF (condensedRingObj Λ.X U) N) :
        P (F.obj ((DerivedCategory.singleFunctor _ 0).obj N)) := by
      let e : F.obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          (DerivedCategory.singleFunctor _ 0).obj
            ((lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj N)) :=
        (lowerStar Λ.X i).mapDerivedCategory.mapIso
          (((openImmersionLowerShriek Λ.X j).mapDerivedCategorySingleFunctor 0).app N) ≪≫
          ((lowerStar Λ.X i).mapDerivedCategorySingleFunctor 0).app _
      exact P.prop_of_iso e.symm (hgen _ (free_factorization_generator Λ X i j N hN))
    obtain ⟨T, ht, ⟨eT⟩, h₁, h₂⟩ := localModelResolution ell E U M hM
    have hthird : P (F.obj ((DerivedCategory.singleFunctor _ 0).obj T.X₃)) :=
      P.ext_of_isTriangulatedClosed₃ _ (F.map_distinguished _ ht.singleTriangle_distinguished)
        (hfree T.X₁ h₁) (hfree T.X₂ h₂)
    have hM' : P (F.obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      P.prop_of_iso (F.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso eT)) hthird
    let eF : F.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj M)) :=
      (lowerStar Λ.X i).mapDerivedCategory.mapIso
        (((openImmersionLowerShriek Λ.X j).mapDerivedCategorySingleFunctor 0).app M) ≪≫
        ((lowerStar Λ.X i).mapDerivedCategorySingleFunctor 0).app _
    exact P.prop_of_iso (eF ≪≫ eL.symm) hM'
  have hheart (M : ModuleRingedComparison.internalModules Λ.X X.left)
      (hM : IsConstructibleModuleObject (condensedRingObj Λ.X X.left) M) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    obtain ⟨r, hr⟩ := exists_condensedLocallyClosed_extension_tower X.left Λ.X M hM
    exact (condensedLocallyClosedPiece Λ.X X.left).extensionProductIter_le_of_isTriangulatedClosed₂
      hpiece r _ hr
  have : P.ContainsZero := ⟨(DerivedCategory.singleFunctor _ 0).obj 0,
    (DerivedCategory.singleFunctor _ 0).map_isZero (isZero_zero _),
    hheart 0 (constructible_of_isZero _ _ (isZero_zero _))⟩
  have : P.IsTriangulated := {}
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ.X X.left)) :=
    ⟨fun e hM ↦ _root_.constructible_of_iso e hM⟩
  have hK : P K.obj := by
    apply DerivedCategory.prop_of_bounded P
      (IsConstructibleModuleObject (condensedRingObj Λ.X X.left)) hheart K.obj K.property.1.1
    intro q
    apply constructible_of_finiteConstantStratified Λ.X X.left
    have hq := K.property.1.2 q
    simpa only [IsConstantModelConstructible,
      if_pos (show CompactSpace X.left ∧ QuasiSeparatedSpace X.left from
        ⟨inferInstance, inferInstance⟩)]
      using hq
  obtain ⟨n, hn⟩ := (ObjectProperty.prop_iSup_iff _ _).mp hK
  exact ⟨n, _, hn, ⟨Retract.refl K.obj⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
