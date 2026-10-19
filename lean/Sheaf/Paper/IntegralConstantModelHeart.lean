/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.CategoryTheory.Abelian.Subcategory
import Sheaf.AlgebraicGeometry.ConstructibleModuleObjectsEssentiallySmall
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.Paper.IntegralCoefficientRingComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.Paper.IntegralHeartLocalModel
import Sheaf.Paper.IntegralModels

/-!
# The integral constant-model constructible category and its heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart/
sk-lem-int-integral-heart-triangulated.md, assertions 1--2
(blueprint: det-lem-int-integral-heart-triangulated).

Coefficients are pulled-back condensed continuous functions into the valuation ring,
and the derived category is the ordinary unbounded category of internal modules.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring for an arbitrary finite extension, using its canonical
spectral norm. A finite extension of the small field of p-adic numbers is small by
`Module.Finite.small`. Its `Shrink` is used only to fit the existing continuous-function
API; `Shrink.algEquiv` identifies it with the given extension. Thus no coefficient
embedding or equality of universes is assumed. Source: blueprint integral-heart setting
and def-weil-l-adic-coefficient-extension
(blueprint: det-lem-int-integral-heart-triangulated). -/
noncomputable abbrev integralHeartCoefficientRingObj
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : Small.{0} E := Module.Finite.small (Padic ℓ) E
  letI : FiniteDimensional (Padic ℓ) (Shrink.{0} E) :=
    (Shrink.algEquiv (Padic ℓ) E).symm.toLinearEquiv.finiteDimensional
  letI := spectralNorm.normedField (Padic ℓ) (Shrink.{0} E)
  Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers ℓ (Shrink.{0} E))

section Helpers
open MonoidalCategory MonObj CondensedRing
open scoped CategoryTheory.Obj
open scoped ZeroObject
universe v₁ v₂ u₁ u₂

section Presentation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  {R : C} {S : D} [MonObj R] [MonObj S]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]
private lemma fp_map (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)
end Presentation
section
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (φ : Λ ⟶ Λ') [IsMonHom φ] [IsIso φ]
omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private lemma fp_point {P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ'}
    (hP : Mod.IsFinitelyPresented Λ' P) :
    Mod.IsFinitelyPresented Λ ((Mod.comap φ).obj P) := by
  apply fp_map (Mod.comap φ) _ hP
  intro n
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ') ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))
private noncomputable def pull_comap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Mod.comap (coefficientMap φ X) ⋙ CondensedRing.upperStar Λ f ≅
      CondensedRing.upperStar Λ' f ⋙ Mod.comap (coefficientMap φ Y) :=
  (CondensedRing.comapUpperStarIso φ f).symm
private lemma local_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eP⟩⟩
private lemma local_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : HasFiniteConstantLocalModel Λ' X M) :
    HasFiniteConstantLocalModel Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  refine ⟨(Mod.comap φ).obj P, fp_point φ hP, ⟨?_⟩⟩
  exact (pull_comap φ (U.f i)).app M ≪≫
    (Mod.comap (coefficientMap φ (U.X i))).mapIso eP ≪≫
    ((upperStarFromPoint (U.X i)).mapModComapIso φ).symm.app P
private lemma stratified_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : IsFiniteConstantStratified Λ' X M) :
    IsFiniteConstantStratified Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact local_iso ((pull_comap φ (S.immersion a)).app M).symm
    (local_comap φ _ _ (hS a))
private lemma stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ local_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
private lemma constructible_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [if_pos h] at hM ⊢
    exact stratified_iso e hM
  · simp only [if_neg h] at hM ⊢
    intro U hU
    exact stratified_iso ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)
private lemma constructible_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : IsConstantModelConstructible Λ' X M) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [if_pos h] at hM ⊢
    exact stratified_comap φ X M hM
  · simp only [if_neg h] at hM ⊢
    intro U hU
    exact stratified_iso ((pull_comap φ U.ι).app M).symm
      (stratified_comap φ _ _ (hM U hU))

private theorem constantModel_comap_iff (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) ↔
      IsConstantModelConstructible Λ' X M := by
  constructor
  · intro h
    have hh := constructible_comap (inv φ) X _ h
    exact constructible_iso
      (((Mod.comapComp (coefficientMap (inv φ) X) (coefficientMap φ X)).symm ≪≫
        Mod.comapCongr (by rw [← coefficientMap_comp]; simp) ≪≫
          Mod.comapId _).app M) hh
  · exact constructible_comap φ X M
end

end Helpers

section General
open scoped CategoryTheory.Obj
open scoped ZeroObject
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private lemma local_zero {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    .singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _)
  refine ⟨U, fun i ↦ ?_⟩
  let P := cokernel (𝟙 (Mod.finiteFree Λ 0))
  have hP : Mod.IsFinitelyPresented Λ P := ⟨0, 0, 𝟙 _, ⟨Iso.refl _⟩⟩
  refine ⟨P, hP, ⟨?_⟩⟩
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  exact ((CondensedRing.upperStar Λ (U.f i)).map_isZero hM).iso
    (F.map_isZero (isZero_cokernel_of_epi _))

private lemma stratified_zero {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  refine ⟨Scheme.Stratification.trivial X, fun a ↦ ?_⟩
  exact local_zero Λ ((CondensedRing.upperStar Λ _).map_isZero hM)

private lemma constructible_zero (X : Scheme.{u}) :
    ObjectProperty.ContainsZero (IsConstantModelConstructible Λ X) := by
  classical
  refine ⟨0, isZero_zero _, ?_⟩
  unfold IsConstantModelConstructible
  split
  · exact stratified_zero Λ (isZero_zero _)
  · intro U hU
    exact stratified_zero Λ ((CondensedRing.upperStar Λ U.ι).map_isZero (isZero_zero _))

private lemma constructible_iso_closed (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) :=
  ⟨fun e h ↦ constructible_iso e h⟩

private lemma bounded_iso (X : Scheme.{u}) :
    (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms := by
  let := constructible_iso_closed Λ X
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstantModelConstructible Λ X)).IsClosedUnderIsomorphisms
  infer_instance

private lemma bounded_trunc (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hK : constantModelBoundedConstructible Λ X K) (n : ℤ) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
    constantModelBoundedConstructible Λ X ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  let := constructible_zero Λ X
  let := constructible_iso_closed Λ X
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  let := ha
  let := hb
  constructor
  · refine ⟨⟨⟨a, ?_⟩, ⟨n, inferInstance⟩⟩,
      DerivedCategory.homologyProperty_truncLE hK.2 n⟩
    exact inferInstanceAs (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj K) a)
  · exact ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
      DerivedCategory.homologyProperty_truncGE hK.2 n⟩

private lemma bounded_single (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := constructible_zero Λ X
  let := constructible_iso_closed Λ X
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply ObjectProperty.prop_of_isZero (IsConstantModelConstructible Λ X)
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

private lemma single_image (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (ObjectProperty.ι (IsConstantModelConstructible Λ X) ⋙
      DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K := by
  let := bounded_iso Λ X
  let := constructible_iso_closed Λ X
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    refine ⟨(constantModelBoundedConstructible Λ X).prop_of_iso e
      (bounded_single Λ X M.obj M.property), ?_, ?_⟩
    · have he : (DerivedCategory.singleFunctor _ 0).obj M.obj ≅ K := e
      exact (DerivedCategory.TStructure.t.isLE_of_iso he 0).le
    · have he : (DerivedCategory.singleFunctor _ 0).obj M.obj ≅ K := e
      exact (DerivedCategory.TStructure.t.isGE_of_iso he 0).ge
  · rintro ⟨hK, hle, hge⟩
    let : K.IsLE 0 := ⟨hle⟩
    let : K.IsGE 0 := ⟨hge⟩
    obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
    have hM : IsConstantModelConstructible Λ X M :=
      ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M) (hK.2 0)
    exact ⟨⟨M, hM⟩, ⟨e.symm⟩⟩

private lemma constructible_products (X : Scheme.{u})
    [ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ X)] :
    ObjectProperty.IsClosedUnderFiniteProducts (IsConstantModelConstructible Λ X) := by
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  let := constructible_zero Λ X
  let := constructible_iso_closed Λ X
  let : P.IsClosedUnderBinaryProducts := by
    constructor
    rintro Z ⟨d⟩
    have h₁ : P (d.diag.obj ⟨WalkingPair.left⟩) := d.prop_diag_obj _
    have h₂ : P (d.diag.obj ⟨WalkingPair.right⟩) := d.prop_diag_obj _
    exact P.prop_of_iso
      (biprod.isoProd _ _ ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair d.diag)).symm ≪≫
        (limit.isoLimitCone ⟨_, d.isLimit⟩)) (P.prop_biprod h₁ h₂)
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

private lemma bounded_tri (X : Scheme.{u})
    [ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ X)]
    [ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ X)]
    [ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ X)] :
    (constantModelBoundedConstructible Λ X).IsTriangulated := by
  let := constructible_zero Λ X
  let := constructible_iso_closed Λ X
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstantModelConstructible Λ X)).IsTriangulated
  infer_instance

private lemma constructible_small (X : Scheme.{u}) [IsNoetherian X] :
    EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X) := by
  let := constructibleModuleObjects_essentiallySmall (X := X) (condensedRingObj Λ X)
  have h : IsConstantModelConstructible Λ X ≤
      IsConstructibleModuleObject (condensedRingObj Λ X) := by
    intro M hM
    have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    rw [IsConstantModelConstructible, if_pos hqc] at hM
    obtain ⟨S, hS⟩ := hM
    refine ⟨S, fun a ↦ ?_⟩
    have hlfp := (hS a).isLocallyFinitelyPresented _
    exact localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
      (localFinitePresentation_of_iso
        ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _) hlfp)
  let : ObjectProperty.EssentiallySmall.{u + 1} (IsConstantModelConstructible Λ X) :=
    ObjectProperty.EssentiallySmall.of_le h
  infer_instance

end General

section SerreTransport
open scoped CategoryTheory.Obj
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private lemma serre_transport (X : Scheme.{u}) (e : Mon.mk Λ ≅ Mon.mk Λ')
    (hkc : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ' X)) (f : M ⟶ N),
      IsConstantModelConstructible Λ' X M → IsConstantModelConstructible Λ' X N →
      IsConstantModelConstructible Λ' X (kernel f) ∧
      IsConstantModelConstructible Λ' X (cokernel f))
    (hext : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ' X)), S.ShortExact →
      IsConstantModelConstructible Λ' X S.X₁ → IsConstantModelConstructible Λ' X S.X₃ →
      IsConstantModelConstructible Λ' X S.X₂) :
    ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ X) ∧
    ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ X) ∧
    ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ X) := by
  let a := e.inv.hom
  let : IsMonHom a := inferInstanceAs (IsMonHom e.inv.hom)
  let : IsIso a := inferInstanceAs (IsIso e.inv.hom)
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
    Mod.comap (coefficientMap a X)
  have cmp (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      IsConstantModelConstructible Λ' X (F.obj M) ↔ IsConstantModelConstructible Λ X M :=
    constantModel_comap_iff a X M
  have ker_coker {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)} (f : M ⟶ N)
      (hM : IsConstantModelConstructible Λ X M)
      (hN : IsConstantModelConstructible Λ X N) :
      IsConstantModelConstructible Λ X (kernel f) ∧
      IsConstantModelConstructible Λ X (cokernel f) := by
    obtain ⟨hk, hc⟩ := hkc _ _ (F.map f) ((cmp _).mpr hM) ((cmp _).mpr hN)
    exact ⟨(cmp _).mp (constructible_iso (PreservesKernel.iso F f).symm hk),
      (cmp _).mp (constructible_iso (PreservesCokernel.iso F f).symm hc)⟩
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · rintro Z ⟨f, k, hk, hf⟩
    exact constructible_iso (limit.isoLimitCone ⟨k, hk⟩) (ker_coker f hf.1 hf.2).1
  · rintro Z ⟨f, k, hk, hf⟩
    exact constructible_iso (colimit.isoColimitCocone ⟨k, hk⟩) (ker_coker f hf.1 hf.2).2
  · intro S hS h₁ h₃
    exact (cmp _).mp (hext (S.map F) (hS.map_of_exact F) ((cmp _).mpr h₁)
      ((cmp _).mpr h₃))
end SerreTransport

private lemma integralHeart_serre (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) := by
  let : Small.{0} E := Module.Finite.small (Padic ℓ) E
  let : FiniteDimensional (Padic ℓ) (Shrink.{0} E) :=
    (Shrink.algEquiv (Padic ℓ) E).symm.toLinearEquiv.finiteDimensional
  let := spectralNorm.normedField (Padic ℓ) (Shrink.{0} E)
  obtain ⟨F, ⟨e⟩⟩ := integralCoefficientRingComparison.{u} ℓ (Shrink.{0} E)
  obtain ⟨hkc, hext⟩ := isConstantModelConstructible_serre_padicIntegers X ℓ F
  exact serre_transport X e hkc hext

/-- The integral bounded constructible category is full triangulated, bounded and stable
under both standard truncations. The degree-zero single functor identifies its heart
with the full abelian category of constructible module sheaves, which is closed under
ambient kernels, cokernels and extensions and is essentially small.
Source: blueprint main-20261015, integral-heart-triangulated, assertions 1--2
(blueprint: det-lem-int-integral-heart-triangulated).

Proof: identify the small coefficient extension with its image in the fixed algebraic
closure using uniqueness of the extended p-adic norm. Transport the existing weak Serre
closure theorem along the resulting condensed ring isomorphism; finite presentations and
constant local models are preserved by restriction of scalars. Apply the homology-property
triangulation and truncation theorems. Concentration and full faithfulness of the single
functor identify the degree-zero heart. The abelian-subcategory criterion gives
abelianness. Finally finite constant local models are locally finitely presented, so the
existing essential-smallness theorem for constructible module objects applies. -/
theorem integralConstantModelHeart
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsTriangulated
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ K, constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K →
      DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Full ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Faithful ∧
    (∀ K, (ObjectProperty.ι
        (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
        DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X)) ∧
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let Λ := integralHeartCoefficientRingObj ℓ E
  obtain ⟨hk, hc, he⟩ := integralHeart_serre ℓ E X
  let : ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ X) := hk
  let : ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ X) := hc
  let : ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ X) := he
  let := constructible_zero Λ X
  let := constructible_iso_closed Λ X
  let := constructible_products Λ X
  exact ⟨bounded_iso Λ X, bounded_tri Λ X,
    fun K hK ↦ ⟨hK.1, bounded_trunc Λ X K hK⟩,
    inferInstance, inferInstance, single_image Λ X, ⟨inferInstance⟩,
    hk, hc, he, constructible_small Λ X⟩

end AlgebraicGeometry.ProEtale
