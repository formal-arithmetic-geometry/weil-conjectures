/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Native field coefficients and scalar-perfect generation

Source: blueprint latest, scalar-six-ctf proof (1), field coefficients.
(blueprint: lem-sfb-native-field-scalar-generation).
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

private theorem lisse_locallyPerfect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hL : IsLisseCoefficientModule Λ L) :
    IsLocallyPerfectScalarModel Λ S ((DerivedCategory.singleFunctor _ 0).obj L) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hL
  refine ⟨𝒰, fun j ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := h𝒰 j
  let A := Mod.finiteFree (scalarRingObj Λ) n
  let C := (HomologicalComplex.single _ (.up ℤ) 0).obj A
  refine ⟨C, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
  · intro q
    by_cases hq : q = 0
    · subst q
      exact ⟨n, ⟨Retract.ofIso (HomologicalComplex.singleObjXSelf _ 0 A)⟩⟩
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A q hq
      have hzero : IsZero (Mod.finiteFree (scalarRingObj Λ) 0) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      exact ⟨0, ⟨Retract.ofIso (hz.iso hzero)⟩⟩
  · let F := finiteConstantScalarExtension Λ (𝒰.X j)
    exact ⟨((upperStar Λ (𝒰.f j)).mapDerivedCategorySingleFunctor 0).app L ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (e ≪≫ (AlgebraicGeometry.ProEtale.scalarFreeIso Λ (𝒰.X j) n).symm) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj A) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app A).symm⟩

private theorem single_extension_generator (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [TopologicalSpace.NoetherianSpace X.left]
    (S : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S))
    (hL : IsLisseCoefficientModule Λ.X L) :
    sfbPerfectScalarGenerator Λ X ((DerivedCategory.singleFunctor _ 0).obj
      ((coefficientHeartLocallyClosedExtension Λ.X a ha).obj L)) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : IsImmersion a := ha
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  let V : X.left.Opens :=
    ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hc : Set.range a.imageι.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl (Set.range a.imageι)).symm
  have : PreservesFiniteColimits (lowerStar Λ.X a.imageι) :=
    closedSupport_lowerStarExact Λ.X a.imageι V.ι hc
  let U := openImmersionLowerShriek Λ.X a.toImage
  let I := lowerStar Λ.X a.imageι
  let e : (sfbLocallyClosedDerivedExtension Λ a ha).obj
      ((DerivedCategory.singleFunctor _ 0).obj L) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((coefficientHeartLocallyClosedExtension Λ.X a ha).obj L) :=
    (I.rightDerivedFunctorIsoMapDerivedCategory.app _) ≪≫
      I.mapDerivedCategory.mapIso ((U.mapDerivedCategorySingleFunctor 0).app L) ≪≫
      (I.mapDerivedCategorySingleFunctor 0).app _
  exact ⟨S, a, ha, _, lisse_locallyPerfect Λ.X S L hL, ⟨e.symm⟩⟩

private theorem fieldFiniteHull_closed
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (G : ObjectProperty C) :
    let P : ObjectProperty C := fun D ↦ ∃ n : ℕ, (G.shiftClosure ℤ).extensionProductIter n D
    P.IsClosedUnderIsomorphisms ∧ P.IsStableUnderShift ℤ ∧ P.IsTriangulatedClosed₂ := by
  let B := G.shiftClosure ℤ
  let P : ObjectProperty C := fun D ↦ ∃ n : ℕ, B.extensionProductIter n D
  have hGn (n : ℕ) : (B.extensionProductIter n).IsClosedUnderIsomorphisms := by
    induction n with
    | zero => exact inferInstanceAs (G.shiftClosure ℤ).IsClosedUnderIsomorphisms
    | succ n ih => rw [ObjectProperty.extensionProductIter_succ]; infer_instance
  have : P.IsClosedUnderIsomorphisms := ⟨by
    rintro D D' e ⟨n, hn⟩
    have := hGn n
    exact ⟨n, (B.extensionProductIter n).prop_of_iso e hn⟩⟩
  have : P.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun a ↦ ⟨by
        rintro D ⟨n, hn⟩
        exact ⟨n, (B.extensionProductIter n).le_shift a D hn⟩⟩ }
  have : P.IsTriangulatedClosed₂ := .mk' (by
    rintro T hT ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + 1 + m, ?_⟩
    rw [ObjectProperty.extensionProductIter_add B rfl]
    exact ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, hn, hm⟩)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem zero_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    IsLisseCoefficientModule Λ (0 : ModuleRingedComparison.internalModules Λ X) := by
  refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
    (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  refine ⟨0, ⟨?_⟩⟩
  apply IsZero.iso
  · exact (upperStar Λ _).map_isZero (isZero_zero _)
  · rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j

private theorem scalarGenerators_containsZero (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsNoetherian X.left] :
    (sfbPerfectScalarGenerator Λ X).ContainsZero := by
  let M : ModuleRingedComparison.internalModules Λ.X X.left := 0
  let W := (DerivedCategory.singleFunctor _ 0).obj
    ((coefficientHeartLocallyClosedExtension Λ.X (𝟙 X.left) (by infer_instance)).obj M)
  refine ⟨W, ?_, single_extension_generator Λ X X.left (𝟙 X.left)
    inferInstance M (zero_lisse Λ.X X.left)⟩
  exact (DerivedCategory.singleFunctor _ 0).map_isZero
    (locallyClosedExtension_zero Λ.X (𝟙 X.left) inferInstance)

private theorem single_subobject_filtration
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty (DerivedCategory C))
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [P.IsTriangulatedClosed₂]
    (M : C) (m : ℕ) (B : Fin (m + 1) → Subobject M)
    (hb : B 0 = ⊥) (ht : B (Fin.last m) = ⊤)
    (hle : ∀ a : Fin m, B a.castSucc ≤ B a.succ)
    (hq : ∀ a : Fin m, P ((DerivedCategory.singleFunctor C 0).obj
      (cokernel (Subobject.ofLE (B a.castSucc) (B a.succ) (hle a))))) :
    P ((DerivedCategory.singleFunctor C 0).obj M) := by
  have hz : IsZero (B 0 : C) :=
    (isZero_zero C).of_iso (Subobject.isoOfEq _ _ hb ≪≫ Subobject.botCoeIsoZero)
  have hall (q : ℕ) (hqm : q < m + 1) :
      P ((DerivedCategory.singleFunctor C 0).obj (B ⟨q, hqm⟩ : C)) := by
    induction q with
    | zero => exact P.prop_of_isZero ((DerivedCategory.singleFunctor C 0).map_isZero hz)
    | succ q ih =>
      let a : Fin m := ⟨q, by omega⟩
      let f := Subobject.ofLE (B a.castSucc) (B a.succ) (hle a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f)
          inferInstance inferInstance
      exact P.ext_of_isTriangulatedClosed₂ _ hS.singleTriangle_distinguished
        (ih (by omega)) (hq a)
  let e : (B (Fin.last m) : C) ≅ M :=
    Subobject.isoOfEq _ _ ht ≪≫ Subobject.underlyingIso (𝟙 M)
  exact P.prop_of_iso ((DerivedCategory.singleFunctor C 0).mapIso e)
    (hall m (Nat.lt_succ_self _))

private def LisseFiltrationProperty (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsNoetherian X.left] : Prop :=
  ∀ (M : ModuleRingedComparison.internalModules Λ X.left),
      IsConstantModelConstructible Λ X.left M →
    ∃ (Q : X.left.FiniteLocallyClosedStratification) (B : Fin (Q.n + 1) → Subobject M),
      B 0 = ⊥ ∧ B (Fin.last Q.n) = ⊤ ∧
      ∃ hle : ∀ a : Fin Q.n, B a.castSucc ≤ B a.succ,
        ∀ a : Fin Q.n,
          Nonempty (cokernel (Subobject.ofLE (B a.castSucc) (B a.succ) (hle a)) ≅
            (coefficientHeartLocallyClosedExtension Λ
              (Q.immersion a) (Q.isImmersion a)).obj
                ((CondensedRing.upperStar Λ
                  (Q.immersion a)).obj M)) ∧
          IsLisseCoefficientModule Λ
            ((CondensedRing.upperStar Λ (Q.immersion a)).obj M)

private def NativeFieldGenerationProperty (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : Prop :=
  ∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left),
    constantModelBoundedConstructible Λ.X X.left K →
      ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K

private theorem lisseFiltration_generation (Λ : ScalarSixRing.{u})
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsNoetherian X.left]
    (hfiltration : LisseFiltrationProperty Λ.X X) : NativeFieldGenerationProperty Λ X := by
  classical
  intro K hK
  let G := (sfbPerfectScalarGenerator Λ X).shiftClosure ℤ
  let P : ObjectProperty (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)) :=
    fun D ↦ ∃ n : ℕ, G.extensionProductIter n D
  obtain ⟨hi, hs, ht⟩ := fieldFiniteHull_closed (sfbPerfectScalarGenerator Λ X)
  have : P.IsClosedUnderIsomorphisms := hi
  have : P.IsStableUnderShift ℤ := hs
  have : P.IsTriangulatedClosed₂ := ht
  have hgen : sfbPerfectScalarGenerator Λ X ≤ P := by
    intro M hM
    exact ⟨0, (ObjectProperty.le_shiftClosure (A := ℤ) _) M hM⟩
  have : P.ContainsZero := by
    have := scalarGenerators_containsZero Λ X
    obtain ⟨Z, hZ, hG⟩ := (sfbPerfectScalarGenerator Λ X).exists_prop_of_containsZero
    exact ⟨Z, hZ, hgen Z hG⟩
  have : P.IsTriangulatedClosed₁ := .mk' (by
    intro T hT h₂ h₃
    exact P.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.inv_rot_of_distTriang _ hT) (P.le_shift _ _ h₃) h₂)
  have : P.IsTriangulatedClosed₃ := .mk' (by
    intro T hT h₁ h₂
    exact P.ext_of_isTriangulatedClosed₂ _
      (Pretriangulated.rot_of_distTriang _ hT) h₂ (P.le_shift _ _ h₁))
  have : P.IsTriangulated := {}
  have hheart (M : ModuleRingedComparison.internalModules Λ.X X.left)
      (hM : IsConstantModelConstructible Λ.X X.left M) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    obtain ⟨Q, B, hb, ht, hle, hQ⟩ := hfiltration M hM
    apply single_subobject_filtration P M Q.n B hb ht hle
    intro a
    obtain ⟨⟨e⟩, hL⟩ := hQ a
    exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
      (hgen _ (single_extension_generator Λ X (Q.domain a) (Q.immersion a)
        (Q.isImmersion a) _ hL))
  let H : ObjectProperty (ModuleRingedComparison.internalModules Λ.X X.left) :=
    fun M ↦ P ((DerivedCategory.singleFunctor _ 0).obj M)
  have : H.IsClosedUnderIsomorphisms :=
    ⟨fun e hM ↦ P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e) hM⟩
  have hPK : P K := by
    apply DerivedCategory.prop_of_bounded P H (fun _ h ↦ h) K hK.1
    intro q
    exact hheart _ (hK.2 q)
  obtain ⟨n, hn⟩ := hPK
  exact ⟨n, _, hn, ⟨Retract.refl K⟩⟩


/-- Finite lisse filtrations and bounded devissage yield finite extension witnesses
of scalar-perfect strata, without using the Tor-amplitude assumption.

Source: blueprint latest, scalar-six-ctf proof (1), field coefficients;
coefficient-heart lisse filtration, (blueprint: lem-sfb-native-field-scalar-generation).

Proof: on each lisse trivializing chart, use the degree-zero scalar complex on the
finite free module of the given rank. The scalar free-module comparison realizes
this complex as the given free coefficient module; zero degrees use rank zero.
Exactness of the canonical closed factor and the single-functor comparisons identify
ordinary lisse extensions with scalar-perfect generators. The union of finite
extension iterates of their shift closure is isomorphism closed, shift stable, and
extension closed by concatenation. It contains zero, using the zero lisse module.
The existing coefficient-heart filtration has lisse locally closed extensions as its
successive quotients. Induct on this filtration using the short exact sequence
triangle for each subobject inclusion. Rotation gives the other two triangle closure
operations. Bounded derived devissage, applied to the inverse image of the finite
hull under the degree-zero single functor, then gives every bounded constructible
complex. Finally take the identity retract. -/
theorem sfbNativeFieldGeneration (ell : ℕ) [Fact ell.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : (∃ E : IntermediateField ℚ_[ell] (PadicAlgCl ell),
      FiniteDimensional ℚ_[ell] E ∧ R = Profinite.padicSubfieldCondensedRing ell E) ∨
      R = Profinite.padicAlgClCondensedRing ell)
    (k : Type u) [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    : let Λ : ScalarSixRing.{u} := ⟨coefficientHeartRingObj R⟩
      ∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left),
        constantModelBoundedConstructible Λ.X X.left K →
          ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
            ).retractClosure K := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have hf : LisseFiltrationProperty (coefficientHeartRingObj R) X :=
    coefficientHeart_lisse_filtration ell R hR X.left
  change NativeFieldGenerationProperty ⟨coefficientHeartRingObj R⟩ X
  exact lisseFiltration_generation ⟨coefficientHeartRingObj R⟩ X hf

end AlgebraicGeometry.ProEtale.CondensedRing
