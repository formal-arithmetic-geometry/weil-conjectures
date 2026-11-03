/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedArbitraryPullback
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!
# Proper direct image on constructible complexes of finite Tor amplitude

Source: blueprint latest, part-six-operations/sec-reduction-finite-coefficients/
sec-proper-direct-image/sk-thm-sfb-proper-base-change/_section.md
(blueprint: sk-thm-sfb-proper-base-change).

The canonical maps live in the ordinary unbounded derived categories of internal
modules over the pulled-back condensed rings. The two endpoint conditions in the
base-change clause express that this natural transformation restricts to Dctf;
its components being invertible says exactly that the restriction is an isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem properImage_exchangeRight_eq_mate
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    Adjunction.exchangeRight af af' θ =
      (mateEquiv af af' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans := by
  ext K
  simp [Adjunction.exchangeRight_app, mateEquiv]

private theorem properImage_baseChangeMap_eq_ambient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) :
    baseChangeMap Λ sq.toCommSq = condensedAmbientExchange Λ sq := by
  have hcomp : pullbackSquareComparison Λ sq.toCommSq =
      condensedAmbientPullbackComparison Λ sq := rfl
  unfold baseChangeMap condensedAmbientExchange
  rw [properImage_exchangeRight_eq_mate, hcomp]

private theorem properImage_ctf_scalar
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) (T : Scheme.{u})
    (K : ConstantModelConstructibleFiniteTor R T) :
    (constantModelBoundedConstructible S T ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      ((internalScalarExtension e.hom.hom T).obj K.obj) := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have : IsIso (coefficientMap e.hom.hom T) := by
    dsimp [coefficientMap]
    infer_instance
  have : (Mod.comap (asIso (coefficientMap e.hom.hom T)).inv).IsEquivalence :=
    (inferInstance :
      (Mod.comapEquivalenceOfIsIso (coefficientMap e.hom.hom T)).inverse.IsEquivalence)
  have : (Mod.extendScalars (coefficientMap e.hom.hom T)).IsEquivalence :=
    Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv _).symm
  have hi : inv (coefficientMap e.hom.hom T) = coefficientMap e.inv.hom T := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← coefficientMap_comp]
    change coefficientMap ((Mon.forget _).map (e.hom ≫ e.inv)) T = _
    rw [Iso.hom_inv_id]
    exact coefficientMap_id T
  let ed : internalScalarExtension e.hom.hom T ≅
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (coefficientMap e.inv.hom T)).mapDerivedCategory :=
    (Mod.extendScalars (coefficientMap e.hom.hom T)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso
        (Mod.extendScalarsIsoComapInv (coefficientMap e.hom.hom T) ≪≫ Mod.comapCongr hi)
  have : (constantModelBoundedConstructible S T).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined S T).2.1
  exact ObjectProperty.prop_of_iso _ (ed.app K.obj).symm
    (constantModelCtf_coefficientIso e T K)

private theorem properImage_projection_coefficientIso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S)
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y)
    (h : ∀ (K : ConstantModelConstructibleFiniteTor S X.left)
      (M : ConstantModelConstructibleFiniteTor S Y.left),
      IsIso (moduleObjectProjectionMap S p.left K.obj M.obj))
    (K : ConstantModelConstructibleFiniteTor R X.left)
    (M : ConstantModelConstructibleFiniteTor R Y.left) :
    IsIso (moduleObjectProjectionMap R p.left K.obj M.obj) := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  apply projection_isIso_of_coefficientIso e.hom.hom ell k p K.obj M.obj
  exact h ⟨_, properImage_ctf_scalar e X.left K⟩ ⟨_, properImage_ctf_scalar e Y.left M⟩

private theorem properImage_finite_projection
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
    (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj A) X.left)
    (M : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj A) Y.left) :
    IsIso (moduleObjectProjectionMap (Profinite.continuousMapRingObj A) p.left K.obj M.obj) := by
  classical
  let B := ULift.{u} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let e : A ≃+* B := ULift.ringEquiv.symm
  let h : Profinite.continuousMapRingSheaf.{u} A ⟶
      Profinite.continuousCoefficientRingSheaf B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousCoefficientRingSheaf B ⟶
      Profinite.continuousMapRingSheaf.{u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let eR : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S g
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S g
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let e' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e'.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  let eb : Mon.mk (Profinite.continuousMapRingObj A) ≅
      Mon.mk (FiniteDiscreteOrdinary.coefficient B) := Mon.mkIso' e'
  have hB : ∃ n : ℕ, (ell ^ n : ℕ) • (1 : B) = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    apply ULift.ext
    exact hn 1
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists B T).some
  exact (finiteProperBaseChange_of_coefficientIso
    (Profinite.continuousMapRingObj A) B eb E ell hB k X Y p).2.2 K M

attribute [local instance] finiteProperCache2 finiteProperCache3 finiteProperCache4
  finiteProperCache5 finiteProperCache6 finiteProperCache7 finiteProperCache8
  finiteProperCache9 finiteProperCache10 finiteProperCache12
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local instance 30000] instCategoryDerivedCategory CategoryTheory.Mod.instCategory
attribute [local instance 1] ProjectionMorphismData.category
attribute [local instance] Sheaf.braidedCategory
attribute [local instance 30000] Sheaf.monoidalCategory Mod.monoidalCategory

attribute [local irreducible] moduleObjectProjectionMap
  upperStar lowerStar AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  DerivedCategory HasDerivedCategory.standard CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private noncomputable def properImage_chosenSquare
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' p' p g) : ChosenCartesianSquare g' p' p g :=
  { toCommSq := sq.toCommSq
    isoPullback := sq.isoPullback
    hom_fst := sq.isoPullback_hom_fst
    hom_snd := sq.isoPullback_hom_snd }

private theorem properImage_isIso_app_of_eq
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    {α β : F ⟶ G} (e : α = β) (K : C) (h : IsIso (β.app K)) :
    IsIso (α.app K) := by
  cases e
  exact h

private theorem properImage_baseChange_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : IsIso ((condensedAmbientExchange Λ sq).app K)) :
    IsIso ((baseChangeMap Λ sq.toCommSq).app K) := by
  exact properImage_isIso_app_of_eq (properImage_baseChangeMap_eq_ambient Λ sq) K h

private theorem properImage_exchange_scheme
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : IsPullback a q' q v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (hK : constantModelBoundedConstructible Λ Z K ∧ DerivedCategory.finiteTorAmplitude _ K) :
    IsIso ((baseChangeMap Λ sq.toCommSq).app K) := by
  let cs := properImage_chosenSquare sq
  have hamb : IsIso ((condensedAmbientExchange Λ cs).app K) :=
    properBaseChange_admissible_generators ℓ Λ hΛ k q v cs K hK
  have hbase := properImage_baseChange_isIso Λ cs K hamb
  have hc : cs.toCommSq = sq.toCommSq := rfl
  rw [hc] at hbase
  exact hbase

private theorem properImage_admissible_projection
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (K : ConstantModelConstructibleFiniteTor Λ X.left)
    (M : ConstantModelConstructibleFiniteTor Λ Y.left) :
    IsIso (moduleObjectProjectionMap Λ p.left K.obj M.obj) := by
  classical
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  have : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  have : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  let E₀ : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ell
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have integral (E : PadicAlgCl.FiniteIntermediateField ell)
      (K : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ell E) X.left)
      (M : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ell E) Y.left) :
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ell E)
        p.left K.obj M.obj) := by
    have hX := (adicConstructibilityPredicateComparison ell X.left
      (Profinite.padicIntegersRingObj ell E.val) (.integral E.val)).2
    have hY := (adicConstructibilityPredicateComparison ell Y.left
      (Profinite.padicIntegersRingObj ell E.val) (.integral E.val)).2
    exact integral_projection ell p E K.obj M.obj
      ((congrFun hX _).mpr K.property.1) ((congrFun hY _).mpr M.property.1)
  have rational (E : PadicAlgCl.FiniteIntermediateField ell)
      (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) X.left)
      (M : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) Y.left) :
      IsIso (moduleObjectProjectionMap (Profinite.continuousMapRingObj E)
        p.left K.obj M.obj) := by
    have hX := (adicConstructibilityPredicateComparison ell X.left
      (Profinite.continuousMapRingObj E) (.continuous E)).2
    have hY := (adicConstructibilityPredicateComparison ell Y.left
      (Profinite.continuousMapRingObj E) (.continuous E)).2
    exact isIso_properProjectionMap_boundedConstructible_rational ell p
      (Mon.mk (Profinite.continuousMapRingObj E)) (Or.inl ⟨E, rfl⟩) K.obj M.obj
      ((congrFun hX _).mpr K.property.1) ((congrFun hY _).mpr M.property.1)
  have closure
      (K : ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ell) X.left)
      (M : ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ell) Y.left) :
      IsIso (moduleObjectProjectionMap (Profinite.padicAlgClRingObj ell)
        p.left K.obj M.obj) := by
    have hX := (adicConstructibilityPredicateComparison ell X.left
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).2
    have hY := (adicConstructibilityPredicateComparison ell Y.left
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).2
    exact isIso_properProjectionMap_boundedConstructible_rational ell p
      (Mon.mk (Profinite.padicAlgClRingObj ell)) (Or.inr rfl) K.obj M.obj
      ((congrFun hX _).mpr K.property.1) ((congrFun hY _).mpr M.property.1)
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, hA, ⟨e⟩⟩ := h
    have : Finite A := hfin
    exact properImage_projection_coefficientIso e ell k p
      (properImage_finite_projection ell k p A hA) K M
  · obtain ⟨e⟩ := h
    exact properImage_projection_coefficientIso (e ≪≫ zIso) ell k p (integral E₀) K M
  · obtain ⟨e⟩ := h
    exact properImage_projection_coefficientIso (e ≪≫ qIso) ell k p (rational E₀) K M
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact properImage_projection_coefficientIso e ell k p (rational E) K M
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact properImage_projection_coefficientIso e ell k p (integral E) K M
  · obtain ⟨e⟩ := h
    exact properImage_projection_coefficientIso e ell k p closure K M

private theorem properImage_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    IsAdmissibleCoefficient Λ := by
  refine ⟨ℓ, inferInstance, ?_⟩
  rcases hΛ with hfin | hZ | hQ | hE | hOE | hbar
  · rcases hfin with ⟨A, hA, htop, hdisc, hring, hfin, hn, he⟩
    obtain ⟨n, hn⟩ := hn
    exact Or.inl ⟨A, hA, hfin, htop, hdisc, hring, ⟨n, by
      simpa [nsmul_eq_mul] using hn 1⟩, he⟩
  · exact Or.inr (Or.inl hZ)
  · exact Or.inr (Or.inr (Or.inl hQ))
  · rcases hE with ⟨E, he⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, he⟩))))
  · rcases hOE with ⟨E, he⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbar))))

private theorem properImage_pullback_ctf
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {T' T : Scheme.{u}} [T'.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T' ↘ Spec (.of k))] [QuasiCompact (T' ↘ Spec (.of k))]
    [IsSeparated (T' ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (a : T' ⟶ T)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (hK : constantModelBoundedConstructible Λ T K ∧ DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible Λ T' ((L((a)^*⟦Λ⟧)).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((L((a)^*⟦Λ⟧)).obj K) := by
  exact ((condensedArbitraryPullback (p := ringChar k) (l := ℓ)
    (hpl := Fact.out) (k := k) Λ (properImage_admissible ℓ Λ hΛ) a).2.1).constructible K hK

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y)

private theorem properImage_preserves
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (hp : IsProper p.left) :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      constantModelBoundedConstructible Λ Y.left ((R((p.left)_*⟦Λ⟧)).obj K.obj) ∧
        DerivedCategory.finiteTorAmplitude _ ((R((p.left)_*⟦Λ⟧)).obj K.obj)) := by
  classical
  let : IsProper p.left := hp
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated X.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated Y.hom)
  let : p.left.IsOver (Spec (.of k)) := ⟨p.w⟩
  intro K
  exact constructibleFiniteTor_rightDerivedLowerStar_of_admissible ℓ k Λ hΛ
    p.left K.obj K.property

private theorem properImage_exchange
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (hp : IsProper p.left) :
    (∀ {X' Y' : Over (Spec (.of k))}
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
      {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : IsPullback g' p' p g) (K : ConstantModelConstructibleFiniteTor Λ X.left),
      IsIso ((baseChangeMap Λ
        (sq.map (Over.forget (Spec (.of k)))).toCommSq).app K.obj)) := by
  classical
  intro X' Y' _ _ _ _ _ _ g p' g' sq K
  -- Keep mapped objects and arrows in the target's syntax: reducing them under
  -- the derived exchange causes expensive kernel conversion.
  let : ((Over.forget (Spec (.of k))).obj X).Over (Spec (.of k)) := ⟨X.hom⟩
  let : LocallyOfFiniteType (((Over.forget (Spec (.of k))).obj X) ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (((Over.forget (Spec (.of k))).obj X) ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated (((Over.forget (Spec (.of k))).obj X) ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated X.hom)
  let : ((Over.forget (Spec (.of k))).obj Y).Over (Spec (.of k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (((Over.forget (Spec (.of k))).obj Y) ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (((Over.forget (Spec (.of k))).obj Y) ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  let : IsSeparated (((Over.forget (Spec (.of k))).obj Y) ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated Y.hom)
  let : ((Over.forget (Spec (.of k))).obj Y').Over (Spec (.of k)) := ⟨Y'.hom⟩
  let : LocallyOfFiniteType (((Over.forget (Spec (.of k))).obj Y') ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y'.hom)
  let : QuasiCompact (((Over.forget (Spec (.of k))).obj Y') ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact Y'.hom)
  let : IsSeparated (((Over.forget (Spec (.of k))).obj Y') ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated Y'.hom)
  let : ((Over.forget (Spec (.of k))).map p).IsOver (Spec (.of k)) := ⟨p.w⟩
  let : ((Over.forget (Spec (.of k))).map g).IsOver (Spec (.of k)) := ⟨g.w⟩
  let : IsProper ((Over.forget (Spec (.of k))).map p) := hp
  exact properImage_exchange_scheme ℓ Λ hΛ k
    ((Over.forget (Spec (.of k))).map p) ((Over.forget (Spec (.of k))).map g)
    (sq.map (Over.forget (Spec (.of k)))) K.obj K.property

private theorem properImage_baseChange_clause
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (hp : IsProper p.left) :
    (∀ {X' Y' : Over (Spec (.of k))}
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
      {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : IsPullback g' p' p g) (K : ConstantModelConstructibleFiniteTor Λ X.left),
      (constantModelBoundedConstructible Λ Y'.left
          ((L((g.left)^*⟦Λ⟧)).obj ((R((p.left)_*⟦Λ⟧)).obj K.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((L((g.left)^*⟦Λ⟧)).obj ((R((p.left)_*⟦Λ⟧)).obj K.obj))) ∧
      (constantModelBoundedConstructible Λ Y'.left
          ((R((p'.left)_*⟦Λ⟧)).obj ((L((g'.left)^*⟦Λ⟧)).obj K.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((R((p'.left)_*⟦Λ⟧)).obj ((L((g'.left)^*⟦Λ⟧)).obj K.obj))) ∧
      IsIso ((baseChangeMap Λ
        (sq.map (Over.forget (Spec (.of k)))).toCommSq).app K.obj)) := by
  classical
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact X.hom)
  let : IsSeparated (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated X.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated Y.hom)
  let : p.left.IsOver (Spec (.of k)) := ⟨p.w⟩
  intro X' Y' _ _ _ _ _ _ g p' g' sq K
  let : X'.left.Over (Spec (.of k)) := ⟨X'.hom⟩
  let : Y'.left.Over (Spec (.of k)) := ⟨Y'.hom⟩
  let : LocallyOfFiniteType (X'.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X'.hom)
  let : QuasiCompact (X'.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact X'.hom)
  let : IsSeparated (X'.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated X'.hom)
  let : LocallyOfFiniteType (Y'.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y'.hom)
  let : QuasiCompact (Y'.left ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact Y'.hom)
  let : IsSeparated (Y'.left ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated Y'.hom)
  let : p'.left.IsOver (Spec (.of k)) := ⟨p'.w⟩
  have hKp := constructibleFiniteTor_rightDerivedLowerStar_of_admissible ℓ k Λ hΛ
    p.left K.obj K.property
  have hleft := properImage_pullback_ctf ℓ k Λ hΛ g.left _ hKp
  have hbc := properImage_exchange (ℓ := ℓ) (Λ := Λ) (p := p) hΛ hp sq K
  let : IsIso ((baseChangeMap Λ
      (sq.map (Over.forget (Spec (.of k)))).toCommSq).app K.obj) := hbc
  have : (constantModelBoundedConstructible Λ Y'.left).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ Y'.left).2.1
  have hright := ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible Λ Y'.left ⊓ DerivedCategory.finiteTorAmplitude _)
    (asIso ((baseChangeMap Λ
      (sq.map (Over.forget (Spec (.of k)))).toCommSq).app K.obj)) hleft
  exact ⟨hleft, hright, hbc⟩

/-- Proper direct image preserves Dctf for every admissible condensed coefficient,
with canonical proper base change in Dctf and the canonical projection formula.

Source: blueprint latest, unit `sk-thm-sfb-proper-base-change`, statement and proof;
Stacks Project, Tags 0F0G, 09B1, 09A6, 0GL0 and 0F10
(blueprint: sk-thm-sfb-proper-base-change).

Proof. Preservation uses the admissible direct-image theorem. The canonical exchange
is identified with the ambient exchange mate and the admissible-generator base-change
lemma applies. That lemma proves the finite, integral, and rational cases separately.
For projection, the proof below explicitly splits the six coefficient cases. The finite
case uses finite proper base change and projection; the integral case uses the integral
proper-formulas theorem (completeness, reduction (5.2), and derived Nakayama); and the rational
cases use the rational proper projection theorem after the constructibility comparison.
Exact coefficient equivalences transport the specified canonical projection maps.
Finally direct image followed by arbitrary pullback puts the source endpoint in Dctf;
closure under isomorphisms transports this property to the target endpoint.
-/
theorem properDirectImage_constructibleFiniteTor
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) (hp : IsProper p.left) :
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      constantModelBoundedConstructible Λ Y.left ((R((p.left)_*⟦Λ⟧)).obj K.obj) ∧
        DerivedCategory.finiteTorAmplitude _ ((R((p.left)_*⟦Λ⟧)).obj K.obj)) ∧
    (∀ {X' Y' : Over (Spec (.of k))}
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
      {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
      (sq : IsPullback g' p' p g) (K : ConstantModelConstructibleFiniteTor Λ X.left),
      (constantModelBoundedConstructible Λ Y'.left
          ((L((g.left)^*⟦Λ⟧)).obj ((R((p.left)_*⟦Λ⟧)).obj K.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((L((g.left)^*⟦Λ⟧)).obj ((R((p.left)_*⟦Λ⟧)).obj K.obj))) ∧
      (constantModelBoundedConstructible Λ Y'.left
          ((R((p'.left)_*⟦Λ⟧)).obj ((L((g'.left)^*⟦Λ⟧)).obj K.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((R((p'.left)_*⟦Λ⟧)).obj ((L((g'.left)^*⟦Λ⟧)).obj K.obj))) ∧
      IsIso ((baseChangeMap Λ
        (sq.map (Over.forget (Spec (.of k)))).toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
      (M : ConstantModelConstructibleFiniteTor Λ Y.left),
      IsIso (moduleObjectProjectionMap Λ p.left K.obj M.obj)) := by
  classical
  exact ⟨properImage_preserves (ℓ := ℓ) (Λ := Λ) (p := p) hΛ hp,
    properImage_baseChange_clause (ℓ := ℓ) (Λ := Λ) (p := p) hΛ hp,
    fun K M ↦ properImage_admissible_projection ℓ k p Λ hΛ K M⟩

end AlgebraicGeometry.ProEtale.CondensedRing
