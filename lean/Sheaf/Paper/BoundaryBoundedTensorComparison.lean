/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Bounded tensor preparation for boundary comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YQ, 0G7E and 06YU;
proetale.tex, Tag 099R; the small-etale clause of lem-sf-flat-model
(blueprint: lem-sf-boundary-bounded-tensor-comparison).

The coefficient ring is the canonical universe lift of the same quotient A_{E,n}.
Complex tensor is the signed direct-sum total tensor, with second differential
multiplied by (-1)^j in bidegree (j,h). The general quasi-isomorphism-localizer
K-flat predicate applies to the ordinary ModuleCat-valued sheaf presentation;
its acyclic-tensor characterization is HomotopyCategory.kFlat_iff_preserves_acyclic.
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.mapDerivedCategory
  DerivedMonoidal.bifunctor


private theorem coefficientSheafWIsMonoidal (A : Type (w + 1)) [CommRing A]
    (X : Scheme.{w}) : (X.smallEtaleTopology.W (A := ModuleCat.{w + 1} A)).IsMonoidal := by
  exact GrothendieckTopology.W.monoidal

attribute [local instance 2000] coefficientSheafWIsMonoidal

section Preparation

universe a b c

variable {C₁ C₂ : Type a} [Category.{b} C₁] [Category.{b} C₂]
  [Abelian C₁] [Abelian C₂]
  [IsGrothendieckAbelian.{b} C₁] [IsGrothendieckAbelian.{b} C₂]
  [MonoidalCategory C₁] [MonoidalCategory C₂]
  [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
  [MonoidalClosed C₁] [MonoidalClosed C₂]
  [BraidedCategory C₁] [BraidedCategory C₂]
  [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
  [HasDerivedCategory.{c} C₁] [HasDerivedCategory.{c} C₂]
  [HasColimitsOfSize.{0, 0} C₁] [HasColimitsOfSize.{0, 0} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private structure TensorPreparation (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (r s u v : ℤ) (B : _root_.DerivedCategory C₂) (M : _root_.DerivedCategory C₁) where
  K : CochainComplex C₂ ℤ
  V : CochainComplex C₁ ℤ
  hK : ∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j)
  eK : B ≅ _root_.DerivedCategory.Q.obj K
  hVs : ∀ h : ℤ, h < u ∨ v < h → IsZero (V.X h)
  hVf : ∀ h : ℤ, exactFunctor _ _ (tensorRight (V.X h))
  hVk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat V
  hPk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
    ((F.mapHomologicalComplex (.up ℤ)).obj V)
  eV : M ≅ _root_.DerivedCategory.Q.obj V
  eP : F.mapDerivedCategory.obj M ≅
    _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj V)
  eN : B ⊗ F.mapDerivedCategory.obj M ≅ _root_.DerivedCategory.Q.obj
    (CochainComplex.mapBifunctor K ((F.mapHomologicalComplex (.up ℤ)).obj V)
      (curriedTensor C₂))
  hTot : ∀ d : ℤ, d < r + u ∨ s + v < d →
    IsZero ((CochainComplex.mapBifunctor K ((F.mapHomologicalComplex (.up ℤ)).obj V)
      (curriedTensor C₂)).X d)
  hH : ∀ d : ℤ, d < r + u ∨ s + v < d →
    IsZero ((_root_.DerivedCategory.homologyFunctor _ d).obj (B ⊗ F.mapDerivedCategory.obj M))
  hge : (B ⊗ F.mapDerivedCategory.obj M).IsGE (r + u)
  hle : (B ⊗ F.mapDerivedCategory.obj M).IsLE (s + v)

private noncomputable def prepareTensor
    (hF : ∀ (X : C₁), ObjectProperty.flat X → ObjectProperty.flat (F.obj X))
    (r s u v : ℤ)
    (B : _root_.DerivedCategory C₂) (M : _root_.DerivedCategory C₁)
    (hB : ∀ j : ℤ, j < r ∨ s < j →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj B))
    (hM : _root_.DerivedCategory.torAmplitudeIn C₁ u v M) :
    TensorPreparation F r s u v B M := by
  classical
  let model := Classical.choose (_root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hM)
  let V : CochainComplex C₁ ℤ := model
  have spec := Classical.choose_spec
    (_root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hM)
  have hVge : V.IsStrictlyGE u := spec.choose
  have hVle : V.IsStrictlyLE v := spec.choose_spec.choose
  have hVflat : ∀ h : ℤ, ObjectProperty.flat (V.X h) := spec.choose_spec.choose_spec.1
  let eV : _root_.DerivedCategory.Q.obj V ≅ M := spec.choose_spec.choose_spec.2.some
  let := hVge
  let := hVle
  let P : CochainComplex C₂ ℤ := (F.mapHomologicalComplex (.up ℤ)).obj V
  have hVs : ∀ h : ℤ, h < u ∨ v < h → IsZero (V.X h) := by
    intro h hh
    rcases hh with hh | hh
    · exact V.isZero_of_isStrictlyGE u h hh
    · exact V.isZero_of_isStrictlyLE v h hh
  have hPs : ∀ h : ℤ, h < u ∨ v < h → IsZero (P.X h) :=
    fun h hh ↦ F.map_isZero (hVs h hh)
  have : P.IsStrictlyGE u := (P.isStrictlyGE_iff u).2 fun h hh ↦ hPs h (.inl hh)
  have : P.IsStrictlyLE v := (P.isStrictlyLE_iff v).2 fun h hh ↦ hPs h (.inr hh)
  have hPflat : ∀ h : ℤ, ObjectProperty.flat (P.X h) :=
    fun h ↦ hF (V.X h) (hVflat h)
  have hVk := CochainComplex.kFlat_of_bounded_of_flat V u v hVflat
  have hPk := CochainComplex.kFlat_of_bounded_of_flat P u v hPflat
  have eP : F.mapDerivedCategory.obj M ≅ _root_.DerivedCategory.Q.obj P :=
    F.mapDerivedCategory.mapIso eV.symm ≪≫ F.mapDerivedCategoryFactors.app V
  have : B.IsGE r := (_root_.DerivedCategory.isGE_iff B r).2 fun j hj ↦ hB j (.inl hj)
  have : B.IsLE s := (_root_.DerivedCategory.isLE_iff B s).2 fun j hj ↦ hB j (.inr hj)
  have repB := _root_.DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE B r s
  let K : CochainComplex C₂ ℤ := repB.choose
  have hKge : K.IsStrictlyGE r := repB.choose_spec.choose
  have hKle : K.IsStrictlyLE s := repB.choose_spec.choose_spec.choose
  let eK : B ≅ _root_.DerivedCategory.Q.obj K := repB.choose_spec.choose_spec.choose_spec.some
  let := hKge
  let := hKle
  have hKs : ∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j) := by
    intro j hj
    rcases hj with hj | hj
    · exact K.isZero_of_isStrictlyGE r j hj
    · exact K.isZero_of_isStrictlyLE s j hj
  let Tot : CochainComplex C₂ ℤ := CochainComplex.mapBifunctor K P (curriedTensor C₂)
  have hTot : ∀ d : ℤ, d < r + u ∨ s + v < d → IsZero (Tot.X d) := by
    intro d hd
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.mapBifunctor.hom_ext (fun j h hjh ↦ ?_)
    apply IsZero.eq_of_src
    have hjh' : j + h = d := hjh
    by_cases hj : j < r ∨ s < j
    · exact ((curriedTensor C₂).map_isZero (hKs j hj)).obj _
    · exact ((curriedTensor C₂).obj _).map_isZero (hPs h (by omega))
  have : Tot.IsStrictlyGE (r + u) := (Tot.isStrictlyGE_iff _).2
    fun d hd ↦ hTot d (.inl hd)
  have : Tot.IsStrictlyLE (s + v) := (Tot.isStrictlyLE_iff _).2
    fun d hd ↦ hTot d (.inr hd)
  let N := B ⊗ F.mapDerivedCategory.obj M
  have eN : N ≅ _root_.DerivedCategory.Q.obj Tot :=
    tensorIso eK eP ≪≫ _root_.DerivedCategory.QObjTensorQObjIsoOfKFlatRight K P hPk
  have hge : N.IsGE (r + u) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso eN.symm _
  have hle : N.IsLE (s + v) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso eN.symm _
  refine ⟨K, V, hKs, eK, hVs, fun h ↦ (hVflat h).2, hVk, hPk,
    eV.symm, eP, eN, hTot, ?_, hge, hle⟩
  intro d hd
  rcases hd with hd | hd
  · exact (_root_.DerivedCategory.isGE_iff N (r + u)).1 hge d hd
  · exact (_root_.DerivedCategory.isLE_iff N (s + v)).1 hle d hd

private theorem prepareBoundary
    (hF : ∀ (X : C₁), ObjectProperty.flat X → ObjectProperty.flat (F.obj X))
    (r s u v : ℤ) (B : _root_.DerivedCategory C₂) (M : _root_.DerivedCategory C₁)
    (hB : ∀ j : ℤ, j < r ∨ s < j →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj B))
    (hM : _root_.DerivedCategory.torAmplitudeIn C₁ u v M)
    (S : _root_.DerivedCategory.Plus C₂ → Prop) (hS : ∀ Q, S Q) :
    ∃ (K : CochainComplex C₂ ℤ) (V : CochainComplex C₁ ℤ)
      (P : CochainComplex C₂ ℤ) (Q : _root_.DerivedCategory.Plus C₂),
      P = (F.mapHomologicalComplex (.up ℤ)).obj V ∧
      (∀ j : ℤ, j < r ∨ s < j → IsZero (K.X j)) ∧
      Nonempty (B ≅ _root_.DerivedCategory.Q.obj K) ∧
      (∀ h : ℤ, h < u ∨ v < h → IsZero (V.X h)) ∧
      (∀ h : ℤ, exactFunctor _ _ (tensorRight (V.X h))) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat V ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      Nonempty (M ≅ _root_.DerivedCategory.Q.obj V) ∧
      Nonempty (F.mapDerivedCategory.obj M ≅ _root_.DerivedCategory.Q.obj P) ∧
      Q.obj = B ⊗ F.mapDerivedCategory.obj M ∧
      Nonempty (Q.obj ≅ _root_.DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor K P (curriedTensor C₂))) ∧
      (∀ d : ℤ, d < r + u ∨ s + v < d →
        IsZero ((CochainComplex.mapBifunctor K P (curriedTensor C₂)).X d)) ∧
      (∀ d : ℤ, d < r + u ∨ s + v < d →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ d).obj Q.obj)) ∧
      _root_.DerivedCategory.TStructure.t.bounded Q.obj ∧ S Q := by
  classical
  let R := prepareTensor F hF r s u v B M hB hM
  let P := (F.mapHomologicalComplex (.up ℤ)).obj R.V
  let N := B ⊗ F.mapDerivedCategory.obj M
  let Q : _root_.DerivedCategory.Plus C₂ := ⟨N, ⟨r + u, R.hge⟩⟩
  exact ⟨R.K, R.V, P, Q, rfl, R.hK, ⟨R.eK⟩, R.hVs, R.hVf, R.hVk, R.hPk,
    ⟨R.eV⟩, ⟨R.eP⟩, rfl, ⟨R.eN⟩, R.hTot, R.hH,
    ⟨⟨r + u, R.hge⟩, ⟨s + v, R.hle⟩⟩, hS Q⟩

end Preparation

set_option linter.unusedVariables false in
/-- Bounded representatives and the specified invertible comparison for their tensor.
Source: Stacks Project, sites-cohomology.tex, Tags 06YQ, 0G7E, 06YU; proetale.tex,
Tag 099R; lem-sf-flat-model, small-etale clause
(blueprint: lem-sf-boundary-bounded-tensor-comparison).

Proof:
1. Apply lem-sfb-bounded-representative in ordinary A-module etale sheaves to B
   and [r,s]. This uses no Tor hypothesis on B.
2. Apply lem-sf-flat-model on T to M and [u,v]. Its flat terms give exact tensor
   functors by right exactness (lem-weil-pbc-independent-sheaf-tensor-colimits)
   and symmetry (def-pur-sheaf-tensor-product). Bounded-above flat complexes are
   K-flat by lem-pc-bounded-above-flat-kflat-site.
3. The constant-coefficient inverse image is exact by
   prop-weil-pbc-inverse-image-modules-exact. Its derived factorization
   (lem-weil-pbc-exact-functor-derived-factorization) identifies termwise lV
   with lM. Apply lem-weil-pbc-ringed-topos-kflat-pullback (0G7E) to V.
4. The right-factor clause of lem-trf-site-one-sided-tensor-normalization
   identifies the signed total B' tensor lV with B tensor-derived lM, even
   though B' need not be flat or K-flat.
5. A nonzero total summand has j in [r,s], h in [u,v], and j+h=d. Hence the
   total is zero outside [r+u,s+v], and its cohomology has the same bound.
   This gives bounded and bounded-below membership of the actual tensor Q.
6. A closed immersion is proper (lem-weil-pbc-closed-immersion-proper), hence
   quasi-compact and separated, and therefore quasi-separated by
   lem-pc-separated-quasi-separated.
7. The coefficient ring is finite by def-weil-l-adic-coefficient-extension.
   Apply lem-weil-pbc-comparison-direct-image-canonical-mate to this Q in D+.
   It proves invertibility of the named mate. The argument includes zero
   inputs, the empty scheme, and singleton intervals; it never requires
   finite Tor amplitude of B or locally free terms of V. -/
theorem boundary_bounded_tensor_comparison
    (D : WeilConjectures.FiniteFieldDatum.{w})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) :
    (fun (A : Type (w + 1)) [inst : CommRing A] [fin : Finite A] ↦
    ∀ (Z T : Scheme.{w}) [Z.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    (i : Z ⟶ T) [i.IsOver (Spec (.of D.k))] [IsClosedImmersion i]
    (r s u v : ℤ) (_hrs : r ≤ s) (_huv : u ≤ v)
    (B : DerivedCategoryModule A Z)
    (M : DerivedCategoryModule A T)
    (_hB : DerivedCategory.isBoundedConstructible A Z B)
    (_hM : DerivedCategory.isBoundedConstructible A T M)
    (_hBrs : ∀ j : ℤ, j < r ∨ s < j →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ j).obj B))
    (_hMuv : DerivedCategory.hasTorAmplitudeIn A T u v M),
    ∃ (B' : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{w + 1} A)) ℤ)
      (V : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{w + 1} A)) ℤ)
      (lV : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{w + 1} A)) ℤ)
      (Q : _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{w + 1} A))),
      lV = ((upperStar (ModuleCat.{w + 1} A) i).mapHomologicalComplex (.up ℤ)).obj V ∧
      (∀ j : ℤ, j < r ∨ s < j → IsZero (B'.X j)) ∧
      Nonempty (B ≅ _root_.DerivedCategory.Q.obj B') ∧
      (∀ h : ℤ, h < u ∨ v < h → IsZero (V.X h)) ∧
      (∀ h : ℤ, exactFunctor _ _ (tensorRight (V.X h))) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat V ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat lV ∧
      Nonempty (M ≅ _root_.DerivedCategory.Q.obj V) ∧
      Nonempty (((upperStar (ModuleCat.{w + 1} A) i).mapDerivedCategory).obj M ≅
          _root_.DerivedCategory.Q.obj lV) ∧
      Q.obj = ((derivedTensor (ModuleCat.{w + 1} A) Z).obj B).obj
          (((upperStar (ModuleCat.{w + 1} A) i).mapDerivedCategory).obj M) ∧
      Nonempty (Q.obj ≅ _root_.DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor B' lV (curriedTensor _))) ∧
      (∀ d : ℤ, d < r + u ∨ s + v < d →
        IsZero ((CochainComplex.mapBifunctor B' lV (curriedTensor _)).X d)) ∧
      (∀ d : ℤ, d < r + u ∨ s + v < d →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ d).obj Q.obj)) ∧
      (_root_.DerivedCategory.TStructure.t).bounded Q.obj ∧
      IsIso ((ProEtale.fixedComparisonDirectImageMatePlus A i).app Q))
      (ULift.{w + 1, w} (Padic.coefficientExtensionRing l E n))
      (inst := inferInstance)
      (fin := Equiv.ulift.finite_iff.mpr
        (Padic.finite_coefficientExtensionRing l E n hn)) := by
  classical
  intro Z T _ _ _ _ _ _ _ _ i _ _ r s u v hrs huv B M hB hM hBrs hMuv
  let A := ULift.{w + 1, w} (Padic.coefficientExtensionRing l E n)
  let : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E n hn)
  have hMuv' :=
    (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn (Λ := A) (X := T)
      (a := u) (b := v) (K := M)).1 hMuv
  exact prepareBoundary (upperStar (ModuleCat.{w + 1} A) i)
    (fun X hX ↦ Functor.PreservesFlat.flat_obj
      (F := upperStar (ModuleCat.{w + 1} A) i) hX) r s u v B M hBrs hMuv'
    (fun Q ↦ IsIso ((ProEtale.fixedComparisonDirectImageMatePlus A i).app Q))
    (fun Q ↦ by
      have := ProEtale.isIso_fixedComparisonDirectImageMatePlus A i
      infer_instance)

end AlgebraicGeometry.Etale
