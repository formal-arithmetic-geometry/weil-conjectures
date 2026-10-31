/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude

import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import Mathlib.Algebra.Field.ULift
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology

/-! # Finite Tor amplitude at condensed field coefficients

Source: current blueprint `lem-integral-ctf-equals-bc`, field case of clause (2).
This specializes the local-model and truncation argument to the two field coefficient
families, in the ordinary derived category over the pulled-back condensed ring.
(blueprint: lem-weil-field-tor-amplitude).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

section DiscreteField

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Limits MonoidalCategory in
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- A bounded complex over a discrete constant field has Tor amplitude in its
cohomological interval. This existing helper is retained for the residue-field consumers.

Source: Stacks Project, Tags 08FZ and 010N; constant-field tensor cohomology
`lem-exc-constant-field-sheaf-tensor-cohomology`.
(blueprint: lem-weil-field-tor-amplitude).

Proof: a quasi-isomorphic representative has the same cohomology as `K`. Exact tensor
over the constant field commutes with cohomology. The sheafification counit and tensorator
identify this exact tensor with the tensor used by `derivedTensor`, and the comparison
with the total complex having one degree-zero factor gives the asserted vanishing. -/
theorem bounded_field_tor (Y : Scheme.{u}) (A : Type u) [Field A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    HasProEtaleTorAmplitude Y A K a b := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} A))
  let C := SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := HasDerivedCategory.standard C
  let := SheafOfModules.cochainTensorLocalizationIsMonoidal.{u + 1, u, u + 1}
    (C := Y.ProEt) (J := ProEt.topology Y) R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  change a ≤ b ∧ _
  refine ⟨hab, ?_⟩
  intro L P hL f hf hP M i hi
  have : QuasiIso f := hf
  obtain ⟨eL⟩ := hL
  have hPi : IsZero (P.homology i) := by
    let e := (DerivedCategory.homologyFunctor C i).mapIso
      (asIso (DerivedCategory.Q.map f) ≪≫ eL)
    exact ((hK i hi).of_iso e).of_iso
      ((DerivedCategory.homologyFunctorFactors C i).app P).symm
  obtain ⟨e, _⟩ := SheafOfModules.exists_constantFieldTensorCohomology
    (ProEt.topology Y) (ULift.{u + 1} A) i
  have hz := ((SheafOfModules.siteSheafTensorRight M).map_isZero hPi).of_iso (e M P).symm
  let T := (tensorRight M).mapHomologicalComplex (.up ℤ)
  let S := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let F := PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)
  let p (N : PresheafOfModules.{u + 1} S.obj) :
      (N ⊗ M.val : PresheafOfModules.{u + 1} S.obj) ≅
        SheafOfModules.siteTensorPresheaf N M.val :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl)
  let V := SheafOfModules.forget S
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)
  let e := asIso adj.counit
  let c₁ : tensorRight M ≅ V ⋙ tensorRight M.val ⋙ F :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft V
        (Functor.isoWhiskerLeft F ((curriedTensor C).flip.mapIso (e.app M).symm) ≪≫
          Functor.Monoidal.commTensorRight F M.val)
  let q : tensorRight M.val ≅ SheafOfModules.siteTensorRight M.val :=
    NatIso.ofComponents p (by
      intro N N' f
      ext U : 1
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl)
  let c := c₁ ≪≫ Functor.isoWhiskerLeft V (Functor.isoWhiskerRight q F)
  have : (V ⋙ SheafOfModules.siteTensorRight M.val ⋙ F).PreservesZeroMorphisms := by
    change (SheafOfModules.siteSheafTensorRight M).PreservesZeroMorphisms
    infer_instance
  have ht : IsZero ((T.obj P).homology i) :=
    hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((NatIso.mapHomologicalComplex c (.up ℤ)).app P))
  let t := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P
  exact (ht.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso t)).of_iso
    ((DerivedCategory.homologyFunctorFactors C i).app _)

end DiscreteField

/-- Bounded constructible complexes over the condensed field `E` or the
finite-subextension-valued condensed algebraic closure have Tor amplitude in their
cohomological interval. Consequently every such object has a single finite Tor interval
for all degree-zero module sheaves, and `Dctf = Dbc` as full subcategories of the same
ordinary derived category.

The hypotheses on `Y` hold for every standing scheme: finite type over a field gives
quasi-compactness and local Noetherianity, and separatedness gives quasi-separatedness.
The statement is also valid for every Noetherian qcqs scheme, without a base field or a
characteristic restriction.

Source: blueprint latest, sec-proetale-coefficients/sk-prop-integral-criterion,
`lem-integral-ctf-equals-bc`, clause (2), Local models, Strata and Complexes paragraphs.
(blueprint: lem-weil-field-tor-amplitude).

Proof: compare the stratified locally finitely presented constructibility predicate with
finite constant local models on the Noetherian scheme. A finite constant model over either
field has Tor amplitude [0,0]. Uniform-interval stratified devissage gives the same bound
for every constructible cohomology module. Apply the cohomology Tor-interval theorem with
[c,d]=[0,0]; its finite truncation argument gives exactly [a,b], chosen before any test
module. Boundedness supplies lower and upper bounds; replace the lower bound by its minimum
with the upper bound to order the interval, including for the zero object. Thus every
bounded constructible object has finite Tor amplitude. Extensionality and the definition
of the intersection give equality of the object predicates, hence of their full
subcategories. No completeness or constructibility hypothesis is imposed on test modules. -/
theorem field_tor_amplitude
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsLocallyNoetherian Y]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
      (a b : ℤ), a ≤ b → boundedConstructible (condensedRingObj Λ.X Y) K →
      DerivedCategory.homologyConcentratedIn a b K →
        DerivedCategory.torAmplitudeIn _ a b K) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ.X Y) K →
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn _ a b K) ∧
    (boundedConstructible (condensedRingObj Λ.X Y) ⊓
      DerivedCategory.finiteTorAmplitude _) = boundedConstructible (condensedRingObj Λ.X Y) := by
  have hcert : CondensedRing.IsEllAdicCoefficient ℓ Λ.X inferInstance := by
    rcases hΛ with ⟨E, rfl⟩ | rfl
    · let := PadicAlgCl.normedFieldOfAlgebra ℓ E
      exact .continuous E
    · exact .algebraicClosure
  have hfield :
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with ⟨E, rfl⟩ | rfl
    · exact Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)
    · exact Or.inr (Or.inr ⟨Iso.refl _⟩)
  have hcmp := (adicConstructibilityPredicateComparison ℓ Y Λ.X hcert).2
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ.X Y)) (hM : IsConstantModelConstructible Λ.X Y M) :
      DerivedCategory.torAmplitudeIn _ 0 0 ((DerivedCategory.singleFunctor _ 0).obj M) :=
    torAmplitudeIn_of_constructible_of_uniform_local_model ℓ Λ
      (Or.inr (Or.inr (Or.inr hfield))) 0 0 le_rfl
      (fun S N hN ↦ padic_constant_local_model_tor ℓ Λ.X 0
        (Or.inr ⟨rfl, hfield⟩) S N hN) Y M hM
  have hbound (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
      (a b : ℤ) (hab : a ≤ b) (hK : boundedConstructible (condensedRingObj Λ.X Y) K)
      (hcoh : DerivedCategory.homologyConcentratedIn a b K) :
      DerivedCategory.torAmplitudeIn _ a b K := by
    have hK' : constantModelBoundedConstructible Λ.X Y K := (congrFun hcmp K).mp hK
    have ht := torAmplitudeIn_of_cohomology_interval Y Λ K a b 0 0 hab le_rfl
      (fun q hq ↦ by
        by_cases hqa : q < a
        · exact (DerivedCategory.isGE_iff K a).1 hcoh.1 q hqa
        · exact (DerivedCategory.isLE_iff K b).1 hcoh.2 q (by
            simp only [Set.mem_Icc] at hq
            omega))
      (fun q _ ↦ hmod _ (hK'.2 q))
    simpa only [add_zero] using ht
  have hfinite (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)))
      (hK : boundedConstructible (condensedRingObj Λ.X Y) K) :
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn _ a b K := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
    have ha' : K.IsGE (min a b) :=
      (DerivedCategory.isGE_iff K _).2 fun q hq ↦
        (DerivedCategory.isGE_iff K a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))
    exact ⟨min a b, b, min_le_right _ _,
      hbound K (min a b) b (min_le_right _ _) hK ⟨ha', hb⟩⟩
  refine ⟨hbound, hfinite, ?_⟩
  funext K
  apply propext
  constructor
  · exact And.left
  · intro hK
    obtain ⟨a, b, _, ht⟩ := hfinite K hK
    exact ⟨hK, a, b, ht⟩

end WeilConjectures
