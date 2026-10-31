/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.RationalOpenDirectImageConstructible
import WeilConjectures.NumberTheory.Padics.BaseCoefficientCondensedIdentification
import WeilConjectures.SixFunctors.CompactificationOverField
import WeilConjectures.SixFunctors.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!
# Admissible-coefficient ordinary direct image

The open/proper argument of det-thm-sf-ctf-stability-direct-images is separate from
extension by zero, compact support, and exceptional inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.Limits

attribute [local irreducible] upperStarFromPoint Functor.rightDerivedFunctor
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse

private abbrev ImageCtf
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ K : ConstantModelConstructibleFiniteTor Λ X,
    (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _)
      ((R((f)_*⟦Λ⟧)).obj K.obj)

private theorem imageCtf_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ImageCtf Λ' f) : ImageCtf Λ f := by
  let a : Λ ⟶ Λ' := e.hom.hom
  have : IsMonHom a := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso a := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  let E₀ (Z : Scheme.{u}) :=
    Mod.comapEquivalenceOfIsIso (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap a Z)
  have (Z : Scheme.{u}) : (E₀ Z).functor.Additive :=
    inferInstanceAs (Mod.comap (coefficientMap a Z)).Additive
  have (Z : Scheme.{u}) : (E₀ Z).inverse.Additive :=
    inferInstanceAs (Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (asIso (coefficientMap a Z)).inv).Additive
  let E (Z : Scheme.{u}) := (E₀ Z).mapDerivedCategory
  have (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let F := (lowerStar Λ f).rightDerivedFunctor
  let F' := (lowerStar Λ' f).rightDerivedFunctor
  let i : (E X).inverse ⋙ F' ⋙ (E Y).functor ≅ F :=
    Functor.isoWhiskerLeft (E X).inverse (derivedComapLowerStarIso a f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E X).counitIso F ≪≫ F.leftUnitor
  have hinv (Z : Scheme.{u}) :
      coefficientMap (asIso a).inv Z = inv (coefficientMap a Z) := by
    simp only [asIso_inv]
    exact Functor.map_inv (upperStarFromPoint Z) a
  intro K
  have hK' := constantModelCtf_coefficientIso (Mon.mkIso' (asIso a)) X K
  change (constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _)
    ((Mod.comap (coefficientMap (asIso a).inv X)).mapDerivedCategory.obj K.obj) at hK'
  simp only [hinv] at hK'
  have ht := h ⟨(E X).inverse.obj K.obj, hK'⟩
  have ht' := constantModelCtf_coefficientIso (Mon.mkIso' (asIso a)).symm Y
    ⟨F'.obj ((E X).inverse.obj K.obj), ht⟩
  have : (constantModelBoundedConstructible Λ Y).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ Y).2.1
  exact ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _) (i.app K.obj) ht'

section OpenImage

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]

include ℓ k

private theorem imageCtf_finite
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) :
    ImageCtf (Profinite.continuousMapRingObj A) j := by
  classical
  let B := ULift.{u} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have hB : ∃ n : ℕ, 1 ≤ n ∧ (ℓ : B) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
    apply ULift.ext
    change (ℓ : A) ^ (n + 1) = 0
    have h : (ℓ : A) ^ n = 0 := by
      simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn (1 : A)
    rw [pow_succ, h, zero_mul]
  let e : A ≃+* B := ULift.ringEquiv.symm
  let h : Profinite.continuousMapRingSheaf.{u} A ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheafOfUniverse.{u, u} B ⟶
      Profinite.continuousMapRingSheaf.{u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let eR : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let e' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e'.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  let eb : Mon.mk (Profinite.continuousMapRingObj A) ≅
      Mon.mk (Profinite.continuousMapRingObjOfUniverse.{u, u} B) := Mon.mkIso' e'
  apply imageCtf_coefficientIso eb j
  obtain ⟨d, _, hd⟩ := finiteOpenDirectImage_constantModel_torAmplitude
    ℓ (ringChar k) k (Fact.out : (ringChar k).Prime).pos Fact.out B hB j
  intro K
  obtain ⟨a, b, ht⟩ := K.property.2
  have ht' := ht.mono (min_le_left a b) (le_max_left b a)
  obtain ⟨hbc, htor⟩ := hd (min a b) (max b a) (by omega) K.obj K.property.1 ht'
  exact ⟨hbc, min a b, max b a + d, htor⟩

private theorem imageCtf_integral (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ImageCtf (Profinite.padicIntegersRingObj ℓ E) j := by
  intro K
  exact integralOpenDirectImage ℓ E k j K

private theorem imageCtf_rational (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ImageCtf (Profinite.continuousMapRingObj E) j ∧
      ImageCtf (Profinite.padicAlgClRingObj ℓ) j := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  obtain ⟨hE, hcl⟩ := constantModelBoundedConstructible_rational_open_direct_image ℓ k E j
  constructor
  · intro K
    have heq := (localizingClosure_ctf_equals_bc ℓ X
      (Profinite.continuousMapRingObj E)
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩)))).1.2.2.1
    exact (congrFun heq _).mpr (hE K.obj K.property.1)
  · intro K
    have heq := (localizingClosure_ctf_equals_bc ℓ X (Profinite.padicAlgClRingObj ℓ)
      (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
    exact (congrFun heq _).mpr (hcl K.obj K.property.1)

private theorem imageCtf_admissible_open
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) : ImageCtf Λ j := by
  let E₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ℓ
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, hA, ⟨e⟩⟩ := h
    have : Finite A := hfin
    exact imageCtf_coefficientIso e j (imageCtf_finite ℓ k j A hA)
  · obtain ⟨e⟩ := h
    exact imageCtf_coefficientIso (e ≪≫ zIso) j (imageCtf_integral ℓ k j E₀)
  · obtain ⟨e⟩ := h
    exact imageCtf_coefficientIso (e ≪≫ qIso) j (imageCtf_rational ℓ k j E₀).1
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact imageCtf_coefficientIso e j (imageCtf_rational ℓ k j E).1
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact imageCtf_coefficientIso e j (imageCtf_integral ℓ k j E)
  · obtain ⟨e⟩ := h
    exact imageCtf_coefficientIso e j (imageCtf_rational ℓ k j E₀).2

end OpenImage

/-- Ordinary derived direct image preserves constructible finite-Tor objects at every
admissible coefficient stage.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
det-thm-sf-ctf-stability-direct-images, proof steps 5--9
(blueprint: lem-sfb-admissible-direct-image).

Proof:
1. All schemes in the standing setting are Noetherian and qcqs. Choose a compactification
f = j ≫ p with j quasi-compact open and p proper; its intermediate scheme is again separated
of finite type over k. Ringed-topos derived pushforward composition identifies Rf_* with
Rj_* followed by Rp_* for the cartesian coefficient sheaves.
2. For finite A descend K through finiteTorComparisonNoetherian, retaining a Tor interval
[a,b]. Etale open direct-image finiteness makes Rj_*K bounded constructible. Finite
torsion etale cohomological dimension supplies a uniform bound d for j on all A-module
sheaves. Finite A-modules are finitely presented, so the finite-constant projection formula
applies. open_tor_bound_arbitrary_field gives interval [a,b+d] against every module sheaf.
ComparisonDirectImage and ComparisonTorInterval transport both conclusions to the
pro-etale site. This argument includes the zero ring and zero complex.
3. For O_E use integralOpenDirectImage. For E and the finite-subextension algebraic closure,
use integral generators, exact conservative scalar restriction, and bounded continuity of
direct image: localization commutes with Rj_* on the bounded integral generators, and finite
free scalar extension commutes with Rj_* by additivity. Pass to the degree-zero filtered
coefficient system. Exact filtered colimits preserve cohomology and the same finite
presentations. Finite cones and shifts give bounded constructibility; ctf_equals_bc gives
finite Tor amplitude. For the retained all-continuous algebraic-closure coefficient,
use the lisse integral lattices and the bounded-continuity argument directly for that
coefficient, with the same finite stratification and cohomological bounds; no uniform
finite-extension descent for its local systems is asserted. This requires the continuous
coefficient version of the integral/rational finiteness argument, rather than an
identification of the two algebraic-closure coefficient sheaves.
4. Proper direct image preserves Dctf by finiteProperLocalizing for finite coefficients,
integralProperDirectImageAndFormulas for O_E, and the rational proper direct-image theorem
for E and the algebraic closure. Use Dctf = Dbc only for integral and rational coefficients.
Apply this to the result of steps 2--3 and compose the isomorphism of step 1. Finally
transport through the ring-object isomorphism in hΛ: exact scalar equivalences preserve
finite constant presentations and all Tor tests, and commute with derived direct image.
-/
theorem constructibleFiniteTor_rightDerivedLowerStar_of_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible Λ Y ((R((f)_*⟦Λ⟧)).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((R((f)_*⟦Λ⟧)).obj K) := by
  classical
  let c := (AlgebraicGeometry.compactificationOverField k f).obj.obj
  have : QuasiCompact c.i :=
    (AlgebraicGeometry.compactificationOverField k f).obj.property
  have ho := imageCtf_admissible_open ℓ k c.i Λ hΛ ⟨K, hK⟩
  have hp := (properLocalizingHypotheses_admissible ℓ Λ hΛ k c.g).1
    ⟨_, ho⟩
  have : (constantModelBoundedConstructible Λ Y).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ Y).2.1
  have e : ((R((c.i)_*⟦Λ⟧)) ⋙ R((c.g)_*⟦Λ⟧)).obj K ≅
      (R((f)_*⟦Λ⟧)).obj K := by
    simpa only [← c.comm] using (rightDerivedLowerStarComp Λ c.i c.g).app K
  exact ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _) e hp

end AlgebraicGeometry.ProEtale.CondensedRing
