/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldStageOrdinaryRealization
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude

import Mathlib.Algebra.Field.ULift
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology

/-! # Finite Tor amplitude at field coefficients

Source: Weil conjectures blueprint, node `lem-weil-field-tor-amplitude`, order 2060
(blueprint: lem-weil-field-tor-amplitude).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open CategoryTheory.Limits MonoidalCategory in
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem bounded_field_tor (Y : Scheme.{u}) (A : Type u) [Field A]
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

/-- Field coefficient objects have the finite-Tor property after their specified
ordinary constant-field realization.  The two clauses correspond respectively to a
finite coefficient stage and to the common-stage algebraically closed coefficient
category.  The interval is chosen independently of the test module sheaf.

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
`lem-weil-field-tor-amplitude`, order 2060, statement and proof
(blueprint: lem-weil-field-tor-amplitude).

Proof:
1. By def-weil-finite-tor-amplitude, the field-stage finite-Tor category is the
bounded constructible category itself. Thus the typed Stage and Pair objects already
belong to that subcategory; no additional membership condition is required.
2. Apply lem-sf-field-stage-ordinary-realization to obtain the specified finite or
closure realization and its cohomological boundedness. Choose an ordered interval
[a,b] outside which its cohomology vanishes, before choosing any test module sheaf.
3. Fix an arbitrary representative L, K-flat resolution P → L and degree-zero
module sheaf M from the tests in def-weil-proetale-tor-amplitude. The resolution
and the derived homology comparison identify H^r(P) with H^r(K). Apply
lem-exc-constant-field-sheaf-tensor-cohomology to P and M over the discrete constant
field sheaf. It identifies termwise tensor cohomology with H^r(P) tensor M,
which is zero outside [a,b] by step 2. The sheafification counit and tensorator
identify the two sheaf tensor presentations naturally. The single-factor total
comparison and derived homology comparison give the desired vanishing for the
derived tensor of def-weil-derived-tensor. This works for every representative and
resolution and for every M, with no constructibility or dimension restriction on M.
By def-weil-proetale-tor-amplitude this is the asserted single Tor interval. -/
theorem field_tor_amplitude
    (D : FiniteFieldDatum.{d})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (Y : Scheme.{u}) :
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E),
        ∃ a b : ℤ, Scheme.HasProEtaleTorAmplitude Y
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E)
          ((OrdinaryFieldRealization.System.finite
            (Classical.choice
              (OrdinaryFieldRealization.exists_ordinaryFieldRealization D l hl Ω Y)) E).obj K)
          a b) ∧
      (∀ (K : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y),
        ∃ a b : ℤ, Scheme.HasProEtaleTorAmplitude Y
          (OrdinaryFieldRealization.Closure l Ω)
          ((OrdinaryFieldRealization.System.closure
            (Classical.choice
              (OrdinaryFieldRealization.exists_ordinaryFieldRealization D l hl Ω Y))).obj K)
          a b) := by
  classical
  let S := Classical.choice
    (OrdinaryFieldRealization.exists_ordinaryFieldRealization D l hl Ω Y)
  constructor
  · intro E K
    obtain ⟨a, b, hab, hK⟩ := S.finite_bounded E K
    exact ⟨a, b, bounded_field_tor Y _ _ a b hab hK⟩
  · intro K
    obtain ⟨a, b, hab, hK⟩ := S.closure_bounded K
    exact ⟨a, b, bounded_field_tor Y _ _ a b hab hK⟩

end WeilConjectures
