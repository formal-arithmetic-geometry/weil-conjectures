/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Tor bounds over a constant field sheaf

Source: blueprint main-20261015, sk-lem-integral-models.proof, first paragraph;
Stacks Project, Tags 03ER, 08FC, 010N, 06YS and 08FZ
(blueprint: lem-sfb-constant-field-tor-bounds).

The existing coefficient-sized small representative accommodates every enclosing
coefficient universe. All objects are intrinsic module sheaves over the constant ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Over a constant field sheaf, cohomological support and Tor amplitude have exactly
 the same ordered interval. No finiteness or enough-points hypothesis is used.

Source: blueprint main-20261015, sk-lem-integral-models.proof, first paragraph;
Stacks Tags 03ER, 08FC, 010N, 06YS and 08FZ
(blueprint: lem-sfb-constant-field-tor-bounds).

Proof:
1. Every module sheaf M over the constant field is flat by
lem-exc-constant-field-module-flat. The site/monoidal tensor comparison therefore
makes tensorRight M exact, so it commutes with cohomology (Stacks Tag 010N).
2. For any representative Q(P) isomorphic to B, derived cohomology agrees with the
cohomology of P. The total tensor P tensor M[0] is isomorphic to termwise tensoring
P with M. Its cohomology is thus H^i(P) tensor M, zero whenever H^i(B) is zero.
This verifies every K-flat representative in the Tor predicate, with the same bounds.
3. Conversely choose a K-flat resolution P of an arbitrary representative of B
by lem-pc-kflat-resolution and test with the coefficient module. The canonical
right unit isomorphism identifies P tensor R[0] with P. The resulting cohomology
vanishing transfers to B through the localization cohomology comparison.
4. No bounded representative, enough-points assumption, or geometric finiteness
condition is required. -/
theorem constant_field_tor_bounds (X : Scheme.{u})
    (κ : Type (max v (u + 1))) [Field κ]
    (B : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ))
    (a b : ℤ) (hab : a ≤ b) :
    (∀ i : ℤ, i < a ∨ b < i →
      IsZero ((coefficientModelCohomology
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ) i).obj B)) ↔
      HasCoefficientProEtaleTorAmplitude X κ B a b := by
  classical
  let J := coefficientProEtaleModelTopology.{u, v} X
  let R := ConstantCompletion.constant J κ
  let A := ConstantCompletion.Mod R
  let : Category.{max v (u + 1)} A := inferInstance
  let : HasSheafify J AddCommGrpCat.{max v (u + 1)} :=
    coefficientModelAdditiveSheafify X
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max v (u + 1)} := inferInstance
  let : Abelian A := SheafOfModules.instAbelian.{max v (u + 1), max v (u + 1),
    max v (u + 1), max v (u + 1)} _
  let : HasDerivedCategory.{max v (u + 1) + 1} A := HasDerivedCategory.standard A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.cochainModulesPreadditive R
  have hcoh (P : CochainComplex A ℤ) (e : (ConstantCompletion.Q R).obj P ≅ B)
      (i : ℤ) : (coefficientModelCohomology R i).obj B ≅ P.homology i :=
    (coefficientModelCohomology R i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors A i).app P
  constructor
  · intro h
    refine ⟨hab, ?_⟩
    intro P _ ⟨e⟩ M i hi
    have hp : IsZero (P.homology i) := (h i hi).of_iso (hcoh P e i).symm
    have hf : exactFunctor A A (MonoidalCategory.tensorRight M) :=
      (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M)
        (SheafOfModules.isFlat_constantFieldModule J κ M)
    have := hf.preservesFiniteLimits
    have := hf.preservesFiniteColimits
    let F := MonoidalCategory.tensorRight M
    let t := CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor A) M P
    let c := (HomologicalComplex.homologyFunctor A (.up ℤ) i).mapIso t ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) i).app P
    exact (F.map_isZero hp).of_iso c
  · intro h
    let L := (ConstantCompletion.Q R).objPreimage B
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients L
    have : QuasiIso p := hp
    let e : (ConstantCompletion.Q R).obj P ≅ B :=
      asIso ((ConstantCompletion.Q R).map p) ≪≫
        (ConstantCompletion.Q R).objObjPreimageIso B
    intro i hi
    have hz := h.2 P hP ⟨e⟩
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) i hi
    have hpz : IsZero (P.homology i) := hz.of_iso
      ((HomologicalComplex.homologyFunctor A (.up ℤ) i).mapIso
        (ringedKoszulRightUnitIso R P)).symm
    exact hpz.of_iso (hcoh P e i)

/-- Finite Tor amplitude over the constant field is equivalent to bounded cohomology.
The ordered interval is a single common bound for every test module sheaf.

Source: blueprint main-20261015, sk-lem-integral-models.proof, first paragraph;
Stacks Tag 08FZ (blueprint: lem-sfb-constant-field-tor-bounds).

Proof: apply constant_field_tor_bounds to each ordered integer interval and take
existence of its endpoints. This is proof step 4 of the node. The zero object works
in every ordered interval, including [0,0], and no geometric hypothesis enters. -/
theorem constant_field_finite_tor_amplitude_iff (X : Scheme.{u})
    (κ : Type (max v (u + 1))) [Field κ]
    (B : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) κ)) :
    HasFiniteCoefficientProEtaleTorAmplitude X κ B ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((coefficientModelCohomology
          (ConstantCompletion.constant
            (coefficientProEtaleModelTopology.{u, v} X) κ) i).obj B) := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, h.1, (constant_field_tor_bounds X κ B a b h.1).2 h⟩
  · rintro ⟨a, b, hab, h⟩
    exact ⟨a, b, (constant_field_tor_bounds X κ B a b hab).1 h⟩

end AlgebraicGeometry.Scheme
