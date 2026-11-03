/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedDualizableIndependent

/-! # Duals of perfect complexes in the native coefficient category

Source: Stacks Project, Tags 08JI and 08JJ; the local finite-projective argument
in the proof of prop-sf-dualizable.
(blueprint: lem-sf-native-site-perfect-dual).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finite_projective_dual
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [BraidedCategory A]
    [HasFiniteBiproducts A] (M : A) [HasRightDual M]
    (hM : CategoryTheory.finProj A M) : CategoryTheory.finProj A Mᘁ := by
  obtain ⟨n, ⟨r⟩⟩ := hM
  let B := fun _ : Fin n ↦ 𝟙_ A
  let p : ExactPairing (⨁ B) (⨁ B) :=
    Bicone.exactPairing (biproduct.isBilimit B) (biproduct.isBilimit B)
  let : HasRightDual (⨁ B) := { rightDual := ⨁ B, exact := p }
  refine ⟨n, ⟨{ i := r.rᘁ, r := r.iᘁ, retract := ?_ }⟩⟩
  rw [← comp_rightAdjointMate, r.retract, rightAdjointMate_id]

private theorem bounded_dual_pairing
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{w} A] [Abelian.HasFunctorialFlatResolution A]
    (P : CochainComplex A ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ n, HasRightDual (P.X n)] :
    Nonempty (ExactPairing (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P.rightDual)) := by
  let : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let F : W.kFlat.FullSubcategory ⥤ DerivedCategory A := W.kFlat.ι ⋙ DerivedCategory.Qh
  have : IsIso (Functor.LaxMonoidal.ε F) := by
    dsimp only [F]
    rw [Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_ε,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact inferInstanceAs
      (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal DerivedCategory.Qh W)))
  have (U V : W.kFlat.FullSubcategory) : IsIso (Functor.LaxMonoidal.μ F U V) := by
    dsimp only [F]
    rw [Functor.LaxMonoidal.comp_μ, ObjectProperty.ι_μ,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      DerivedCategory.Qh W U.obj V.obj U.property
  let _ := Functor.Monoidal.ofLaxMonoidal F
  have hP (n : ℤ) : IsDualizable (P.X n) := ⟨inferInstance⟩
  have hd (n : ℤ) : IsDualizable (P.rightDual.X n) :=
    ⟨{ rightDual := P.X (-n)
       exact := BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ }⟩
  let U : W.kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hP n).flat))⟩
  let V : W.kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a) (fun n ↦ (hd n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj U) ((ObjectProperty.ι _).obj V) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing U V := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) U V
  let _ : ExactPairing (F.obj U) (F.obj V) := ExactPairing.map F U V
  exact ⟨exactPairingCongr (X' := F.obj U) (Y' := F.obj V)
    ((DerivedCategory.quotientCompQhIso A).app P).symm
    ((DerivedCategory.quotientCompQhIso A).app P.rightDual).symm⟩

/-- The native coefficient dual of a site-perfect complex is site-perfect, and the
closed evaluation is the evaluation of an exact pairing.
Source: Stacks Project, Tags 08JI and 08JJ; blueprint prop-sf-dualizable, local
finite-projective models (blueprint: lem-sf-native-site-perfect-dual).

Proof: a finite-projective term is a retract of a finite sum of units and hence
is dualizable. Its dual is a retract of that same sum: take adjoint mates of the
two retraction maps, using the sum of the unit self-pairings. A bounded model P
therefore has its signed termwise dual P.rightDual, bounded in the opposite
interval and again termwise finite projective. Both complexes are K-flat, and
localization transports their exact pairing. Dualizability descends along the
pro-etale model cover. Its canonical closed dual has exactly the closed evaluation.
Pull that pairing back to each covering scheme. Uniqueness of left duals identifies
the pullback with the localized signed dual model, proving site-perfectness of
the coefficient dual. The argument allows empty covers, zero complexes and the
zero coefficient ring. -/
theorem native_sitePerfect_dual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) (hK : IsPerfectOnCoefficientSite Λ Y K) :
    IsPerfectOnCoefficientSite Λ Y ((ihom K).obj (𝟙_ _)) ∧
      ∃ ep : ExactPairing ((ihom K).obj (𝟙_ _)) K,
        ep.evaluation' = (ihom.ev K).app (𝟙_ _) := by
  obtain ⟨C, hC⟩ := hK
  let _ : BraidedCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :=
    (DerivedCategory.nonempty_braidedCategory _).some
  let _ (i : C.I₀) : BraidedCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
        (condensedRingObj Λ (C.X i)))) := (DerivedCategory.nonempty_braidedCategory _).some
  have hdual : IsDualizable K := by
    apply isDualizable_of_cover C
    intro i
    obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := hC i
    let := ha
    let := hb
    have ht (n : ℤ) : IsDualizable (P.X n) := (CategoryTheory.finProj.isDualizable (hP n))
    exact (DerivedCategory.isDualizable_Q_obj_independent P a b ht).of_iso
      (((leftDerivedUpperStarIsoMapDerivedCategory Λ (C.f i)).app K) ≪≫ eP).symm
  let := (MonoidalClosed.isDualizable_iff_isIso_ihomUnitTensorToIhom K).1 hdual
  let ep := MonoidalClosed.exactPairingOfIsIso K
  refine ⟨⟨C, fun i ↦ ?_⟩, ep, rfl⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := hC i
  let := ha
  let := hb
  let _ (n : ℤ) : HasRightDual (P.X n) := (CategoryTheory.finProj.isDualizable (hP n)).some
  obtain ⟨pP⟩ := bounded_dual_pairing P a b
  let _ := pP
  let pD := BraidedCategory.exactPairing_swap (DerivedCategory.Q.obj P)
    (DerivedCategory.Q.obj P.rightDual)
  let localPair := exactPairingCongr (X' := DerivedCategory.Q.obj P.rightDual)
    (Y' := DerivedCategory.Q.obj P) (Iso.refl _)
    ((((leftDerivedUpperStarIsoMapDerivedCategory Λ (C.f i)).app K) ≪≫ eP))
  obtain ⟨j⟩ := nonempty_leftDerivedUpperStar_obj_iso_of_exactPairing (C.f i) ep localPair
  refine ⟨P.rightDual, -b, -a, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · intro n
    exact finite_projective_dual (P.X (-n)) (hP (-n))
  · exact ((leftDerivedUpperStarIsoMapDerivedCategory Λ (C.f i)).app _).symm ≪≫ j

end AlgebraicGeometry.ProEtale.CondensedRing
