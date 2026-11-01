/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.SixFunctors.SignedDerivedInternalHomExact
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Signed exact shifts for an arbitrary normalized rational Verdier datum

Restrict the signed ambient internal-Hom shift and localize it. The comparison
with the given datum uses its object and pure-tensor formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
  (A : Datum D l hl X E w)

/-- The integral full-subcategory comparison is the identity on ambient Hom. -/
def integralDualComparison :
    IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves ⋙
        (sfIntegralConstructible l E X).ι ≅
      (sfIntegralConstructible l E X).ι.op ⋙ IntegralVerdier.dual l E X w.omega.obj :=
  Iso.refl _

/-- The localization comparison is fixed by the datum's integral object formula. -/
def localizationDualComparison :
    (sfRationalConstructibleLocalization l E X).op ⋙ A.dual ≅
      IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves ⋙
        sfRationalConstructibleLocalization l E X :=
  NatIso.ofComponents (fun K ↦ eqToIso (A.objects _)) (by
    intro K M f
    apply (by
      intro C hC A A' B B' hA hB f g h
      cases hA; cases hB; cases h
      simp : ∀ {C : Type _} [Category C] {A A' B B' : C}
        (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'},
        HEq f g → f ≫ eqToHom hB = eqToHom hA ≫ g) (A.objects _) (A.objects _)
    exact A.pure M.unop K.unop f.unop 1)

/-- Restriction and raw scalar localization preserve the signed exact Hom shift.
Source: Stacks Tags 08JC and 0A8X, and blueprint thm-coef-qbar-verdier steps 3--4.
(blueprint: lem-coef-rational-verdier-signed-shift-X3).

Proof: choose the ambient signed Hom shift with its degree-one reindexing formula.
The full constructible inclusion transports that shift to the restricted integral
Hom and detects distinguished triangles. The object and pure-tensor formulas give
the displayed localization comparison for the supplied datum, independently of
any previously chosen exact shift. Localize the restricted shift using the
universal property of scalar localization. Its comparison commutes with shifts,
and exactness descends through the exact essentially surjective localization.
Both comparisons therefore retain the signed ambient normalization. -/
theorem signedShift_exists :
    ∃ a : (IntegralVerdier.dual l E X w.omega.obj).CommShift ℤ,
    ∃ i : (IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves).CommShift ℤ,
    ∃ t : A.dual.CommShift ℤ,
      (letI := a; (IntegralVerdier.dual l E X w.omega.obj).IsTriangulated) ∧
      (∀ K : IntegralVerdier.Ambient l E X,
        (a.commShiftIso (1 : ℤ)).hom.app (op K) =
          -(CategoryTheory.RingedHomUniverses.sourceShift (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) K (-1)).inv.app
              w.omega.obj) ∧
      (letI := a; letI := i
        NatTrans.CommShift (integralDualComparison D l hl X E w A).hom ℤ) ∧
      (letI := i; letI := t
        NatTrans.CommShift (localizationDualComparison D l hl X E w A).hom ℤ) ∧
      (letI := t; A.dual.IsTriangulated) := by
  let I := (sfIntegralConstructible l E X).ι
  let U := IntegralVerdier.restrictedDual l E X w.omega.obj A.preserves
  let V := IntegralVerdier.dual l E X w.omega.obj
  obtain ⟨a, ha, hnorm, _⟩ :=
    CategoryTheory.signedDerivedInternalHom_exact.{u + 1, u, u, u + 2}
      (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X) w.omega.obj
  letI : V.CommShift ℤ := a
  haveI : V.IsTriangulated := ha
  let ei := integralDualComparison D l hl X E w A
  let i : U.CommShift ℤ := Functor.CommShift.ofComp ei ℤ
  letI := i
  have hi : NatTrans.CommShift ei.hom ℤ := Functor.CommShift.ofComp_compatibility ei ℤ
  haveI : U.IsTriangulated := by
    constructor
    intro T hT
    apply (I.map_distinguished_iff _).mp
    have hTV := V.map_distinguished (I.op.mapTriangle.obj T) (I.op.map_distinguished T hT)
    have ht : (I.op ⋙ V).mapTriangle.obj T ∈ distTriang _ :=
      isomorphic_distinguished _ hTV _ ((Functor.mapTriangleCompIso I.op V).app T)
    have ht' := isomorphic_distinguished _ ht _ ((Functor.mapTriangleIso ei).app T)
    exact isomorphic_distinguished _ ht' _ ((Functor.mapTriangleCompIso U I).symm.app T)
  let Q := sfRationalConstructibleLocalization l E X
  let W := Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E X)
  haveI : Q.IsLocalization W := ScalarLocalization.semilinear_localization_isLocalization
    (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E X)
    (Padic.coefficientExtensionUniformizer l E)
  let e := localizationDualComparison D l hl X E w A
  letI : Localization.Lifting Q.op W.op (U ⋙ Q) A.dual := ⟨e⟩
  let t : A.dual.CommShift ℤ := Functor.commShiftOfLocalization Q.op W.op ℤ (U ⋙ Q) A.dual
  letI := t
  have he : NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q.op W.op ℤ (U ⋙ Q) A.dual
  haveI : Q.op.mapArrow.EssSurj := Localization.essSurj_mapArrow Q.op W.op
  have ht : A.dual.IsTriangulated := Functor.isTriangulated_of_precomp_iso e
  exact ⟨a, i, t, ha, hnorm, hi, he, ht⟩

/-- The rational shift obtained from the proved signed ambient construction. -/
@[irreducible] def signedShift : A.dual.CommShift ℤ :=
  (signedShift_exists D l hl X E w A).choose_spec.choose_spec.choose

/-- The constructed rational shift makes the given duality exact. -/
theorem signedShift_exact : letI := signedShift D l hl X E w A
    A.dual.IsTriangulated := by
  unfold signedShift
  exact (signedShift_exists D l hl X E w A).choose_spec.choose_spec.choose_spec.2.2.2.2

end WeilConjectures.RationalVerdier
