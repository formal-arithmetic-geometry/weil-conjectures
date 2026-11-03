/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationAdjunction
import WeilConjectures.CategoryTheory.ScalarLocalization.TensorLocalizationComparison
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # The square identifying localized proper direct image

Source: current blueprint `lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`,
final sentence, together with the prescribed proper coefficient mate.
(blueprint: lem-sfb-proper-scalar-localization-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] HasDerivedCategory.standard upperStarFromPoint
  Mod.extendScalars

/-- Proper integral pushforward is additive.
Source: additivity of ordinary derived pushforward
(blueprint: lem-sfb-proper-scalar-localization-square).
Proof: restrict the additive ordinary derived pushforward to the full subcategories. -/
theorem properIntegralPushforward_additive
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ell E.1 p).Additive := by
  dsimp only [PadicIntegersRingObj.boundedConstructibleLowerStar]
  infer_instance

set_option maxHeartbeats 2000000 in
-- Comparing the actual coefficient and full-subcategory functors needs this budget.
/-- The proper rational pushforward is the scalar localization of the integral one.

The scalar ring ℤ[1/ell] is sufficient here: for an O_E-module H,
ℤ[1/ell] tensor_ℤ H = E tensor_{O_E} H, by the module localization universal
property and E = O_E[1/ell]. This keeps the canonical integer action on the
actual categories and avoids choosing any new coefficient action.

Source: Bhatt--Scholze, Proposition 6.8.14(2), and the current blueprint
`lem-sfb-dc-proper-pushforward-left-adjoint-e.proof.md`, final sentence;
`lem-sfb-qcqs-proper-integral-rational-scalar-comparison` for the actual proper mate.
(blueprint: lem-sfb-proper-scalar-localization-square)

Proof: finite-type schemes over k are topologically Noetherian. Derived scalar
extension O_E to E on bounded constructible complexes is localization of Hom
modules at the powers of ell and has integral models. Its natural tensor-Hom
bijections construct equivalences from the raw scalar-localized categories to
the actual E-coefficient constructible categories. They send 1 tensor f to the
actual scalar extension of f. Equivalently compare both localization functors
with the localization at ell-power-torsion cones, retaining the natural
comparison with actual scalar extension. Every bounded constructible integral
complex is bounded below. The published
qcqs localization comparison therefore applies to every source object. Its canonical
mate is invertible and gives
the square on integral objects and arrows. Extend the square to fractions:
each component commutes with the integer action, and ell is invertible after
extension; hence naturality for integral arrows extends to arbitrary localized
arrows. The localization universal property gives the displayed natural iso.
Only categories and the left-functor square are asserted, not existence of any
exceptional adjoint. For identity maps the square is the identity square; for
empty sources the categories and their comparisons are zero. -/
theorem properScalarLocalizationSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    let F := PadicIntegersRingObj.boundedConstructibleLowerStar ell E.1 p
    let : F.Additive := properIntegralPushforward_additive ell k E p
    ∃ eZ : ScalarLocalization ℤ
        (Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ell E.1⟧) (ell : ℤ) ≌
          Dᵇc(Z.left)⟦Profinite.continuousMapRingObj E.1⟧,
    ∃ eY : ScalarLocalization ℤ
        (Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ell E.1⟧) (ell : ℤ) ≌
          Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E.1⟧,
      Nonempty (ScalarLocalization.mapFunctor ℤ (ell : ℤ) F ⋙ eY.functor ≅
        eZ.functor ⋙ ContinuousMapRingObj.boundedConstructibleLowerStar ell E p) := by
  classical
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : IsNoetherian Z.left := ⟨⟩
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : IsNoetherian Y.left := ⟨⟩
  let CZ := Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ell E.1⟧
  let CY := Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ell E.1⟧
  let F := PadicIntegersRingObj.boundedConstructibleLowerStar ell E.1 p
  let : F.Additive := properIntegralPushforward_additive ell k E p
  let Fq := ContinuousMapRingObj.boundedConstructibleLowerStar ell E p
  let QZ := ScalarLocalization.localization ℤ CZ (ell : ℤ)
  let QY := ScalarLocalization.localization ℤ CY (ell : ℤ)
  let WZ := Rationalization.W (Submonoid.powers (ell : ℤ)) CZ
  let WY := Rationalization.W (Submonoid.powers (ell : ℤ)) CY
  have : QZ.IsLocalization WZ :=
    ScalarLocalization.tensor_localization_isLocalization ℤ CZ (ell : ℤ)
  have : QY.IsLocalization WY :=
    ScalarLocalization.tensor_localization_isLocalization ℤ CY (ell : ℤ)
  let LZ := boundedConstructibleExtendScalars Z.left ell E
  let LY := boundedConstructibleExtendScalars Y.left ell E
  let eZ := CategoryTheory.Localization.uniq QZ LZ WZ
  let eY := CategoryTheory.Localization.uniq QY LY WY
  let cZ : QZ ⋙ eZ.functor ≅ LZ := CategoryTheory.Localization.compUniqFunctor QZ LZ WZ
  let cY : QY ⋙ eY.functor ≅ LY := CategoryTheory.Localization.compUniqFunctor QY LY WY
  let φ := padicIntegersRingObjToContinuousMapRingObj ell E
  let : ∀ T : Scheme.{u}, CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.Mod.extendScalars (coefficientMap φ T)) :=
    fun T ↦ (padicIntegers_invertEll T ell E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
  let β := derivedPushHom φ p.left
  let α : F ⋙ LY ⟶ LZ ⋙ Fq :=
    { app M := ObjectProperty.homMk (β.app M.obj)
      naturality {M N} f := by
        apply (boundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)).ι.map_injective
        exact β.naturality f.hom }
  have hα (M : CZ) : IsIso (α.app M) := by
    have hi := localizedDirectImageComparison_isIso ell E p.left M.obj M.property.1.1
    have : IsIso ((boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)).ι.map
          (α.app M)) := hi
    exact isIso_of_reflects_iso (α.app M) (boundedConstructible _).ι
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let t : F ⋙ LY ≅ LZ ⋙ Fq := asIso α
  let F' := ScalarLocalization.mapFunctor ℤ (ell : ℤ) F
  let f : QZ ⋙ F' ≅ F ⋙ QY :=
    eqToIso (ScalarLocalization.mapFunctor_localization ℤ (ell : ℤ) F)
  let h : QZ ⋙ (F' ⋙ eY.functor) ≅ QZ ⋙ (eZ.functor ⋙ Fq) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight f eY.functor ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F cY ≪≫ t ≪≫
      Functor.isoWhiskerRight cZ.symm Fq ≪≫ Functor.associator _ _ _
  exact ⟨eZ, eY, ⟨CategoryTheory.Localization.liftNatIso QZ WZ _ _ _ _ h⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
