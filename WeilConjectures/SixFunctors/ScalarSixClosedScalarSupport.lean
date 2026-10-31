/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.AlgebraicGeometry.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

/-! # Closed support under scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

private theorem closedExtensionIso
    (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left]
    [PreservesFiniteColimits (lowerStar Λ.X i.left)] :
    Nonempty (scalarSixExtension E G Λ i ≅ (lowerStar Λ.X i.left).mapDerivedCategory) := by
  let b := scalarSixImmersion G Λ i
  let eS := scalarSixEquivalence Λ S.left
  let eX := scalarSixEquivalence Λ X.left
  letI := E.additive b
  letI := E.finiteLimits b
  letI := E.finiteColimits b
  let d : lowerStar Λ.X i.left ⋙
        (ModuleRingedComparison.equivalence Λ.X X.left).functor ≅
      (ModuleRingedComparison.equivalence Λ.X S.left).functor ⋙ E.extension b :=
    G.push Λ i.left ≪≫ Functor.isoWhiskerLeft
      (ModuleRingedComparison.equivalence Λ.X S.left).functor
      (E.closedComparison b (inferInstanceAs (IsClosedImmersion i.left))).symm
  let dd : (lowerStar Λ.X i.left).mapDerivedCategory ⋙ eX.functor ≅
      eS.functor ⋙ E.derived b :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso d ≪≫ Functor.mapDerivedCategoryCompIso _ _
  exact ⟨(dd.isoCompInverse (H := eX) ≪≫ Functor.associator _ _ _).symm⟩

/-- Scalar extension preserves closed support, without specifying a comparison map.

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md (2), closed case;
Stacks Tags 09AA, 09BM and 09AH.
(blueprint: lem-sfb-scalar-six-closed-scalar-support).

Proof: transport the exact closed direct image through the fixed module equivalences.
The closed counit identifies its closed restriction with its source, and its
complementary-open restriction is zero. Exact inverse image commutes with derived
scalar extension by the canonical scalar-adjunction mate. Thus scalar extension of
the closed direct image still has zero complementary-open restriction: scalar
extension is a left adjoint and preserves the zero object. The exact unbounded
open/closed localization theorem makes the closed unit invertible on this object.
It is consequently in the essential image of the exact closed direct image.
Transport back along E.closedComparison and the fixed derived equivalences to obtain
membership in the essential image of scalarSixExtension. No chosen comparison,
restriction normalization, naturality, or open-unit transport is asserted. -/
theorem scalarSixClosedScalar_mem_essImage
    (E : LocallyClosedExtensionData.{u}) (G : ScalarSixGeometry.{u})
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {k : Type u} [Field k] {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : S ⟶ X) [IsClosedImmersion i.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)) :
    (scalarSixExtension E G Λ' i).essImage
      ((scalarSixChange a X.left).obj ((scalarSixExtension E G Λ i).obj M)) := by
  letI : IsCommMonObj Λ.X := Λ.comm
  letI : IsCommMonObj Λ'.X := Λ'.comm
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  let V : X.left.Opens :=
    ⟨(Set.range i.left)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := V.ι
  have hij : Set.range i.left.base = (Set.range j.base)ᶜ := by
    simp [j, V]
  letI := closedSupport_lowerStarExact Λ.X i.left j hij
  letI := closedSupport_lowerStarExact Λ'.X i.left j hij
  obtain ⟨e⟩ := closedExtensionIso E G Λ i
  obtain ⟨e'⟩ := closedExtensionIso E G Λ' i
  obtain ⟨C⟩ := scalarSixPullbackData_exists.{u}
  let r := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X j)
  let r' := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ'.X j)
  let N := (scalarSixExtension E G Λ i).obj M
  let K := (scalarSixChange a X.left).obj N
  have hz : IsZero ((scalarSixPull Λ j).obj N) := by
    have h := (condensedSupportDerivedLocalization Λ.X i.left j hij).2.2.2.2.1 M
    exact h.of_iso ((r.app N).symm ≪≫
      (supportPullback Λ.X j).mapDerivedCategory.mapIso (e.app M))
  have hz' : IsZero ((supportPullback Λ'.X j).mapDerivedCategory.obj K) := by
    letI : (scalarSixChange a V).IsLeftAdjoint :=
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom V)).isLeftAdjoint
    have h := (scalarSixChange a V).map_isZero hz
    exact h.of_iso (r'.app K ≪≫ ((C.theta a j).app N).symm)
  have hu := (condensedSupportDerivedLocalization Λ'.X i.left j hij).2.2.1 K hz'
  letI := hu
  exact ⟨_, ⟨e'.app _ ≪≫
    (asIso ((closedPullbackDerivedAdjunction Λ'.X i.left).unit.app K)).symm⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
