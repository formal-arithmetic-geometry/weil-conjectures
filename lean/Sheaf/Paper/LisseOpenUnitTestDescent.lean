/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.ScalarTestsRegularOpenUnit
import Sheaf.Paper.OpenUnitCoverDescent
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.MorphismProperty.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-!
# Scalar contractible tests detect the lisse open unit

Source: blueprint main-20261015, six-functor stability, direct-images proof, paragraph (3),
agent-formulated scalar-to-lisse descent sublemma; Stacks 08FI, 0D6F, 0D6J.
(blueprint: lem-sfb-lisse-open-unit-test-descent).

The scalar arrow is the right-derived natural transformation of actual restriction on
sections on the full small pro-etale site. The conclusion uses the specified derived
internal-module adjunction, with its K-injective direct image and K-flat inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The open base change of a test object, still regarded as an object of the full site.
Source: scalar tests in the agent sublemma for blueprint direct-images paragraph (3)
(blueprint: lem-sfb-lisse-open-unit-test-descent). -/
def openUnitTest {X : Scheme.{u}} (U : X.Opens) (V : X.ProEt) : X.ProEt :=
  Scheme.ProEt.mk (pullback.snd U.ι V.hom ≫ V.hom)

/-- The actual projection from the open base change to the original test object.
Source: scalar restriction in the agent sublemma for blueprint direct-images paragraph (3)
(blueprint: lem-sfb-lisse-open-unit-test-descent). -/
def openUnitTestProjection {X : Scheme.{u}} (U : X.Opens) (V : X.ProEt) :
    openUnitTest U V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.snd U.ι V.hom) rfl

/-- The actual scalar restriction in the ordinary unbounded derived category of abelian
 groups. Derive the natural transformation of evaluation functors on the full site, then
 evaluate at the degree-zero underlying coefficient sheaf. Restricting a K-injective
 resolution to a slice remains K-injective, so these endpoints are canonically
 `RΓ(V, Λ_V[0])` and `RΓ(U ×_X V, Λ_(U ×_X V)[0])`, with the actual restriction map.
Source: agent scalar-to-lisse sublemma, blueprint direct-images paragraph (3); Stacks 08FI
(blueprint: lem-sfb-lisse-open-unit-test-descent). -/
def scalarOpenUnitTestRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {X : Scheme.{u}} (U : X.Opens) (V : X.ProEt) :=
  (Functor.rightDerivedFunctorNatTrans
    ((sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (openUnitTestProjection U V).op)).app
        ((DerivedCategory.singleFunctor _ 0).obj (condensedRingObj Λ X))

private theorem isIso_app_finite_biproduct
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] (F G : C ⥤ D) [F.Additive] [G.Additive]
    (α : F ⟶ G) (R : C) (hR : IsIso (α.app R)) (n : ℕ) :
    IsIso (α.app (⨁ fun _ : Fin n ↦ R)) := by
  let K := Discrete.functor (fun _ : Fin n ↦ R)
  have : ∀ i, IsIso ((Functor.whiskerLeft K α).app i) := fun _ ↦ hR
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α _ (biproduct.isColimit _)

private theorem isIso_open_unit_of_isFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z Y : Scheme.{u}} (j : Z ⟶ Y)
    (hR : IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ j).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ Y)))))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : Mod.IsFree (condensedRingObj Λ Y) M) :
    IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ j).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  have : (CondensedRing.upperStar Λ j).leftDerivedFunctor.Additive :=
    Functor.additive_of_iso
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm
  let α := Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ j).unit
  obtain ⟨n, ⟨e⟩⟩ := hM
  apply (NatTrans.isIso_app_iff_of_iso α e).2
  exact isIso_app_finite_biproduct _ _ α (Mod.regular (condensedRingObj Λ Y)) hR n

/-- Scalar contractible tests detect the actual open unit for every lisse internal module.
Source: blueprint direct-images paragraph (3), agent-formulated scalar-to-lisse sublemma;
Stacks 08FI, 0D6F, 0D6J (blueprint: lem-sfb-lisse-open-unit-test-descent).

Proof: Unpack the lisse trivialization. On each covering chart apply the scalar-test
criterion for the regular module to its composite map to X. Whisker the actual adjunction
unit by the degree-zero single functor. Its endpoint functors are additive and preserve
finite biproducts, so the rank-one result implies the finite-free result, including rank
zero. Naturality transports it along the chart's trivialization. The open-unit covering
descent criterion then detects invertibility of the original specified unit. -/
theorem isIso_lisse_open_unit_of_scalar_contractible_tests
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsAffine X] (f : Γ(X, ⊤))
    (hscalar : ∀ (V : X.ProEt), IsAffine V.left →
      (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} V →
      IsIso (scalarOpenUnitTestRestriction Λ (X.basicOpen f) V))
    (X' : Scheme.{u}) [IsAffine X'] (a : X' ⟶ X) [WeaklyEtale a]
    (N : Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1}) (condensedRingObj Λ X'))
    (hN : IsLisseCoefficientModule Λ N) :
    IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
      (pullback.snd (X.basicOpen f).ι a)).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj N)) := by
  obtain ⟨𝒰, h𝒰⟩ := hN
  apply isIso_open_unit_of_cover Λ X (X.basicOpen f) X' a N 𝒰
  intro i
  have : WeaklyEtale (𝒰.f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X' 𝒰.mem₀) ⟨i⟩
  apply isIso_open_unit_of_isFree Λ _ _ _ (h𝒰 i)
  exact isIso_regular_open_unit_of_scalar_tests Λ X (X.basicOpen f) hscalar
    (𝒰.X i) (𝒰.f i ≫ a)

end AlgebraicGeometry.ProEtale
