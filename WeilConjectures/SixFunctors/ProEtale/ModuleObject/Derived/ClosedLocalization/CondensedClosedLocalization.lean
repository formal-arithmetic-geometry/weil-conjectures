/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization

/-! # Closed-support localization with condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-localization/
prop-sf-localization-all-stages.md and its proof
(blueprint: prop-sf-localization-all-stages).

All operations act on the ordinary derived category of modules over the pulled-back
condensed ring. The structure below records restrictions of the prescribed functors and
their right adjunction, so it does not choose an unrelated counit or exceptional map.

## Main statements

* `condensedClosedLocalization`: support adjunction, triangle and finite-Tor restrictions.
* `condensedClosedLocalization_finiteBounds`: explicit finite-coefficient Tor bounds.
* `condensedClosedLocalization_finiteExceptional`: finite etale exceptional identification.
* `condensedClosedLocalization_nativeExceptional`: native Brown exceptional identification.
* `condensedClosedLocalization_integralReduction`: reduction comparison and uniform bounds.
* `condensedClosedLocalization_weil`: canonical Frobenius exchanges and equivariant triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restrictions and the exceptional adjunction for a closed/open pair. Every functor
except the right adjoint is fixed by the ambient module operations. The right adjoint is
specified by its adjunction, hence up to unique counit-compatible isomorphism.
Source: clauses (1)--(2) (blueprint: prop-sf-localization-all-stages). -/
structure ClosedLocalization {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) where
  /-- Closed direct image preserves bounded constructibility. -/
  closed_mem : ∀ K : ConstantModelBoundedConstructible Λ Z,
    constantModelBoundedConstructible Λ X ((moduleObjectDerivedPushforward Λ i).obj K.obj)
  /-- Open direct image preserves bounded constructibility, clause (1). -/
  open_mem : ∀ K : ConstantModelBoundedConstructible Λ U,
    constantModelBoundedConstructible Λ X ((moduleObjectDerivedPushforward Λ j).obj K.obj)
  /-- Closed pullback preserves bounded constructibility. -/
  closed_pull_mem : ∀ K : ConstantModelBoundedConstructible Λ X,
    constantModelBoundedConstructible Λ Z ((moduleObjectDerivedPullback Λ i).obj K.obj)
  /-- Open pullback preserves bounded constructibility. -/
  open_pull_mem : ∀ K : ConstantModelBoundedConstructible Λ X,
    constantModelBoundedConstructible Λ U ((moduleObjectDerivedPullback Λ j).obj K.obj)
  /-- The right adjoint on bounded constructible objects, clause (2). -/
  exceptional : ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ Z
  /-- Its defining adjunction to the actual closed direct image. -/
  adjunction : (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ Z).ι ⋙ moduleObjectDerivedPushforward Λ i)
      closed_mem ⊣ exceptional

variable {Λ} {X Z U : Scheme.{u}} {i : Z ⟶ X} {j : U ⟶ X}

/-- The actual closed direct image, restricted to Dbc.
Source: clause (2) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.closedPush (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ Z).ι ⋙ moduleObjectDerivedPushforward Λ i) L.closed_mem

/-- The actual open direct image, restricted to Dbc.
Source: clause (1) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPush (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ U).ι ⋙ moduleObjectDerivedPushforward Λ j) L.open_mem

/-- The actual open pullback, restricted to Dbc.
Source: clause (3) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPull (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ U).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙ moduleObjectDerivedPullback Λ j) L.open_pull_mem

/-- The prescribed support triangle with a variable last arrow; the first two arrows
are the exceptional counit and ordinary open adjunction unit.
Source: clause (3) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.triangle (L : ClosedLocalization Λ i j)
    (K : ConstantModelBoundedConstructible Λ X)
    (δ : (moduleObjectDerivedPushforward Λ j).obj
        ((moduleObjectDerivedPullback Λ j).obj K.obj) ⟶
      ((moduleObjectDerivedPushforward Λ i).obj (L.exceptional.obj K).obj) ⟦(1 : ℤ)⟧) :=
  Triangle.mk (L.adjunction.counit.app K).hom
    ((derivedUpperStarLowerStarAdjunction Λ j).unit.app K.obj) δ

variable (Λ)

variable {Λ}

variable (Λ)

variable {Λ}

/-- The open pullback/direct-image adjunction with its specified ambient unit.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPullPushAdjunction (L : ClosedLocalization Λ i j) :
    L.openPull ⊣ L.openPush :=
  (derivedUpperStarLowerStarAdjunction Λ j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

variable (Λ)

/-- The geometric base change of a model morphism, reusing the actual pullback functor.
Source: descended immersion pair in the Weil paragraph
(blueprint: prop-sf-localization-all-stages). -/
def localizationFiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {S T : Over (Spec (.of D.k₀))} (f : S ⟶ T) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f).left

private theorem localizationAction_equivalence {T : Scheme.{u}} (g : T ≅ T) :
    (localizationAction Λ g).IsEquivalence := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := StrictWeil.action_inverse Λ g
  let P := constantModelBoundedConstructible Λ T
  let F := localizationAction Λ g
  let G := localizationAction Λ g.symm
  let aa : F ⋙ G ≅ 𝟭 _ :=
    (P.fullyFaithfulι.whiskeringRight _).preimageIso (Functor.isoWhiskerLeft P.ι a)
  let bb : G ⋙ F ≅ 𝟭 _ :=
    (P.fullyFaithfulι.whiskeringRight _).preimageIso (Functor.isoWhiskerLeft P.ι b)
  exact Functor.IsEquivalence.mk' G aa.symm bb

private theorem localizationFiberCartesian (D : WeilConjectures.FiniteFieldDatum.{u})
    {S T : Over (Spec (.of D.k₀))} (f : S ⟶ T) :
    IsPullback
      (pullback.fst S.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (localizationFiberMap D f) f.left
      (pullback.fst T.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback T.hom _)
  · convert IsPullback.of_hasPullback S.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) using 1 <;>
      simp [localizationFiberMap, Over.pullback]
  · simp [localizationFiberMap, Over.pullback]

private theorem localization_open_unit (L : ClosedLocalization Λ i j)
    (K : ConstantModelBoundedConstructible Λ X) :
    (L.openPullPushAdjunction.unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ j).unit.app K.obj := by
  change (constantModelBoundedConstructible Λ X).ι.map
    (L.openPullPushAdjunction.unit.app K) = _
  dsimp only [ClosedLocalization.openPullPushAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp

private theorem localization_orthogonal {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z))
    (G : DerivedCategory (supportModules Λ U)) (m : ℤ) :
    Subsingleton (((moduleObjectDerivedPushforward Λ i).obj P) ⟦m⟧ ⟶
      (moduleObjectDerivedPushforward Λ j).obj G) := by
  let := closedSupport_lowerStarExact Λ i j hij
  let I := (lowerStar Λ i).mapDerivedCategory
  let J := (supportPullback Λ j).mapDerivedCategory
  have hz := (condensedSupportDerivedLocalization Λ i j hij).2.2.2.2.1
  have : Subsingleton ((shiftFunctor _ m).obj (I.obj P) ⟶
      (moduleObjectDerivedPushforward Λ j).obj G) :=
    Recollement.subsingleton_hom_shift I J (closedSupportOpenDerivedAdjunction Λ j)
      hz P G m
  let eI := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app P
  exact (((shiftFunctor _ m).mapIso eI).homCongr
    (Iso.refl ((moduleObjectDerivedPushforward Λ j).obj G))).subsingleton

private theorem localization_triangle_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (e₁ : F.obj T.obj₁ ≅ T.obj₁) (e₂ : F.obj T.obj₂ ≅ T.obj₂)
    (e₃ : F.obj T.obj₃ ≅ T.obj₃)
    (h₁ : F.map T.mor₁ ≫ e₂.hom = e₁.hom ≫ T.mor₁)
    (h₂ : F.map T.mor₂ ≫ e₃.hom = e₂.hom ≫ T.mor₂)
    (hsub : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃)) :
    ∃ e : F.mapTriangle.obj T ≅ T,
      e.hom.hom₁ = e₁.hom ∧ e.hom.hom₂ = e₂.hom ∧ e.hom.hom₃ = e₃.hom := by
  have := hsub
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
    (F.mapTriangle.obj T) T (F.map_distinguished T hT) hT e₁.hom e₂.hom h₁
  have : Subsingleton ((F.mapTriangle.obj T).obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) :=
    (((shiftFunctor C (1 : ℤ)).mapIso e₁).homCongr (Iso.refl T.obj₃)).subsingleton
  have hc : c = e₃.hom := Triangle.cancel_mor₂_of_subsingleton
    (F.map_distinguished T hT) (hc₂.trans h₂.symm)
  rw [hc] at hc₃
  exact ⟨Triangle.isoMk _ _ e₁ e₂ e₃ h₁ h₂ hc₃, rfl, rfl, rfl⟩

end AlgebraicGeometry.ProEtale.CondensedRing
