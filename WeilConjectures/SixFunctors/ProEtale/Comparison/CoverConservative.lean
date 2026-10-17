/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Detecting isomorphisms on the pro-étale site: covering families and the affine basis

This file proves the first two clauses of blueprint `lem-cbc-proetale-stalk-conservative`, for a
Grothendieck abelian coefficient category `A`.

1. *Locality for covering families.* For a pro-étale covering family `g i : W i ⟶ X`, a morphism
   of pro-étale sheaves on `X` is an isomorphism if and only if all its pullbacks `(g i)^*` are;
   a sheaf vanishes if and only if all its pullbacks vanish. The same holds for morphisms of
   complexes (quasi-isomorphisms) and in the derived category, the pullbacks being exact and an
   isomorphism of the derived category being detected on the cohomology sheaves.
2. *Detection on the affine basis.* A pro-étale sheaf vanishes, and a morphism of pro-étale
   sheaves is an isomorphism, if and only if this holds on the sections over every object of
   the affine pro-étale site `X.AffineProEt`; a morphism of complexes is a quasi-isomorphism if
   and only if its restriction to the affine pro-étale site is one.

The general categorical input is that a jointly conservative family of exact functors between
abelian categories induces a jointly conservative family of functors between the derived
categories (`CategoryTheory.DerivedCategory.isIso_iff_forall_isIso_mapDerivedCategory_map`) and
between the categories of complexes up to quasi-isomorphism
(`HomologicalComplex.quasiIso_iff_forall_quasiIso_mapHomologicalComplex_map`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite ZeroObject

open scoped CategoryTheory.Functor

section General

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {D : ι → Type*}
  [∀ i, Category* (D i)] [∀ i, Abelian (D i)]

/-- Let `F i : C ⥤ D i` be a family of functors between abelian categories preserving homology
which jointly reflects isomorphisms. Then a morphism of short complexes in `C` is a
quasi-isomorphism if and only if its images under all the `F i` are. -/
lemma CategoryTheory.ShortComplex.quasiIso_iff_forall_quasiIso_map
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).PreservesZeroMorphisms] [∀ i, (F i).PreservesHomology]
    (hF : ∀ {X Y : C} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f)
    {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    QuasiIso φ ↔ ∀ i, QuasiIso ((F i).mapShortComplex.map φ) := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  simp only [γ.quasiIso_iff, fun i ↦ (γ.map (F i)).quasiIso_iff, LeftHomologyMapData.map_φH]
  exact ⟨fun _ _ ↦ inferInstance, fun h ↦ hF _ h⟩

/-- Let `F i : C ⥤ D i` be a family of additive functors between abelian categories preserving
homology which jointly reflects isomorphisms. Then a morphism of homological complexes in `C` is
a quasi-isomorphism if and only if its images under all the `F i` are. -/
lemma HomologicalComplex.quasiIso_iff_forall_quasiIso_mapHomologicalComplex_map
    {κ : Type*} {c : ComplexShape κ}
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] [∀ i, (F i).PreservesHomology]
    (hF : ∀ {X Y : C} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f)
    {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    QuasiIso φ ↔ ∀ i, QuasiIso (((F i).mapHomologicalComplex c).map φ) := by
  simp only [quasiIso_iff, quasiIsoAt_iff]
  refine ⟨fun h i n ↦ ?_, fun h n ↦ ?_⟩
  · exact (ShortComplex.quasiIso_iff_forall_quasiIso_map F hF
      ((shortComplexFunctor C c n).map φ)).1 (h n) i
  · exact (ShortComplex.quasiIso_iff_forall_quasiIso_map F hF
      ((shortComplexFunctor C c n).map φ)).2 fun i ↦ h i n

variable [HasDerivedCategory C] [∀ i, HasDerivedCategory (D i)]

/-- Let `F i : C ⥤ D i` be a family of exact functors between abelian categories which jointly
reflects isomorphisms. Then the induced functors `D(F i)` between the derived categories jointly
reflect isomorphisms: an isomorphism of the derived category is detected on the cohomology
objects, with which the `D(F i)` commute. -/
lemma CategoryTheory.DerivedCategory.isIso_iff_forall_isIso_mapDerivedCategory_map
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)]
    (hF : ∀ {X Y : C} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f)
    {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ i, IsIso ((F i).mapDerivedCategory.map f) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  refine hF _ fun i ↦ ?_
  have := (NatIso.isIso_map_iff ((F i).mapDerivedCategoryHomologyFunctorIso n) f).2
    (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor (D i) n).map
      ((F i).mapDerivedCategory.map f))))
  exact this

/-- Let `F i : C ⥤ D i` be a family of exact functors between abelian categories which jointly
reflects isomorphisms. Then an object of the derived category of `C` vanishes if and only if its
images under all the `D(F i)` vanish. -/
lemma CategoryTheory.DerivedCategory.isZero_iff_forall_isZero_mapDerivedCategory_obj
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)]
    (hF : ∀ {X Y : C} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f)
    (K : DerivedCategory C) :
    IsZero K ↔ ∀ i, IsZero ((F i).mapDerivedCategory.obj K) := by
  refine ⟨fun hK i ↦ (F i).mapDerivedCategory.map_isZero hK, fun h ↦ ?_⟩
  have : IsIso (0 : K ⟶ 0) :=
    (isIso_iff_forall_isIso_mapDerivedCategory_map F hF _).2 fun i ↦
      isIso_of_source_target_iso_zero _ (h i).isoZero
        ((F i).mapDerivedCategory.map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

end General

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Cover

variable {X : Scheme.{u}} {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, WeaklyEtale (g i)]

/-- The pullbacks along the members of a pro-étale covering family jointly reflect
isomorphisms of pro-étale sheaves. -/
lemma isIso_of_forall_isIso_upperStar_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {G G' : Sheaf (Scheme.ProEt.topology X) A} (φ : G ⟶ G')
    (h : ∀ i, IsIso ((g i)^*[A].map φ)) : IsIso φ :=
  isIso_of_isIso_localizationRestriction A φ g hg fun i ↦
    (NatIso.isIso_map_iff (upperStarIsoLocalizationRestriction A (g i) inferInstance) φ).1
      (h i)

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (1): *locality for covering families*,
for sheaves. A morphism of pro-étale sheaves on `X` is an isomorphism if and only if its inverse
images along all the members of a pro-étale covering family `g i : W i ⟶ X` are. -/
theorem isIso_iff_forall_isIso_upperStar_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {G G' : Sheaf (Scheme.ProEt.topology X) A} (φ : G ⟶ G') :
    IsIso φ ↔ ∀ i, IsIso ((g i)^*[A].map φ) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_forall_isIso_upperStar_map A g hg φ⟩

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (1): *locality for covering families*,
vanishing of sheaves. A pro-étale sheaf on `X` vanishes if and only if its inverse images along
all the members of a pro-étale covering family `g i : W i ⟶ X` vanish. -/
theorem isZero_iff_forall_isZero_upperStar_obj
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (G : Sheaf (Scheme.ProEt.topology X) A) :
    IsZero G ↔ ∀ i, IsZero ((g i)^*[A].obj G) := by
  refine ⟨fun hG i ↦ (g i)^*[A].map_isZero hG, fun h ↦ ?_⟩
  have : IsIso (0 : G ⟶ 0) := isIso_of_forall_isIso_upperStar_map A g hg _ fun i ↦
    isIso_of_source_target_iso_zero _ (h i).isoZero
      ((g i)^*[A].map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (1): *locality for covering families*,
for complexes. A morphism of complexes of pro-étale sheaves on `X` is a quasi-isomorphism if and
only if its inverse images along all the members of a pro-étale covering family
`g i : W i ⟶ X` are: the inverse images are exact and jointly reflect isomorphisms. -/
theorem quasiIso_iff_forall_quasiIso_upperStar_mapHomologicalComplex_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {κ : Type*} {c : ComplexShape κ}
    {K L : HomologicalComplex (Sheaf (Scheme.ProEt.topology X) A) c} (φ : K ⟶ L) :
    QuasiIso φ ↔ ∀ i, QuasiIso (((g i)^*[A].mapHomologicalComplex c).map φ) :=
  HomologicalComplex.quasiIso_iff_forall_quasiIso_mapHomologicalComplex_map
    (fun i ↦ (g i)^*[A]) (fun φ ↦ isIso_of_forall_isIso_upperStar_map A g hg φ) φ

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (1): *locality for covering families*,
in the derived category. A morphism of `D(X_proét)` is an isomorphism if and only if its inverse
images along all the members of a pro-étale covering family `g i : W i ⟶ X` are. -/
theorem isIso_iff_forall_isIso_mapDerivedCategory_upperStar_map
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (f : K ⟶ L) :
    IsIso f ↔ ∀ i, IsIso (D((g i)^*[A]).map f) :=
  DerivedCategory.isIso_iff_forall_isIso_mapDerivedCategory_map (fun i ↦ (g i)^*[A])
    (fun φ ↦ isIso_of_forall_isIso_upperStar_map A g hg φ) f

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (1): *locality for covering families*,
vanishing in the derived category. An object of `D(X_proét)` vanishes if and only if its inverse
images along all the members of a pro-étale covering family `g i : W i ⟶ X` vanish. -/
theorem isZero_iff_forall_isZero_mapDerivedCategory_upperStar_obj
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    IsZero K ↔ ∀ i, IsZero (D((g i)^*[A]).obj K) :=
  DerivedCategory.isZero_iff_forall_isZero_mapDerivedCategory_obj (fun i ↦ (g i)^*[A])
    (fun φ ↦ isIso_of_forall_isIso_upperStar_map A g hg φ) K

end Cover

section Affine

variable {X : Scheme.{u}}

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (2): *detection on the affine basis*, for
morphisms of sheaves. A morphism of pro-étale sheaves on `X` is an isomorphism if and only if it
is one on the sections over every object of the affine pro-étale site of `X`. -/
theorem isIso_iff_forall_isIso_app_affineProEt {G G' : Sheaf (Scheme.ProEt.topology X) A}
    (φ : G ⟶ G') :
    IsIso φ ↔ ∀ W : X.AffineProEt, IsIso (φ.hom.app (op ((AffineProEt.toProEt X).obj W))) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_isIso_app_affineProEt A φ⟩

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (2): *detection on the affine basis*, for
vanishing of sheaves. A pro-étale sheaf on `X` vanishes if and only if its sections over every
object of the affine pro-étale site of `X` vanish. -/
theorem isZero_iff_forall_isZero_obj_affineProEt (G : Sheaf (Scheme.ProEt.topology X) A) :
    IsZero G ↔ ∀ W : X.AffineProEt, IsZero (G.obj.obj (op ((AffineProEt.toProEt X).obj W))) := by
  refine ⟨fun hG W ↦ ?_, fun h ↦ ?_⟩
  · exact ((sheafSections _ A).obj (op ((AffineProEt.toProEt X).obj W))).map_isZero hG
  · have : IsIso (0 : G ⟶ 0) := isIso_of_isIso_app_affineProEt A _ fun W ↦
      isIso_of_source_target_iso_zero _ (h W).isoZero
        (((sheafSections _ A).obj (op ((AffineProEt.toProEt X).obj W))).map_isZero
          (isZero_zero _)).isoZero
    exact (isZero_zero _).of_iso (asIso (0 : G ⟶ 0))

/-- Restriction of pro-étale sheaves to the affine pro-étale site, an equivalence of
categories since the affine pro-étale site is a dense subsite. -/
noncomputable abbrev restrictAffineProEt :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (AffineProEt.topology X) A :=
  (AffineProEt.toProEt X).sheafPushforwardContinuous A (AffineProEt.topology X)
    (Scheme.ProEt.topology X)

instance : (restrictAffineProEt (X := X) A).Additive where

instance : (restrictAffineProEt (X := X) A).IsEquivalence := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  infer_instance

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (2): *detection on the affine basis*, for
complexes. A morphism of complexes of pro-étale sheaves on `X` is a quasi-isomorphism if and only
if its restriction to the affine pro-étale site of `X` is one: restriction to the affine
pro-étale site is an equivalence of categories, hence exact and conservative. -/
theorem quasiIso_iff_quasiIso_restrictAffineProEt_mapHomologicalComplex_map {κ : Type*}
    {c : ComplexShape κ} {K L : HomologicalComplex (Sheaf (Scheme.ProEt.topology X) A) c}
    (φ : K ⟶ L) :
    QuasiIso φ ↔ QuasiIso (((restrictAffineProEt (X := X) A).mapHomologicalComplex c).map φ) :=
  (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ _).symm

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (2): *detection on the affine bases of an
open cover*. For an open cover `𝒰` of `X`, a morphism of pro-étale sheaves on `X` is an
isomorphism if and only if, for every member `𝒰.f i`, its inverse image along `𝒰.f i` is an
isomorphism on the sections over every object of the affine pro-étale site of `𝒰.X i`. -/
theorem isIso_iff_forall_isIso_upperStar_map_app_affineProEt (𝒰 : X.OpenCover)
    {G G' : Sheaf (Scheme.ProEt.topology X) A} (φ : G ⟶ G') :
    IsIso φ ↔ ∀ (i : 𝒰.I₀) (W : (𝒰.X i).AffineProEt),
      IsIso (((𝒰.f i)^*[A].map φ).hom.app (op ((AffineProEt.toProEt _).obj W))) := by
  rw [isIso_iff_forall_isIso_upperStar_map A 𝒰.f
    (zariskiPrecoverage_le_proetalePrecoverage _ 𝒰.mem₀)]
  exact forall_congr' fun i ↦ isIso_iff_forall_isIso_app_affineProEt A _

end Affine

end AlgebraicGeometry.ProEtale
