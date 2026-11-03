/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePunctualKernel.CondensedCurvePunctualKernel
public import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
public import WeilConjectures.AlgebraicGeometry.FieldExtensionComponentLocalDimension
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover

/-! # The perverse heart on a smooth curve with condensed coefficients

Source: latest blueprint, sec-wft-perverse/
sk-lem-wft-curve-heart/_section.md and sk-lem-wft-curve-heart.proof.md.
(blueprint: sk-lem-wft-curve-heart)

The two classes are defined by ordinary module-sheaf cohomology. Finite closed support
is expressed by zero restriction off a finite set of closed points. The geometric
category is exactly the recorded finite-constant-model bounded constructible category.
Weil objects are fixed pairs for the ordinary derived module inverse image whose
carriers lie in the geometric heart. For rational coefficients Dctf equals Dbc.
All support tests and subobjects in the two classes are geometric.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverse

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual category of modules over the pulled-back condensed coefficient ring.
Source: current blueprint, ambient category in sk-lem-wft-curve-heart
(blueprint: sk-lem-wft-curve-heart). -/
abbrev Modules (C : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C)

/-- A constructible sheaf is punctual when it vanishes off a finite set of closed points.
This includes the zero sheaf and allows the empty finite set. Zero inverse image on the
complement is the support condition for a sheaf, with no choice of a geometric stalk.
Source: current blueprint sk-lem-wft-curve-heart, opening definition
(blueprint: sk-lem-wft-curve-heart). -/
def IsPunctual (C : Scheme.{u}) (F : Modules Λ C) : Prop :=
  IsConstantModelConstructible Λ C F ∧
    ∃ U : C.Opens, ((U : Set C)ᶜ).Finite ∧
      (∀ x ∈ (U : Set C)ᶜ, IsClosed ({x} : Set C)) ∧
      IsZero ((CondensedRing.upperStar Λ U.ι).obj F)

/-- Absence of a nonzero punctual subsheaf is tested on geometric module monomorphisms,
without imposing a Weil structure on the subobject.
Source: current blueprint sk-lem-wft-curve-heart, lower-class formula
(blueprint: sk-lem-wft-curve-heart). -/
def HasNoPunctualSubsheaf (C : Scheme.{u}) (F : Modules Λ C) : Prop :=
  ∀ (G : Modules Λ C) (i : G ⟶ F), Mono i → IsPunctual Λ C G → IsZero G

/-- The upper curve class at n: cohomology above n vanishes and H^n is punctual.
This is the shift by -n of the displayed class at zero.
Source: current blueprint sk-lem-wft-curve-heart, first displayed class
(blueprint: sk-lem-wft-curve-heart). -/
def upper (C : Scheme.{u}) (n : ℤ) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  fun K ↦ (∀ a : ℤ, n < a → IsZero ((DerivedCategory.homologyFunctor _ a).obj K)) ∧
    IsPunctual Λ C ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The lower curve class at n: cohomology below n-1 vanishes and H^(n-1) has no
nonzero punctual subsheaf. This is the shift by -n of the displayed class at zero.
Source: current blueprint sk-lem-wft-curve-heart, second displayed class
(blueprint: sk-lem-wft-curve-heart). -/
def lower (C : Scheme.{u}) (n : ℤ) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  fun K ↦ (∀ a : ℤ, a < n - 1 → IsZero ((DerivedCategory.homologyFunctor _ a).obj K)) ∧
    HasNoPunctualSubsheaf Λ C ((DerivedCategory.homologyFunctor _ (n - 1)).obj K)

/-- The perverse heart, retaining its ambient geometric derived morphisms.
Source: current blueprint sk-lem-wft-curve-heart, heart definition
(blueprint: sk-lem-wft-curve-heart). -/
def heart (C : Scheme.{u}) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  constantModelBoundedConstructible Λ C ⊓ (upper Λ C 0 ⊓ lower Λ C 0)

/-- Perverse cohomology H^n, once the t-structure with the specified classes is supplied.
It is H^0(K[n]) with values in the actual Mathlib heart, using the existing cohomology
functor of the recorded t-structure dependency.
Source: current blueprint sk-lem-wft-curve-heart, notation paragraph
(blueprint: sk-lem-wft-curve-heart). -/
abbrev cohomology (C : Scheme.{u})
    [(constantModelBoundedConstructible Λ C).IsTriangulated]
    (t : TStructure (ConstantModelBoundedConstructible Λ C)) (n : ℤ) :=
  shiftFunctor (ConstantModelBoundedConstructible Λ C) n ⋙ t.homology₀

/-- Perverse Weil sheaves are the full subcategory of the recorded strict Weil pairs
whose underlying geometric complex lies in the perverse heart.
Source: current blueprint sk-lem-wft-curve-heart, Weil definition paragraph
(blueprint: sk-lem-wft-curve-heart). -/
abbrev WeilHeart {C : Scheme.{u}} (g : C ≅ C) :=
  ObjectProperty.FullSubcategory
    (fun K : Endofunctor.IsoAlgebra (CondensedRing.upperStar Λ g.hom).mapDerivedCategory ↦
      heart Λ C K.carrier)

/-- The canonical forgetful functor retains the carrier and its geometric derived arrow.
The defining carrier property supplies exactly bounded constructibility and the
geometric perverse conditions. Source: current blueprint sk-lem-wft-curve-heart, final paragraph
(blueprint: sk-lem-wft-curve-heart). -/
def forget {C : Scheme.{u}} (g : C ≅ C) :
    WeilHeart Λ g ⥤ (heart Λ C).FullSubcategory where
  obj K := ⟨K.obj.carrier, K.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

/-- Abelianness and exactness of the canonical functor, including reflection of exactness
for arbitrary two composable arrows. The endpoint clauses spell out reflection of
short exact sequences as well. Abelian structures are asserted, not assumed.
Source: current blueprint sk-lem-wft-curve-heart, final paragraph
(blueprint: sk-lem-wft-curve-heart). -/
def WeilAssertions {C : Scheme.{u}} (g : C ≅ C) : Prop :=
  Exists fun [_hGeom : Abelian (heart Λ C).FullSubcategory] ↦
    Exists fun [_hWeil : Abelian (WeilHeart Λ g)] ↦
      PreservesFiniteLimits (forget Λ g) ∧ PreservesFiniteColimits (forget Λ g) ∧
      (∀ (A B D : WeilHeart Λ g) (f : A ⟶ B) (h : B ⟶ D),
        (ComposableArrows.mk₂ f h).Exact ↔
          (ComposableArrows.mk₂ ((forget Λ g).map f) ((forget Λ g).map h)).Exact) ∧
      (∀ (A B : WeilHeart Λ g) (f : A ⟶ B), Mono f ↔ Mono ((forget Λ g).map f)) ∧
      (∀ (A B : WeilHeart Λ g) (f : A ⟶ B), Epi f ↔ Epi ((forget Λ g).map f))

private lemma constructible_iso (C : Scheme.{u}) {F G : Modules Λ C}
    (e : F ≅ G) (hF : IsConstantModelConstructible Λ C F) :
    IsConstantModelConstructible Λ C G := by
  have hlocal (T : Scheme.{u}) {M N : Modules Λ T} (e : M ≅ N)
      (h : HasFiniteConstantLocalModel Λ T M) : HasFiniteConstantLocalModel Λ T N := by
    obtain ⟨U, hU⟩ := h
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstrat (T : Scheme.{u}) {M N : Modules Λ T} (e : M ≅ N)
      (h : IsFiniteConstantStratified Λ T M) : IsFiniteConstantStratified Λ T N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hlocal _ ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)
      (hS a)⟩
  unfold IsConstantModelConstructible at hF ⊢
  split_ifs at hF ⊢ with h
  · exact hstrat _ e hF
  · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hF U hU)

private lemma constructible_zero (C : Scheme.{u}) (F : Modules Λ C) (hF : IsZero F) :
    IsConstantModelConstructible Λ C F := by
  have hlocal (T : Scheme.{u}) (M : Modules Λ T) (hM : IsZero M) :
      HasFiniteConstantLocalModel Λ T M := by
    refine ⟨.singleton (𝟙 T) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    have : (upperStarFromPoint T).IsLeftAdjoint := by
      unfold upperStarFromPoint
      let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
      infer_instance
    have : PreservesFiniteColimits ((upperStarFromPoint T).mapMod Λ) := inferInstance
    have : ((upperStarFromPoint T).mapMod Λ).PreservesZeroMorphisms := by infer_instance
    refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
    · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
    · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
        (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))
  have hstrat (T : Scheme.{u}) (M : Modules Λ T) (hM : IsZero M) :
      IsFiniteConstantStratified Λ T M := by
    let S : Scheme.Stratification T := {
      n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ T
      immersion := fun _ ↦ 𝟙 T
      range_immersion := fun _ ↦ Set.range_id' }
    exact ⟨S, fun a ↦ hlocal _ _
      ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩
  classical
  unfold IsConstantModelConstructible
  split
  · exact hstrat _ _ hF
  · exact fun U _ ↦ hstrat _ _ ((CondensedRing.upperStar Λ U.ι).map_isZero hF)

private lemma punctual_zero (C : Scheme.{u}) (F : Modules Λ C) (hF : IsZero F) :
    IsPunctual Λ C F := by
  refine ⟨constructible_zero Λ C F hF, ⊤, ?_, ?_, ?_⟩
  · simp
  · simp
  · exact (CondensedRing.upperStar Λ (⊤ : C.Opens).ι).map_isZero hF

private lemma punctual_iso (C : Scheme.{u}) {F G : Modules Λ C}
    (e : F ≅ G) (hF : IsPunctual Λ C F) : IsPunctual Λ C G := by
  obtain ⟨hF, U, hU, hclosed, hz⟩ := hF
  exact ⟨constructible_iso Λ C e hF, U, hU, hclosed,
    hz.of_iso ((CondensedRing.upperStar Λ U.ι).mapIso e).symm⟩

private lemma noPunctual_zero (C : Scheme.{u}) (F : Modules Λ C) (hF : IsZero F) :
    HasNoPunctualSubsheaf Λ C F := by
  intro G i hi _
  exact IsZero.of_mono i hF

private lemma noPunctual_iso (C : Scheme.{u}) {F G : Modules Λ C}
    (e : F ≅ G) (hF : HasNoPunctualSubsheaf Λ C F) :
    HasNoPunctualSubsheaf Λ C G := by
  intro M i hi hM
  exact hF M (i ≫ e.inv) (by infer_instance) hM

private lemma heart_iff_cohomology (C : Scheme.{u})
    (K : ConstantModelBoundedConstructible Λ C) :
    heart Λ C K.obj ↔
      (∀ a : ℤ, a ≠ -1 → a ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor _ a).obj K.obj)) ∧
      IsPunctual Λ C ((DerivedCategory.homologyFunctor _ 0).obj K.obj) ∧
      HasNoPunctualSubsheaf Λ C ((DerivedCategory.homologyFunctor _ (-1)).obj K.obj) := by
  change (constantModelBoundedConstructible Λ C K.obj ∧
    ((∀ a : ℤ, 0 < a → _) ∧ _) ∧ ((∀ a : ℤ, a < 0 - 1 → _) ∧ _)) ↔ _
  constructor
  · rintro ⟨_, ⟨hu, hp⟩, hl, hn⟩
    refine ⟨fun a h₁ h₂ ↦ ?_, hp, hn⟩
    by_cases ha : 0 < a
    · exact hu a ha
    · exact hl a (by omega)
  · rintro ⟨hz, hp, hn⟩
    exact ⟨K.property, ⟨fun a ha ↦ hz a (by omega) (by omega), hp⟩,
      fun a ha ↦ hz a (by omega) (by omega), hn⟩

private lemma upper_shift (C : Scheme.{u}) (K : DerivedCategory (Modules Λ C))
    (n a n' : ℤ) (h : a + n' = n) (hK : upper Λ C n K) :
    upper Λ C n' (K⟦a⟧) := by
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · exact (hK.1 (a + i) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor (Modules Λ C) 0).shiftIso a i (a + i) rfl).app K)
  · exact punctual_iso Λ C
      (((DerivedCategory.homologyFunctor (Modules Λ C) 0).shiftIso a n' n h).app K).symm
      hK.2

private lemma lower_shift (C : Scheme.{u}) (K : DerivedCategory (Modules Λ C))
    (n a n' : ℤ) (h : a + n' = n) (hK : lower Λ C n K) :
    lower Λ C n' (K⟦a⟧) := by
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · exact (hK.1 (a + i) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor (Modules Λ C) 0).shiftIso a i (a + i) rfl).app K)
  · exact noPunctual_iso Λ C
      (((DerivedCategory.homologyFunctor (Modules Λ C) 0).shiftIso
        a (n' - 1) (n - 1) (by omega)).app K).symm hK.2

private lemma single_constructible (C : Scheme.{u}) (F : Modules Λ C)
    (hF : IsConstantModelConstructible Λ C F) (n : ℤ) :
    constantModelBoundedConstructible Λ C ((DerivedCategory.singleFunctor _ n).obj F) := by
  let K := (DerivedCategory.singleFunctor (Modules Λ C) n).obj F
  refine ⟨⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, fun i ↦ ?_⟩
  by_cases hi : i = n
  · subst i
    exact constructible_iso Λ C
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Λ C) n).app F).symm hF
  · apply constructible_zero Λ C
    by_cases h : i < n
    · exact DerivedCategory.isZero_of_isGE K n i h
    · exact DerivedCategory.isZero_of_isLE K n i (by omega)

private lemma heart_single_punctual (C : Scheme.{u}) (F : Modules Λ C)
    (hF : IsPunctual Λ C F) : heart Λ C ((DerivedCategory.singleFunctor _ 0).obj F) := by
  let K := (DerivedCategory.singleFunctor (Modules Λ C) 0).obj F
  refine ⟨single_constructible Λ C F hF.1 0, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    exact DerivedCategory.isZero_of_isLE K 0 a ha
  · exact punctual_iso Λ C
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Λ C) 0).app F).symm hF
  · intro a ha
    exact DerivedCategory.isZero_of_isGE K 0 a (by omega)
  · exact noPunctual_zero Λ C _ (DerivedCategory.isZero_of_isGE K 0 (0 - 1) (by omega))

private lemma heart_single_shift_noPunctual (C : Scheme.{u}) (F : Modules Λ C)
    (hF : IsConstantModelConstructible Λ C F) (hn : HasNoPunctualSubsheaf Λ C F) :
    heart Λ C (((DerivedCategory.singleFunctor _ 0).obj F)⟦(1 : ℤ)⟧) := by
  let K := (DerivedCategory.singleFunctor (Modules Λ C) 0).obj F
  have hb := single_constructible Λ C F hF 0
  have hbc : constantModelBoundedConstructible Λ C (K⟦(1 : ℤ)⟧) := by
    refine ⟨DerivedCategory.TStructure.t.bounded.le_shift (1 : ℤ) K hb.1, fun i ↦ ?_⟩
    exact constructible_iso Λ C
      (((DerivedCategory.homologyFunctor (Modules Λ C) 0).shiftIso
        1 i (1 + i) rfl).app K).symm (hb.2 _)
  have hu : upper Λ C 1 K :=
    ⟨fun a ha ↦ DerivedCategory.isZero_of_isLE K 0 a (by omega),
      punctual_zero Λ C _ (DerivedCategory.isZero_of_isLE K 0 1 (by omega))⟩
  have hl : lower Λ C 1 K :=
    ⟨fun a ha ↦ DerivedCategory.isZero_of_isGE K 0 a (by omega),
      noPunctual_iso Λ C
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Λ C) 0).app F).symm hn⟩
  exact ⟨hbc, upper_shift Λ C K 1 1 0 (by omega) hu,
    lower_shift Λ C K 1 1 0 (by omega) hl⟩

private lemma upper_iso (C : Scheme.{u}) (n : ℤ)
    {K L : DerivedCategory (Modules Λ C)} (e : K ≅ L) (hK : upper Λ C n K) :
    upper Λ C n L := by
  exact ⟨fun a ha ↦ (hK.1 a ha).of_iso
    ((DerivedCategory.homologyFunctor _ a).mapIso e).symm,
    punctual_iso Λ C ((DerivedCategory.homologyFunctor _ n).mapIso e) hK.2⟩

private lemma lower_iso (C : Scheme.{u}) (n : ℤ)
    {K L : DerivedCategory (Modules Λ C)} (e : K ≅ L) (hK : lower Λ C n K) :
    lower Λ C n L := by
  exact ⟨fun a ha ↦ (hK.1 a ha).of_iso
    ((DerivedCategory.homologyFunctor _ a).mapIso e).symm,
    noPunctual_iso Λ C ((DerivedCategory.homologyFunctor _ (n - 1)).mapIso e) hK.2⟩

private lemma upper_le_next (C : Scheme.{u}) (n : ℤ)
    (K : DerivedCategory (Modules Λ C)) (hK : upper Λ C n K) : upper Λ C (n + 1) K := by
  exact ⟨fun a ha ↦ hK.1 a (by omega), punctual_zero Λ C _ (hK.1 _ (by omega))⟩

private lemma lower_ge_prev (C : Scheme.{u}) (n : ℤ)
    (K : DerivedCategory (Modules Λ C)) (hK : lower Λ C (n + 1) K) : lower Λ C n K := by
  exact ⟨fun a ha ↦ hK.1 a (by omega), noPunctual_zero Λ C _ (hK.1 _ (by omega))⟩

private lemma punctual_image (C : Scheme.{u})
    (hclosure : ∀ (F G : Modules Λ C) (f : F ⟶ G),
      IsConstantModelConstructible Λ C F → IsConstantModelConstructible Λ C G →
        IsConstantModelConstructible Λ C (kernel f) ∧
        IsConstantModelConstructible Λ C (cokernel f))
    {F G : Modules Λ C} (f : F ⟶ G) (hF : IsPunctual Λ C F)
    (hG : IsConstantModelConstructible Λ C G) : IsPunctual Λ C (image f) := by
  obtain ⟨hcF, U, hU, hclosed, hz⟩ := hF
  have hk := (hclosure F G f hcF hG).1
  have hi := (hclosure (kernel f) F (kernel.ι f) hk hcF).2
  refine ⟨constructible_iso Λ C (Abelian.coimageIsoImage' f) hi,
    U, hU, hclosed, ?_⟩
  exact IsZero.of_epi ((CondensedRing.upperStar Λ U.ι).map (factorThruImage f)) hz

private lemma perverse_orthogonal (C : Scheme.{u})
    (hclosure : ∀ (F G : Modules Λ C) (f : F ⟶ G),
      IsConstantModelConstructible Λ C F → IsConstantModelConstructible Λ C G →
        IsConstantModelConstructible Λ C (kernel f) ∧
        IsConstantModelConstructible Λ C (cokernel f))
    (A B : ConstantModelBoundedConstructible Λ C) (f : A.obj ⟶ B.obj)
    (hA : upper Λ C 0 A.obj) (hB : lower Λ C 1 B.obj) : f = 0 := by
  have : A.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).2 hA.1
  have : B.obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).2 (by
    simpa using hB.1)
  apply (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1
  dsimp only
  rw [Functor.map_zero]
  let f₀ := (DerivedCategory.homologyFunctor (Modules Λ C) 0).map f
  have hp := punctual_image Λ C hclosure f₀ hA.2 (B.property.2 0)
  have hz := hB.2 (image f₀) (image.ι f₀) (by infer_instance) hp
  change f₀ = 0
  rw [← image.fac f₀, hz.eq_of_tgt (factorThruImage f₀) 0, zero_comp]

private lemma boundedConstructible_iso (C : Scheme.{u})
    {K L : DerivedCategory (Modules Λ C)} (e : K ≅ L)
    (hK : constantModelBoundedConstructible Λ C K) :
    constantModelBoundedConstructible Λ C L := by
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ constructible_iso Λ C ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

private lemma fibre_upper (C : Scheme.{u})
    (K : DerivedCategory (Modules Λ C)) (hK : K.IsLE 0)
    (Q : Modules Λ C) (f : K ⟶ (DerivedCategory.singleFunctor _ 0).obj Q)
    (hf : Epi ((DerivedCategory.homologyFunctor _ 0).map f))
    (hp : IsPunctual Λ C (kernel ((DerivedCategory.homologyFunctor _ 0).map f)))
    (A : DerivedCategory (Modules Λ C)) (i : A ⟶ K)
    (δ : (DerivedCategory.singleFunctor _ 0).obj Q ⟶ A⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk i f δ ∈ distTriang _) :
    upper Λ C 0 A := by
  let T := Pretriangulated.Triangle.mk i f δ
  have hz (a : ℤ) (ha : a ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (Modules Λ C) a).obj
        ((DerivedCategory.singleFunctor _ 0).obj Q)) := by
    by_cases h : a < 0
    · exact DerivedCategory.isZero_of_isGE _ 0 a h
    · exact DerivedCategory.isZero_of_isLE _ 0 a (by omega)
  have hm : Mono ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map i) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0 (by omega)).2
      ((hz (-1) (by omega)).eq_of_src _ _)
  have hmT : Mono ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map T.mor₁) := by
    change Mono ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map i)
    exact hm
  have he := DerivedCategory.HomologySequence.exact₂ T hT 0
  have e := he.fIsKernel.conePointUniqueUpToIso
    (kernelIsKernel ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map f))
  refine ⟨fun a ha ↦ ?_, punctual_iso Λ C e.symm hp⟩
  have hKa := DerivedCategory.isZero_of_isLE K 0 a ha
  have hex := DerivedCategory.HomologySequence.exact₁ T hT (a - 1) a (by omega)
  apply hex.isZero_X₂ _ (hKa.eq_of_tgt _ _)
  by_cases h : a = 1
  · subst a
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1
      (by omega)).1 hf
  · exact (hz (a - 1) (by omega)).eq_of_src _ _

private lemma lower_extension (C : Scheme.{u}) (Q : Modules Λ C)
    (hn : HasNoPunctualSubsheaf Λ C Q)
    (B T : DerivedCategory (Modules Λ C)) (hTge : T.IsGE 1)
    (f : (DerivedCategory.singleFunctor _ 0).obj Q ⟶ B) (g : B ⟶ T)
    (δ : T ⟶ ((DerivedCategory.singleFunctor _ 0).obj Q)⟦(1 : ℤ)⟧)
    (h : Pretriangulated.Triangle.mk f g δ ∈ distTriang _) :
    lower Λ C 1 B := by
  have hg : B.IsGE 0 := DerivedCategory.TStructure.t.isGE₂ (Pretriangulated.Triangle.mk f g δ) h 0
    (by change ((DerivedCategory.singleFunctor (Modules Λ C) 0).obj Q).IsGE 0
        infer_instance) (DerivedCategory.TStructure.t.isGE_of_ge T 0 1 (by omega))
  have hi := DerivedCategory.isIso_homologyMap_mor₁
    (Pretriangulated.Triangle.mk f g δ) h (-1) 0 (by omega)
    (DerivedCategory.isZero_of_isGE T 1 (-1) (by omega))
    (DerivedCategory.isZero_of_isGE T 1 0 (by omega))
  have hif : IsIso ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map f) := by
    exact hi
  refine ⟨fun a ha ↦ DerivedCategory.isZero_of_isGE B 0 a (by omega), ?_⟩
  exact noPunctual_iso Λ C
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Λ C) 0).app Q).symm ≪≫
      asIso ((DerivedCategory.homologyFunctor _ 0).map f)) hn

private lemma perverse_triangle (C : Scheme.{u})
    [hTri : (constantModelBoundedConstructible Λ C).IsTriangulated]
    (htrunc : ∀ K : ConstantModelBoundedConstructible Λ C,
      constantModelBoundedConstructible Λ C
        ((DerivedCategory.TStructure.t.truncLE 0).obj K.obj))
    (htors : ∀ F : Modules Λ C, IsConstantModelConstructible Λ C F →
      ∃ (P : Modules Λ C) (i : P ⟶ F) (_ : Mono i), IsPunctual Λ C P ∧
        IsConstantModelConstructible Λ C (cokernel i) ∧
        HasNoPunctualSubsheaf Λ C (cokernel i))
    (K : ConstantModelBoundedConstructible Λ C) :
    ∃ (A B : ConstantModelBoundedConstructible Λ C),
      upper Λ C 0 A.obj ∧ lower Λ C 1 B.obj ∧
      ∃ (f : A ⟶ K) (g : K ⟶ B) (δ : B ⟶ A⟦(1 : ℤ)⟧),
        Pretriangulated.Triangle.mk f g δ ∈ distTriang _ := by
  let Pbc := constantModelBoundedConstructible Λ C
  have : Pbc.IsClosedUnderIsomorphisms := ⟨fun e h ↦ boundedConstructible_iso Λ C e h⟩
  let t := DerivedCategory.TStructure.t (C := Modules Λ C)
  let K' := (t.truncLE 0).obj K.obj
  have hK' : Pbc K' := htrunc K
  let F := (DerivedCategory.homologyFunctor (Modules Λ C) 0).obj K.obj
  obtain ⟨P, i, hi, hp, hq, hn⟩ := htors F (K.property.2 0)
  let Q := cokernel i
  let q := cokernel.π i
  let Q₀ := (DerivedCategory.singleFunctor (Modules Λ C) 0).obj Q
  have hQ : Pbc Q₀ := single_constructible Λ C Q hq 0
  have hLE : K'.IsLE 0 := by dsimp [K', t]; infer_instance
  have hGE : Q₀.IsGE 0 := by dsimp [Q₀]; infer_instance
  have heK : IsIso ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map
      ((t.truncLEι 0).app K.obj)) := by
    change IsIso ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map
      ((DerivedCategory.TStructure.t.truncLTι (0 + 1)).app K.obj))
    exact DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K.obj (0 + 1) 0 (by omega)
  let eK : (DerivedCategory.homologyFunctor (Modules Λ C) 0).obj K' ≅ F :=
    asIso ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map
      ((t.truncLEι 0).app K.obj))
  let eQ : (DerivedCategory.homologyFunctor (Modules Λ C) 0).obj Q₀ ≅ Q :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Λ C) 0).app Q
  obtain ⟨v, hv⟩ :=
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
      (X := K') (Y := Q₀) 0).2 (eK.hom ≫ q ≫ eQ.inv)
  dsimp only at hv
  have hvEpi : Epi ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map v) := by
    rw [hv]
    infer_instance
  have hkernel : IsPunctual Λ C
      (kernel ((DerivedCategory.homologyFunctor (Modules Λ C) 0).map v)) := by
    rw [hv, ← Category.assoc]
    let e := kernelCompMono (eK.hom ≫ q) eQ.inv ≪≫
      kernelIsIsoComp eK.hom q ≪≫
      (kernelIsKernel q).conePointUniqueUpToIso
        (Abelian.monoIsKernelOfCokernel
        (Cofork.ofπ (cokernel.π i) (by simp)) (cokernelIsCokernel i))
    exact punctual_iso Λ C e.symm hp
  obtain ⟨A, a, δA, hA⟩ := Pretriangulated.distinguished_cocone_triangle₁ v
  have hPA : Pbc A := Pbc.ext_of_isTriangulatedClosed₁ _ hA hK' hQ
  have hupper := fibre_upper Λ C K' hLE Q v hvEpi hkernel A a δA hA
  let u := (t.truncLEι 0).app K.obj
  obtain ⟨B, b, δB, hB⟩ := Pretriangulated.distinguished_cocone_triangle (a ≫ u)
  have hPB : Pbc B := Pbc.ext_of_isTriangulatedClosed₃ _ hB hPA K.property
  let o := someOctahedron rfl hA (t.triangleLEGE_distinguished 0 1 (by omega) K.obj) hB
  have hlower := lower_extension Λ C Q hn B ((t.truncGE 1).obj K.obj)
    (by dsimp [t]; infer_instance) o.m₁ o.m₃ _ o.mem
  refine ⟨⟨A, hPA⟩, ⟨B, hPB⟩, hupper, hlower,
    ObjectProperty.homMk (a ≫ u), ObjectProperty.homMk b,
    ObjectProperty.homMk (δB ≫ (Pbc.ι.commShiftIso (1 : ℤ)).inv.app ⟨A, hPA⟩), ?_⟩
  change (Pbc.ι.mapTriangle.obj _) ∈ distTriang _
  apply Pretriangulated.isomorphic_distinguished _ hB _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by dsimp [Functor.mapTriangle]; simp)
    (by dsimp [Functor.mapTriangle]; simp)
    (by simp [Functor.mapTriangle, Pretriangulated.Triangle.mk])

private lemma perverse_tStructure (C : Scheme.{u})
    [hTri : (constantModelBoundedConstructible Λ C).IsTriangulated]
    (hclosure : ∀ (F G : Modules Λ C) (f : F ⟶ G),
      IsConstantModelConstructible Λ C F → IsConstantModelConstructible Λ C G →
        IsConstantModelConstructible Λ C (kernel f) ∧
        IsConstantModelConstructible Λ C (cokernel f))
    (htrunc : ∀ K : ConstantModelBoundedConstructible Λ C,
      constantModelBoundedConstructible Λ C
        ((DerivedCategory.TStructure.t.truncLE 0).obj K.obj))
    (htors : ∀ F : Modules Λ C, IsConstantModelConstructible Λ C F →
      ∃ (P : Modules Λ C) (i : P ⟶ F) (_ : Mono i), IsPunctual Λ C P ∧
        IsConstantModelConstructible Λ C (cokernel i) ∧
        HasNoPunctualSubsheaf Λ C (cokernel i)) :
    ∃ t : TStructure (ConstantModelBoundedConstructible Λ C),
      (∀ K n, t.le n K ↔ upper Λ C n K.obj) ∧
      (∀ K n, t.ge n K ↔ lower Λ C n K.obj) ∧ t.bounded = ⊤ := by
  let P := constantModelBoundedConstructible Λ C
  let t : TStructure P.FullSubcategory := {
    le := fun n K ↦ upper Λ C n K.obj
    ge := fun n K ↦ lower Λ C n K.obj
    le_isClosedUnderIsomorphisms := fun n ↦
      ⟨fun e h ↦ upper_iso Λ C n (P.ι.mapIso e) h⟩
    ge_isClosedUnderIsomorphisms := fun n ↦
      ⟨fun e h ↦ lower_iso Λ C n (P.ι.mapIso e) h⟩
    le_shift := fun n a n' h K hK ↦ upper_iso Λ C n'
      ((P.ι.commShiftIso a).symm.app K) (upper_shift Λ C K.obj n a n' h hK)
    ge_shift := fun n a n' h K hK ↦ lower_iso Λ C n'
      ((P.ι.commShiftIso a).symm.app K) (lower_shift Λ C K.obj n a n' h hK)
    zero' := fun {A B} f hA hB ↦ ObjectProperty.hom_ext _
      (perverse_orthogonal Λ C hclosure A B f.hom hA hB)
    le_zero_le := fun K hK ↦ upper_le_next Λ C 0 K.obj hK
    ge_one_le := fun K hK ↦ lower_ge_prev Λ C 0 K.obj hK
    exists_triangle_zero_one := fun K ↦ by
      obtain ⟨A, B, hA, hB, f, g, δ, hT⟩ := perverse_triangle Λ C htrunc htors K
      exact ⟨A, B, hA, hB, f, g, δ, hT⟩ }
  refine ⟨t, fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl, ?_⟩
  apply le_antisymm le_top
  intro K _
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  refine ⟨⟨a, ⟨⟨?_, ?_⟩⟩⟩, ⟨b + 1, ⟨⟨?_, ?_⟩⟩⟩⟩
  · intro i hi
    exact DerivedCategory.isZero_of_isGE K.obj a i (by omega)
  · exact noPunctual_zero Λ C _
      (DerivedCategory.isZero_of_isGE K.obj a (a - 1) (by omega))
  · intro i hi
    exact DerivedCategory.isZero_of_isLE K.obj b i (by omega)
  · exact punctual_zero Λ C _
      (DerivedCategory.isZero_of_isLE K.obj b (b + 1) (by omega))

private def heart_equivalence (C : Scheme.{u})
    [(constantModelBoundedConstructible Λ C).IsTriangulated]
    (t : TStructure (ConstantModelBoundedConstructible Λ C))
    (hle : ∀ K n, t.le n K ↔ upper Λ C n K.obj)
    (hge : ∀ K n, t.ge n K ↔ lower Λ C n K.obj) :
    (heart Λ C).FullSubcategory ≌ t.heart.FullSubcategory where
  functor := {
    obj K := ⟨⟨K.obj, K.property.1⟩,
      (hle _ 0).2 K.property.2.1, (hge _ 0).2 K.property.2.2⟩
    map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  inverse := {
    obj K := ⟨K.obj.obj, K.obj.property,
      (hle _ 0).1 K.property.1, (hge _ 0).1 K.property.2⟩
    map f := ObjectProperty.homMk f.hom.hom }
  unitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (by intros; ext; simp)
  counitIso := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _)))
    (by intros; ext; simp)
  functor_unitIso_comp K := by ext; simp

private lemma heart_abelian (C : Scheme.{u})
    [(constantModelBoundedConstructible Λ C).IsTriangulated]
    (t : TStructure (ConstantModelBoundedConstructible Λ C))
    (hle : ∀ K n, t.le n K ↔ upper Λ C n K.obj)
    (hge : ∀ K n, t.ge n K ↔ lower Λ C n K.obj) :
    Nonempty (Abelian (heart Λ C).FullSubcategory) := by
  let e := heart_equivalence Λ C t hle hge
  let hAb : Abelian t.heart.FullSubcategory :=
    TStructure.abelianHeartFullSubcategory t
  let hprod : HasFiniteProducts t.heart.FullSubcategory :=
    @Abelian.has_finite_products _ _ hAb
  let : HasFiniteProducts (heart Λ C).FullSubcategory := ⟨fun n ↦ by
    let : HasLimitsOfShape (Discrete (Fin n)) t.heart.FullSubcategory :=
      @HasFiniteProducts.out _ _ hprod n
    exact Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact ⟨abelianOfEquivalence e.functor⟩

private theorem geometric_pure (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    (hPure : C₀.left.IsPureDimension 1) :
    (D.geometricFiber C₀).left.IsPureDimension 1 := by
  let e : ↥(⊤ : C₀.left.Opens) ≃ₜ C₀.left := Homeomorph.Set.univ _
  have ht : ∀ Z ∈ irreducibleComponents ↥(⊤ : C₀.left.Opens),
      topologicalKrullDim Z = (1 : WithBot ℕ∞) := by
    intro Z hZ
    have hZ' : e.symm ⁻¹' Z ∈ irreducibleComponents C₀.left := by
      apply preimage_mem_irreducibleComponents hZ e.symm.isOpenEmbedding
      simpa only [e.symm.surjective.range_eq, Set.inter_univ] using hZ.1.nonempty
    let eZ : Z ≃ₜ e.symm ⁻¹' Z := e.subtype (by simp)
    exact (IsHomeomorph.topologicalKrullDim_eq eZ eZ.isHomeomorph).trans (hPure _ hZ')
  exact (field_extension_component_local_dimension (L := D.k) C₀.hom).2.2.2 1
    (fun x ↦ topologicalKrullDimAt_eq_of_equidimensional_open C₀.hom ⊤ 1 ht x (by trivial))

private def pullEquivalence {C : Scheme.{u}} (g : C ≅ C) :
    Modules Λ C ≌ Modules Λ C :=
  CategoryTheory.Equivalence.mk
    (CondensedRing.upperStar Λ g.hom) (CondensedRing.upperStar Λ g.inv)
    ((CondensedRing.upperStarId Λ C).symm ≪≫
      CondensedRing.upperStarCongr Λ g.inv_hom_id.symm ≪≫
      CondensedRing.upperStarComp Λ g.inv g.hom)
    ((CondensedRing.upperStarComp Λ g.hom g.inv).symm ≪≫
      CondensedRing.upperStarCongr Λ g.hom_inv_id ≪≫ CondensedRing.upperStarId Λ C)

private instance pullEquivalence_functor_additive {C : Scheme.{u}} (g : C ≅ C) :
    (pullEquivalence Λ g).functor.Additive :=
  inferInstanceAs (CondensedRing.upperStar Λ g.hom).Additive

private instance pullEquivalence_inverse_additive {C : Scheme.{u}} (g : C ≅ C) :
    (pullEquivalence Λ g).inverse.Additive :=
  inferInstanceAs (CondensedRing.upperStar Λ g.inv).Additive

private lemma punctual_pull (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C]
    (f : C ⟶ C) [IsIso f] (G : Modules Λ C) (hG : IsPunctual Λ C G) :
    IsPunctual Λ C ((CondensedRing.upperStar Λ f).obj G) := by
  obtain ⟨hG, U, hf, hclosed, hz⟩ := hG
  let W := f ⁻¹ᵁ U
  refine ⟨(hc f G hG).1, W, ?_, ?_, ?_⟩
  · exact hf.preimage f.homeomorph.injective.injOn
  · intro x hx
    have he : f ⁻¹' ({f x} : Set C) = ({x} : Set C) := by
      ext y
      exact f.homeomorph.injective.eq_iff
    rw [← he]
    exact (hclosed (f x) hx).preimage f.continuous
  · exact CondensedRing.isZero_upperStar_restrict Λ f U W rfl G hz

private lemma noSubobjects_pull {A : Type*} [Category A]
    (P : ObjectProperty A) (F G : A ⥤ A) [G.Full] [G.Faithful]
    [G.PreservesMonomorphisms] (η : F ⋙ G ≅ 𝟭 A)
    (hP : ∀ X, P X → P (G.obj X))
    (X : A) (hX : ∀ Y (i : Y ⟶ X), Mono i → P Y → IsZero Y) :
    ∀ Y (i : Y ⟶ F.obj X), Mono i → P Y → IsZero Y := by
  intro Y i hi hY
  let j : G.obj Y ⟶ X := G.map i ≫ η.hom.app X
  have : Mono j := by dsimp [j]; infer_instance
  have hz := hX (G.obj Y) j inferInstance (hP Y hY)
  exact IsZero.of_full_of_faithful_of_isZero G Y hz

private def pullInverseUnit {C : Scheme.{u}} (g : C ≅ C) :
    CondensedRing.upperStar Λ g.hom ⋙ CondensedRing.upperStar Λ g.inv ≅ 𝟭 (Modules Λ C) :=
  (CondensedRing.upperStarComp Λ g.inv g.hom).symm ≪≫
    CondensedRing.upperStarCongr Λ g.inv_hom_id ≪≫ CondensedRing.upperStarId Λ C

private lemma pull_inverse_full {C : Scheme.{u}} (g : C ≅ C) :
    (CondensedRing.upperStar Λ g.inv).Full :=
  inferInstanceAs (pullEquivalence Λ g).inverse.Full

private lemma pull_inverse_faithful {C : Scheme.{u}} (g : C ≅ C) :
    (CondensedRing.upperStar Λ g.inv).Faithful :=
  inferInstanceAs (pullEquivalence Λ g).inverse.Faithful

private lemma pull_inverse_mono {C : Scheme.{u}} (g : C ≅ C) :
    (CondensedRing.upperStar Λ g.inv).PreservesMonomorphisms :=
  inferInstanceAs (pullEquivalence Λ g).inverse.PreservesMonomorphisms

private lemma noPunctual_pull (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C]
    (g : C ≅ C) (F : Modules Λ C) (hF : HasNoPunctualSubsheaf Λ C F) :
    HasNoPunctualSubsheaf Λ C ((CondensedRing.upperStar Λ g.hom).obj F) := by
  let := pull_inverse_full Λ g
  let := pull_inverse_faithful Λ g
  let := pull_inverse_mono Λ g
  exact noSubobjects_pull (IsPunctual Λ C)
    (CondensedRing.upperStar Λ g.hom) (CondensedRing.upperStar Λ g.inv)
    (pullInverseUnit Λ g) (punctual_pull Λ hc g.inv) F hF

private lemma heart_pull (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C]
    (g : C ≅ C) (K : DerivedCategory (Modules Λ C)) (hK : heart Λ C K) :
    heart Λ C ((CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj K) := by
  let F := CondensedRing.upperStar Λ g.hom
  have hH (n : ℤ) := (F.mapDerivedCategoryHomologyFunctorIso n).app K
  refine ⟨(CondensedRing.StrictWeilCondensed.action_preserves Λ g K).1.mpr hK.1,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a ha
    exact (F.map_isZero (hK.2.1.1 a ha)).of_iso (hH a).symm
  · exact punctual_iso Λ C (hH 0) (punctual_pull Λ hc g.hom _ hK.2.1.2)
  · intro a ha
    exact (F.map_isZero (hK.2.2.1 a ha)).of_iso (hH a).symm
  · exact noPunctual_iso Λ C (hH (0 - 1)) (noPunctual_pull Λ hc g _ hK.2.2.2)

private def restrictEquivalence {A : Type*} [Category A]
    (P : ObjectProperty A) (E : A ≌ A)
    (hF : ∀ X, P X → P (E.functor.obj X))
    (hG : ∀ X, P X → P (E.inverse.obj X)) :
    P.FullSubcategory ≌ P.FullSubcategory where
  functor := P.lift (P.ι ⋙ E.functor) (fun X ↦ hF X.obj X.property)
  inverse := P.lift (P.ι ⋙ E.inverse) (fun X ↦ hG X.obj X.property)
  unitIso := NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (E.unitIso.app X.obj))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact E.unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (E.counitIso.app X.obj))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact E.counitIso.hom.naturality f.hom)
  functor_unitIso_comp X := ObjectProperty.hom_ext _ (E.functor_unit_comp X.obj)

private def heartPullEquivalence (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C] (g : C ≅ C) :
    (heart Λ C).FullSubcategory ≌ (heart Λ C).FullSubcategory :=
  restrictEquivalence (heart Λ C) (pullEquivalence Λ g).mapDerivedCategory
    (heart_pull Λ hc g) (heart_pull Λ hc g.symm)

private def weilHeartEquivalence (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C] (g : C ≅ C) :
    WeilHeart Λ g ≌ Endofunctor.IsoAlgebra (heartPullEquivalence Λ hc g).functor where
  functor := {
    obj K := Endofunctor.IsoAlgebra.mk ⟨K.obj.carrier, K.property⟩
      (ObjectProperty.isoMk _ K.obj.str)
    map f := ObjectProperty.homMk {
      f := ObjectProperty.homMk f.hom.hom.f
      h := ObjectProperty.hom_ext _ f.hom.hom.h } }
  inverse := {
    obj K := ⟨Endofunctor.IsoAlgebra.mk K.carrier.obj ((heart Λ C).ι.mapIso K.str),
      K.carrier.property⟩
    map f := ObjectProperty.homMk (ObjectProperty.homMk {
      f := f.hom.f.hom
      h := congrArg (fun f ↦ f.hom) f.hom.h }) }
  unitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk (Iso.refl _))))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.Hom.ext
      simp)
  counitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Endofunctor.Algebra.isoMk (ObjectProperty.isoMk _ (Iso.refl _))
      (by
        apply ObjectProperty.hom_ext
        change (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
        simp)))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.Hom.ext
      apply ObjectProperty.hom_ext
      simp)
  functor_unitIso_comp K := by
    apply ObjectProperty.hom_ext
    apply Endofunctor.Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    exact Category.id_comp _

private lemma faithful_exact_tests {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [hZA : HasZeroMorphisms A] [hZB : HasZeroMorphisms B]
    (U : A ⥤ B) [U.Faithful] [U.PreservesZeroMorphisms]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] :
    (∀ (X Y Z : A) (f : X ⟶ Y) (h : Y ⟶ Z),
      (ComposableArrows.mk₂ f h).Exact ↔
        (ComposableArrows.mk₂ (U.map f) (U.map h)).Exact) ∧
    (∀ (X Y : A) (f : X ⟶ Y), Mono f ↔ Mono (U.map f)) ∧
    (∀ (X Y : A) (f : X ⟶ Y), Epi f ↔ Epi (U.map f)) := by
  cases Subsingleton.elim hZA (@Preadditive.preadditiveHasZeroMorphisms A _ inferInstance)
  cases Subsingleton.elim hZB (@Preadditive.preadditiveHasZeroMorphisms B _ inferInstance)
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z f h
    constructor
    · intro hex
      have hz : f ≫ h = 0 := by
        simpa [-Fin.reduceFinMk] using hex.toIsComplex.zero 0 (by omega)
      have hs : (ShortComplex.mk f h hz).Exact :=
        (ShortComplex.exact_iff_exact_toComposableArrows _).2 hex
      exact (hs.map U).exact_toComposableArrows
    · intro hex
      have hmap : U.map f ≫ U.map h = 0 := by
        simpa [-Fin.reduceFinMk] using hex.toIsComplex.zero 0 (by omega)
      have hz : f ≫ h = 0 := U.map_injective (by simpa using hmap)
      have hs : (ShortComplex.mk f h hz).Exact :=
        ((ShortComplex.mk f h hz).exact_map_iff_of_faithful U).1
          ((ShortComplex.exact_iff_exact_toComposableArrows _).2 hex)
      exact hs.exact_toComposableArrows
  · intro X Y f
    exact (U.mono_map_iff_mono f).symm
  · intro X Y f
    exact (U.epi_map_iff_epi f).symm

private lemma equivalence_additive {A : Type*} [Category A]
    [Preadditive A] [HasFiniteProducts A]
    (E : A ≌ A) : E.functor.Additive :=
  Functor.additive_of_preserves_binary_products E.functor

private lemma weil_assertions_of_geometric (hc : ConstantModelPullbackStatement Λ)
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C] (g : C ≅ C)
    (hG : Nonempty (Abelian (heart Λ C).FullSubcategory)) : WeilAssertions Λ g := by
  let hZA : HasZeroMorphisms (WeilHeart Λ g) := inferInstance
  let hZB : HasZeroMorphisms (heart Λ C).FullSubcategory := inferInstance
  let hpre : Preadditive (heart Λ C).FullSubcategory := inferInstance
  let hAb : Abelian (heart Λ C).FullSubcategory := hG.some
  let hprod : HasFiniteProducts (heart Λ C).FullSubcategory :=
    @Abelian.has_finite_products _ _ hAb
  let : Abelian (heart Λ C).FullSubcategory :=
    @abelianOfEquivalence _ _ hpre hprod _ _ hAb (𝟭 _) inferInstance
  let : HasFiniteProducts (heart Λ C).FullSubcategory := hprod
  let H := (heartPullEquivalence Λ hc g).functor
  let : PreservesFiniteLimits H := inferInstance
  let : PreservesFiniteColimits H := inferInstance
  let : H.Additive := equivalence_additive (heartPullEquivalence Λ hc g)
  let e := weilHeartEquivalence Λ hc g
  let : HasFiniteProducts (WeilHeart Λ g) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  let : Abelian (WeilHeart Λ g) := abelianOfEquivalence e.functor
  have he : e.functor ⋙ Endofunctor.IsoAlgebra.forget H ≅ forget Λ g := Iso.refl _
  let : PreservesFiniteLimits (forget Λ g) := preservesFiniteLimits_of_natIso he
  let : PreservesFiniteColimits (forget Λ g) := preservesFiniteColimits_of_natIso he
  let : (forget Λ g).Faithful := by
    exact inferInstanceAs (e.functor ⋙ Endofunctor.IsoAlgebra.forget H).Faithful
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact faithful_exact_tests (hZA := hZA) (hZB := hZB) (forget Λ g)

private lemma weil_assertions_qbar (ell : ℕ) [Fact ell.Prime]
    {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C] (g : C ≅ C)
    (hG : Nonempty (Abelian (heart (Profinite.padicAlgClRingObj ell) C).FullSubcategory)) :
    WeilAssertions (Profinite.padicAlgClRingObj ell) g := by
  exact weil_assertions_of_geometric _ (constantModelPullback _) g hG

/-- The perverse Weil heart is abelian and its canonical forgetful functor is exact
and reflects exactness, on the geometric fibre of any smooth curve over the fixed
finite field. Source: current blueprint sk-lem-wft-curve-heart, Weil assertions
(blueprint: sk-lem-wft-curve-heart).

Proof: Use the preceding geometric construction. Geometric Frobenius inverse image
and its inverse are exact equivalences and commute with ordinary cohomology. They
reindex finite closed sets and preserve monomorphisms, hence preserve punctual
sheaves and the absence of punctual subobjects. They preserve both perverse classes.
Restrict the derived pullback equivalence to the geometric heart and identify the
stated Weil heart with the invertible algebras of this additive equivalence. The
existing IsoAlgebra.abelian and forgetful finite-limit/finite-colimit instances create
kernels and cokernels with their induced invertible Frobenius maps. Transfer these
structures across the explicit equivalence, whose underlying forgetful functor is
unchanged. Faithful exact forgetting reflects short-complex exactness and the endpoint
mono and epi conditions. These are steps 6--7 of the DAG proof; the Frobenius and
strict-pair morphisms are exactly sk-def-sf-weil-complexes. -/
theorem curve_perverse_weil_heart (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (C₀ : Over (Spec (.of D.k₀))) [Smooth C₀.hom] [QuasiCompact C₀.hom]
    [IsSeparated C₀.hom] (_hPure : C₀.left.IsPureDimension 1) :
    WeilAssertions (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius C₀) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  have hunit : IsUnit (ell : D.k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : ell.Prime) (Ne.symm _hEll))
  have hsm : Smooth (D.geometricFiber C₀).hom := by
    dsimp [WeilConjectures.FiniteFieldDatum.geometricFiber]; infer_instance
  have hqc : QuasiCompact (D.geometricFiber C₀).hom := by
    dsimp [WeilConjectures.FiniteFieldDatum.geometricFiber]; infer_instance
  have hsep : IsSeparated (D.geometricFiber C₀).hom := by
    dsimp [WeilConjectures.FiniteFieldDatum.geometricFiber]; infer_instance
  have hpure := geometric_pure D C₀ _hPure
  generalize hg : D.geometricFrobenius C₀ = g at ⊢
  clear hg
  generalize ht : D.geometricFiber C₀ = C at g hsm hqc hsep hpure ⊢
  let : Smooth C.hom := hsm
  let : QuasiCompact C.hom := hqc
  let : IsSeparated C.hom := hsep
  let : CompactSpace C.left := QuasiCompact.compactSpace_of_compactSpace C.hom
  let : QuasiSeparatedSpace C.left := quasiSeparatedSpace_of_quasiSeparated C.hom
  have hgeom := curve_perverse_heart ell D.k hunit C hpure
  exact weil_assertions_qbar ell g hgeom.2.1

end AlgebraicGeometry.ProEtale.CondensedCurvePerverse
