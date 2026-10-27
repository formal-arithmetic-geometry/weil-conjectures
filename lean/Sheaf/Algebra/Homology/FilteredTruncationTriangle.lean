/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Algebra.Homology.FilteredTruncationData
import Sheaf.Algebra.Homology.FilteredTruncationConstruction
import Sheaf.Algebra.Homology.UniformFilteredTruncation
import Sheaf.Algebra.Homology.FilteredBoundedLocalizationComparison
import Mathlib.CategoryTheory.Localization.Equivalence
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension

/-!
# Universal truncation triangles for finite filtered derived categories

Source: Varshavsky--Lefschetz--Verdier trace formula, §§5.1.1--5.1.2,
pp. 39--40 (blueprint: lem-trf-filtered-truncation-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated
open ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section TriangleComparison

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

private lemma triangle_hom_ext_middle (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (hs : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃))
    (f g : T ⟶ T') (h : f.hom₂ = g.hom₂) : f = g := by
  obtain ⟨h₁, h₃, _⟩ := (triangle_morphism_extension T T' hT hT' f.hom₂).2.1 hs
  apply Triangle.hom_ext
  · exact h₁ _ _ f.comm₁.symm (by rw [h]; exact g.comm₁.symm)
  · exact h
  · exact h₃ _ _ f.comm₂ (by rw [h]; exact g.comm₂)

private lemma triangle_comparison (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (hM : T.obj₂ = T'.obj₂)
    (h₀ : Subsingleton (T.obj₁ ⟶ T'.obj₃))
    (h₁ : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃))
    (h₀' : Subsingleton (T'.obj₁ ⟶ T.obj₃))
    (_h₁' : Subsingleton (T'.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃))
    (hself : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃))
    (hself' : Subsingleton (T'.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)) :
    ∃! e : T ≅ T', e.hom.hom₂ = eqToHom hM := by
  obtain ⟨f, hf⟩ := (triangle_morphism_extension T T' hT hT' (eqToHom hM)).1.2.2.mp
    (h₀.elim _ _)
  obtain ⟨g, hg⟩ := (triangle_morphism_extension T' T hT' hT (eqToHom hM.symm)).1.2.2.mp
    (h₀'.elim _ _)
  let e : T ≅ T' :=
    { hom := f
      inv := g
      hom_inv_id := triangle_hom_ext_middle T T hT hT hself _ _ (by
        change f.hom₂ ≫ g.hom₂ = 𝟙 _
        simp [hf, hg])
      inv_hom_id := triangle_hom_ext_middle T' T' hT' hT' hself' _ _ (by
        change g.hom₂ ≫ f.hom₂ = 𝟙 _
        simp [hf, hg]) }
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  exact triangle_hom_ext_middle T T' hT hT' h₁ _ _ (he'.trans hf.symm)

end TriangleComparison

namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

private def toUniformPlus : Complex A false ⥤
    UniformFilteredComplexes A none (CochainComplex.plus A) where
  obj K := ⟨K.obj, K.property.1, (fun _ _ h ↦ by cases h), by
    obtain ⟨n, hn⟩ := K.property.2.1
    exact ⟨n, (CochainComplex.isStrictlyGE_iff _ _).2 hn⟩⟩
  map f := ⟨f.hom⟩

private def fromUniformPlus : UniformFilteredComplexes A none (CochainComplex.plus A) ⥤
    Complex A false where
  obj K := ⟨K.obj, K.property.1, by
    obtain ⟨n, hn⟩ := K.property.2.2
    exact ⟨⟨n, fun i hi ↦ (CochainComplex.isStrictlyGE_iff _ _).1 hn i hi⟩, Or.inl rfl⟩⟩
  map f := ⟨f.hom⟩

private noncomputable def uniformPlusEquivalence : Complex A false ≌
    UniformFilteredComplexes A none (CochainComplex.plus A) where
  functor := toUniformPlus A
  inverse := fromUniformPlus A
  unitIso := Iso.refl _
  counitIso := Iso.refl _

private abbrev plusW := uniformFilteredQuasiIso (C := A) none (CochainComplex.plus A)

private noncomputable def plusLocalization := toUniformPlus A ⋙ (plusW A).Q

private instance : (plusLocalization A).IsLocalization (quasiIso (A := A) false) := by
  apply Functor.IsLocalization.of_equivalence_source (plusW A).Q (plusW A)
    (plusLocalization A) (quasiIso false) (uniformPlusEquivalence A).symm
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _ hf
  · intro X Y f hf
    exact Localization.inverts (plusW A).Q (plusW A) _ hf
  · exact Iso.refl _

private noncomputable def derivedPlusEquivalence :=
  Localization.uniq (Q (A := A) false) (plusLocalization A) (quasiIso false)

private noncomputable def intoUnbounded : Derived (A := A) false ⥤ UniformFiltered.Derived A :=
  (derivedPlusEquivalence A).functor ⋙ uniformFilteredComparison none
    (P := CochainComplex.plus A) (R := fun _ ↦ True) (fun _ _ ↦ True.intro)

private noncomputable def intoUnboundedFullyFaithful : (intoUnbounded A).FullyFaithful := by
  let h := (uniformFiltered_bounded_localization_comparison A none).2.1.some
  exact (Functor.FullyFaithful.ofFullyFaithful (derivedPlusEquivalence A).functor).comp h

private noncomputable def complexIntoUnbounded : Complex A false ⥤ UniformFiltered.Complexes A :=
  toUniformPlus A ⋙ uniformFilteredInclusion none (P := CochainComplex.plus A)
    (R := fun _ ↦ True) (fun _ _ ↦ True.intro)

private noncomputable def intoUnboundedFactors :
    Q false ⋙ intoUnbounded A ≅ complexIntoUnbounded A ⋙ UniformFiltered.Q := by
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Localization.compUniqFunctor (Q false) (plusLocalization A) (quasiIso false)) _

private noncomputable def intoUnboundedGrade [UniformFiltered.Model A]
    (D : FilteredTruncationCore A) (p : ℤ) :
    intoUnbounded A ⋙ UniformFiltered.Model.gr p ≅ D.gr p ⋙ DerivedCategory.Plus.ι := by
  apply (Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
    (DerivedCategory A)).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (intoUnboundedFactors A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (complexIntoUnbounded A) (UniformFiltered.Model.grComparison p) ≪≫
    (D.grComparison p).symm

private lemma unbounded_conservative [UniformFiltered.Model A]
    (M : UniformFiltered.Derived A)
    (h : ∀ a : ℤ, IsZero ((UniformFiltered.Model.gr a).obj M)) : IsZero M := by
  let P : ObjectProperty (UniformFiltered.Derived A) := fun X ↦
    ∀ a : ℤ, a ≠ 0 → IsZero ((UniformFiltered.Model.gr a).obj X)
  let F := ObjectProperty.ι P ⋙ UniformFiltered.Model.omega
  let := UniformFiltered.Model.pure_equivalence (C := A) 0
  have hz : IsZero (F.obj ⟨M, fun a _ ↦ h a⟩) :=
    (h 0).of_iso (UniformFiltered.Model.pureComparison 0 M (fun a _ ↦ h a)).symm
  rw [IsZero.iff_id_eq_zero]
  have he : (𝟙 (⟨M, fun a _ ↦ h a⟩ : P.FullSubcategory)) = 0 := by
    apply F.map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact hz.eq_of_src _ _
  exact congrArg (fun f ↦ f.hom) he

private lemma unbounded_orthogonality [UniformFiltered.Model A]
    (p : ℤ) (L R : UniformFiltered.Derived A)
    (hL : ∀ a : ℤ, a < p → IsZero ((UniformFiltered.Model.gr a).obj L))
    (hR : ∀ a : ℤ, p ≤ a → IsZero ((UniformFiltered.Model.gr a).obj R)) :
    Subsingleton (L ⟶ R) := by
  have hz : IsZero ((UniformFiltered.Model.high p).obj R) := by
    apply unbounded_conservative A
    intro a
    by_cases ha : a < p
    · exact UniformFiltered.Model.high_support p a R ha
    · exact (hR a (by omega)).of_iso
        ((UniformFiltered.Model.high_grade p a (by omega)).app R)
  obtain ⟨_, hs⟩ := UniformFiltered.Model.high_hom_bijective p L R hL
  constructor
  intro f g
  obtain ⟨f', rfl⟩ := hs f
  obtain ⟨g', rfl⟩ := hs g
  rw [hz.eq_of_tgt f' g']

/-- Disjoint filtration supports are semiorthogonal, also after a cochain shift.
The bounded-below localization embeds fully faithfully in the uniform unbounded
localization. The graded comparison transports support. In the latter category,
vanishing of all grades implies zero by its pure-grade equivalence. Thus the high
truncation of a low-supported object is zero; its universal Hom bijection gives
orthogonality. Commutation of grading with shifts gives the shifted assertion. -/
private theorem filteredSupportOrthogonality (D : FilteredTruncationCore A)
    (p : ℤ) (L R : Derived (A := A) false)
    (hL : ∀ a : ℤ, a < p → IsZero ((D.gr a).obj L))
    (hR : ∀ a : ℤ, p ≤ a → IsZero ((D.gr a).obj R)) :
    letI := D.model
    Subsingleton (L ⟶ R) ∧ Subsingleton (L⟦(1 : ℤ)⟧ ⟶ R) := by
  let := D.model
  obtain ⟨U⟩ := UniformFiltered.unbounded_truncation A
  let := U
  have transfer (X Y : Derived (A := A) false)
      (hX : ∀ a : ℤ, a < p → IsZero ((D.gr a).obj X))
      (hY : ∀ a : ℤ, p ≤ a → IsZero ((D.gr a).obj Y)) : Subsingleton (X ⟶ Y) := by
    have hXu : ∀ a : ℤ, a < p →
        IsZero ((UniformFiltered.Model.gr a).obj ((intoUnbounded A).obj X)) := by
      intro a ha
      exact ((DerivedCategory.Plus.ι (C := A)).map_isZero (hX a ha)).of_iso
        ((intoUnboundedGrade A D a).app X)
    have hYu : ∀ a : ℤ, p ≤ a →
        IsZero ((UniformFiltered.Model.gr a).obj ((intoUnbounded A).obj Y)) := by
      intro a ha
      exact ((DerivedCategory.Plus.ι (C := A)).map_isZero (hY a ha)).of_iso
        ((intoUnboundedGrade A D a).app Y)
    have hs := unbounded_orthogonality A p _ _ hXu hYu
    exact ⟨fun f g ↦ (intoUnboundedFullyFaithful A).map_injective (hs.elim _ _)⟩
  refine ⟨transfer L R hL hR, transfer _ R ?_ hR⟩
  intro a ha
  exact ((CategoryTheory.shiftFunctor (DerivedCategory.Plus A) (1 : ℤ)).map_isZero
    (hL a ha)).of_iso (((D.gr a).commShiftIso (1 : ℤ)).app L)

private noncomputable def intoUnboundedOmega [UniformFiltered.Model A]
    (D : FilteredTruncationCore A) :
    intoUnbounded A ⋙ UniformFiltered.Model.omega ≅ D.omega ⋙ DerivedCategory.Plus.ι := by
  apply (Localization.fullyFaithfulWhiskeringLeft (Q false) (quasiIso false)
    (DerivedCategory A)).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (intoUnboundedFactors A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (complexIntoUnbounded A) UniformFiltered.Model.omegaComparison ≪≫
    D.omegaComparison.symm

private def pure (D : FilteredTruncationCore A) (p : ℤ) :
    ObjectProperty (Derived (A := A) false) := fun M ↦
  ∀ a : ℤ, a ≠ p → IsZero ((D.gr a).obj M)

private def unboundedPure [UniformFiltered.Model A] (p : ℤ) :
    ObjectProperty (UniformFiltered.Derived A) := fun M ↦
  ∀ a : ℤ, a ≠ p → IsZero ((UniformFiltered.Model.gr a).obj M)

private noncomputable def intoPure [UniformFiltered.Model A]
    (D : FilteredTruncationCore A) (p : ℤ) :
    (pure A D p).FullSubcategory ⥤ (unboundedPure A p).FullSubcategory where
  obj M := ⟨(intoUnbounded A).obj M.obj, fun a ha ↦
    ((DerivedCategory.Plus.ι (C := A)).map_isZero (M.property a ha)).of_iso
      ((intoUnboundedGrade A D a).app M.obj)⟩
  map f := ⟨(intoUnbounded A).map f.hom⟩

private noncomputable def intoPureFullyFaithful [UniformFiltered.Model A]
    (D : FilteredTruncationCore A) (p : ℤ) : (intoPure A D p).FullyFaithful where
  preimage f := ⟨(intoUnboundedFullyFaithful A).preimage f.hom⟩
  map_preimage f := by
    ext
    exact (intoUnboundedFullyFaithful A).map_preimage f.hom
  preimage_map f := by
    ext
    exact (intoUnboundedFullyFaithful A).preimage_map f.hom

private lemma pure_omega_fullyFaithful [UniformFiltered.Model A]
    (D : FilteredTruncationCore A) (p : ℤ) :
    Nonempty ((ObjectProperty.ι (pure A D p) ⋙ D.omega).FullyFaithful) := by
  let H := ObjectProperty.ι (unboundedPure A p) ⋙ UniformFiltered.Model.omega
  let : H.IsEquivalence := UniformFiltered.Model.pure_equivalence (C := A) p
  have h := (intoPureFullyFaithful A D p).comp (Functor.FullyFaithful.ofFullyFaithful H)
  have e : intoPure A D p ⋙ H ≅
      (ObjectProperty.ι (pure A D p) ⋙ D.omega) ⋙ DerivedCategory.Plus.ι :=
    Functor.isoWhiskerLeft (ObjectProperty.ι (pure A D p)) (intoUnboundedOmega A D)
  exact ⟨Functor.FullyFaithful.ofCompFaithful (h.ofIso e)⟩

/-- Forgetting filtration is an equivalence on the full pure-grade subcategory.
The fully faithful bounded-below comparison identifies the pure subcategories.
Full faithfulness of forgetting follows from the unbounded pure-grade equivalence.
For essential surjectivity, choose its pure preimage of an ordinary bounded-below
object. The surviving grade is isomorphic to that object, so all graded homologies
have a common lower bound. The essential-image theorem for the bounded-below
comparison supplies a filtered bounded-below preimage. Full faithfulness of the
ordinary bounded-below inclusion descends its underlying comparison isomorphism. -/
private theorem filteredPureGradeEquivalence (D : FilteredTruncationCore A) (p : ℤ) :
    (ObjectProperty.ι (fun M : Derived (A := A) false ↦
      ∀ a : ℤ, a ≠ p → IsZero ((D.gr a).obj M)) ⋙ D.omega).IsEquivalence := by
  obtain ⟨U⟩ := UniformFiltered.unbounded_truncation A
  let := U
  obtain ⟨hF⟩ := pure_omega_fullyFaithful A D p
  let := hF.full
  let := hF.faithful
  have hess : (ObjectProperty.ι (pure A D p) ⋙ D.omega).EssSurj := by
    constructor
    intro K
    let G := ObjectProperty.ι (unboundedPure A p) ⋙ UniformFiltered.Model.omega
    let : G.IsEquivalence := UniformFiltered.Model.pure_equivalence (C := A) p
    let M := G.objPreimage ((DerivedCategory.Plus.ι (C := A)).obj K)
    let e := G.objObjPreimageIso ((DerivedCategory.Plus.ι (C := A)).obj K)
    obtain ⟨c, hc⟩ := K.property
    let : K.obj.IsGE c := hc
    let J := UniformFiltered.Q.objPreimage M.obj
    let eJ := UniformFiltered.Q.objObjPreimageIso M.obj
    have hsupport : uniformLocalizedSupport none (Set.Ici c) M.obj := by
      refine ⟨J, ⟨eJ⟩, ?_⟩
      intro a n hn
      have hz : IsZero ((DerivedCategory.homologyFunctor A n).obj
          ((UniformFiltered.Model.gr a).obj M.obj)) := by
        by_cases ha : a = p
        · subst a
          exact (DerivedCategory.isZero_of_isGE K.obj c n (by simpa using hn)).of_iso
            ((DerivedCategory.homologyFunctor A n).mapIso
              (UniformFiltered.Model.pureComparison p M.obj M.property ≪≫ e))
        · exact (DerivedCategory.homologyFunctor A n).map_isZero (M.property a ha)
      exact hz.of_iso
        ((DerivedCategory.homologyFunctorFactors A n).symm.app
            ((UniformFiltered.evaluation (some a)).obj J) ≪≫
          (DerivedCategory.homologyFunctor A n).mapIso
            ((UniformFiltered.Model.grComparison a).app J).symm ≪≫
          (DerivedCategory.homologyFunctor A n).mapIso
            ((UniformFiltered.Model.gr a).mapIso eJ))
    have himage := ((uniformFiltered_bounded_localization_comparison A none).2.2.2.2.2.2.1
      M.obj).2 ⟨c, hsupport⟩
    obtain ⟨N, ⟨eN⟩⟩ := himage
    let X := (derivedPlusEquivalence A).inverse.obj N
    let eX : (intoUnbounded A).obj X ≅ M.obj :=
      (uniformFilteredComparison none (P := CochainComplex.plus A)
        (R := fun _ ↦ True) (fun _ _ ↦ True.intro)).mapIso
          ((derivedPlusEquivalence A).counitIso.app N) ≪≫ eN
    have hX : pure A D p X := by
      intro a ha
      apply IsZero.of_full_of_faithful_of_isZero (DerivedCategory.Plus.ι (C := A))
      exact (M.property a ha).of_iso
        (((intoUnboundedGrade A D a).app X).symm ≪≫
          (UniformFiltered.Model.gr a).mapIso eX)
    refine ⟨⟨X, hX⟩, ⟨(DerivedCategory.Plus.ι (C := A)).preimageIso ?_⟩⟩
    exact ((intoUnboundedOmega A D).app X).symm ≪≫
      UniformFiltered.Model.omega.mapIso eX ≪≫ e
  exact { faithful := hF.faithful, full := hF.full, essSurj := hess }

/-- Universal filtration truncations and their distinguished triangles.
Source: Varshavsky--Lefschetz--Verdier trace formula, §§5.1.1--5.1.2,
pp. 39--40 (blueprint: lem-trf-filtered-truncation-triangle).

Starting with the normalized cone and truncation construction, embed the
bounded-below localization fully faithfully into the unbounded uniform filtered
localization. Its universal high-truncation Hom bijection gives semiorthogonality.
Triangle morphism extension then proves the two Hom bijections and uniqueness of
supported triangles. Finally restrict the unbounded pure-grade equivalence using
the essential-image description by a common lower bound on graded cohomology. -/
theorem filteredTruncationTriangle : Nonempty (FilteredTruncationData A) := by
  classical
  obtain ⟨D⟩ := filteredTruncationCore A
  let := D.model
  let pure (p : ℤ) : ObjectProperty (Derived (A := A) false) :=
    fun M ↦ ∀ a : ℤ, a ≠ p → IsZero ((D.gr a).obj M)
  let F (p : ℤ) := ObjectProperty.ι (pure p) ⋙ D.omega
  have hF (p : ℤ) : (F p).IsEquivalence := filteredPureGradeEquivalence A D p
  let E (p : ℤ) := (F p).asEquivalence
  refine ⟨{
    model := D.model
    omega := D.omega
    omegaComparison := D.omegaComparison
    gr := D.gr
    grComparison := D.grComparison
    high := D.high
    low := D.low
    inclusion := D.inclusion
    quotient := D.quotient
    connecting := D.connecting
    distinguished := D.distinguished
    high_support := D.high_support
    low_support := D.low_support
    unique_triangle := ?_
    high_hom_bijective := ?_
    low_hom_bijective := ?_
    high_hom_natural := ?_
    low_hom_natural := ?_
    high_comparison := D.high_comparison
    low_comparison := D.low_comparison
    high_normalization := D.high_normalization
    low_normalization := D.low_normalization
    grade_truncation := D.grade_truncation
    grade_normalization := D.grade_normalization
    pure := pure
    pure_iff := fun _ _ ↦ Iff.rfl
    place := fun p ↦ (E p).inverse
    place_equivalence := fun p ↦ (E p).symm.isEquivalence_functor
    place_forget := fun p ↦ (Functor.associator _ _ _).symm ≪≫ (E p).counitIso
    place_grade := fun p a K ha ↦ ((E p).inverse.obj K).property a ha }⟩
  · intro p M L R i q d hT hL hR
    exact triangle_comparison _ _ (D.distinguished p M) hT rfl
      (filteredSupportOrthogonality A D p _ _ (D.high_support p · M) hR).1
      (filteredSupportOrthogonality A D p _ _ (D.high_support p · M) hR).2
      (filteredSupportOrthogonality A D p _ _ hL (D.low_support p · M)).1
      (filteredSupportOrthogonality A D p _ _ hL (D.low_support p · M)).2
      (filteredSupportOrthogonality A D p _ _
        (D.high_support p · M) (D.low_support p · M)).2
      (filteredSupportOrthogonality A D p _ _ hL hR).2
  · intro p L M hL
    let T := Triangle.mk ((D.inclusion p).app M) ((D.quotient p).app M)
      ((D.connecting p).app M)
    let S := contractibleTriangle L
    have hS := contractible_distinguished L
    have hT := D.distinguished p M
    obtain ⟨hz, hs⟩ := filteredSupportOrthogonality A D p L _ hL (D.low_support p · M)
    constructor
    · intro f g h
      exact ((triangle_morphism_extension S T hS hT (f ≫ (D.inclusion p).app M)).2.1
        hs).1 f g (by simp [S, T]) (by simpa [S, T] using h.symm)
    · intro g
      obtain ⟨f, hf⟩ := (triangle_morphism_extension S T hS hT g).1.1.mp (hz.elim _ _)
      exact ⟨f, by simpa [S, T, Category.id_comp, Category.comp_id] using hf⟩
  · intro p M R hR
    let T := Triangle.mk ((D.inclusion p).app M) ((D.quotient p).app M)
      ((D.connecting p).app M)
    let S := Triangle.mk (0 : (0 : Derived (A := A) false) ⟶ R) (𝟙 R) 0
    have hS := contractible_distinguished₁ R
    have hT := D.distinguished p M
    obtain ⟨hz, hs⟩ := filteredSupportOrthogonality A D p _ R (D.high_support p · M) hR
    constructor
    · intro f g h
      exact ((triangle_morphism_extension T S hT hS ((D.quotient p).app M ≫ f)).2.1
        hs).2.1 f g (by simp [S, T]) (by simpa [S, T] using h.symm)
    · intro g
      obtain ⟨f, hf⟩ := (triangle_morphism_extension T S hT hS g).1.2.1.mp (hz.elim _ _)
      exact ⟨f, by simpa [S, T, Category.id_comp, Category.comp_id] using hf⟩
  · intro p L L' M M' f g h
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun k ↦ f ≫ h ≫ k) ((D.inclusion p).naturality g)
  · intro p M M' R R' f g h
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ h ≫ g) ((D.quotient p).naturality f).symm

end CochainComplex.FiniteFiltered
