/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q81, J7
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGluing
import Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable
import Sheaf.AlgebraicGeometry.EtaleQuotientAffineOpenCover
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient
import Sheaf.AlgebraicGeometry.EtalePullbackRelationPresheaf
import Sheaf.AlgebraicGeometry.RepresentableEtaleQuotientPresentation
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Quotients of étale equivalence relations

Source: Stacks Project, Spaces, Tags 02WW and 02WV, with the quotient universal
property and presentation kernel-pair identity (blueprint: lem-trf-etale-relation-quotient).

The presheaf coequalizer of the two Yoneda maps is the pointwise quotient presheaf.
Its sheafification is specified by its universal property at this presheaf, without
assuming existence of sheafification for every small-valued presheaf on the big site.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical quotient map is the presheaf coequalizer projection followed by the
sheafification unit `η`. Source: Stacks, Spaces, quotient preceding Tag 02WW
(blueprint: lem-trf-etale-relation-quotient). -/
noncomputable def relationQuotientMap {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj) : yoneda.obj V ⟶ F.obj :=
  coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η
/-- Sheafify a subpresheaf inside an existing sheaf, without a global sheafification
instance. This is Mathlib’s subsheaf closure construction. -/
private theorem reflection_of_mono {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P : Cᵒᵖ ⥤ Type w} (F : Sheaf J (Type w))
    (f : P ⟶ F.obj) [Mono f] :
    ∃ (H : Sheaf J (Type w)) (η : P ⟶ H.obj),
      ∀ G : Sheaf J (Type w), Function.Bijective (fun g : H.obj ⟶ G.obj ↦ η ≫ g) := by
  let K := Subfunctor.range f
  let H : Sheaf J (Type w) := ⟨(K.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2
      (K.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1 F.property))⟩
  refine ⟨H, Subfunctor.toRangeSheafify J f, fun G ↦ ⟨?_, ?_⟩⟩
  · intro g h e
    apply K.to_sheafify_lift_unique ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)
    apply (cancel_epi (Subfunctor.toRange f)).1
    exact e
  · intro g
    refine ⟨K.sheafifyLift (inv (Subfunctor.toRange f) ≫ g)
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.property), ?_⟩
    dsimp [Subfunctor.toRangeSheafify]
    rw [Category.assoc, Subfunctor.to_sheafifyLift, IsIso.hom_inv_id_assoc]

/-- A relation that is already the kernel pair makes the quotient unit injective. -/
private theorem quotient_unit_mono {C : Type u} [Category.{v} C]
    [HasBinaryProducts C] {R V : C} (s t : R ⟶ V)
    {F : Cᵒᵖ ⥤ Type v}
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F)
    (h : IsPullback (yoneda.map s) (yoneda.map t)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) : Mono η := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro T
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y e
  obtain ⟨a, rfl⟩ := (CategoryTheory.epi_iff_surjective
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app T)).1 inferInstance x
  obtain ⟨b, rfl⟩ := (CategoryTheory.epi_iff_surjective
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app T)).1 inferInstance y
  obtain ⟨r, hr, ht⟩ := Types.exists_of_isPullback (h.app T) a b e
  have he := ConcreteCategory.congr_hom
    (congr_app (coequalizer.condition (yoneda.map s) (yoneda.map t)) T) r
  change (coequalizer.π (yoneda.map s) (yoneda.map t)).app T (r ≫ s) =
    (coequalizer.π (yoneda.map s) (yoneda.map t)).app T (r ≫ t) at he
  change r ≫ s = a at hr
  change r ≫ t = b at ht
  simpa only [hr, ht] using he

/-- Restricted quotient presheaves embed in the original quotient and hence admit
sheafification inside its sheaf. Source: Stacks, Groupoids, Tag 045Z. -/
private theorem restricted_reflection {S : Scheme.{u}} {R V W : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (g : W ⟶ V) [Etale s.left] [Etale t.left] [Etale g.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj) [Mono η] :
    ∃ (H : Sheaf (Scheme.fppfTopology.over S) (Type u))
      (ηH : coequalizer (yoneda.map (restrictedEtaleRelationSource s t g))
        (yoneda.map (restrictedEtaleRelationTarget s t g)) ⟶ H.obj),
      ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
        Function.Bijective (fun k : H.obj ⟶ G.obj ↦ ηH ≫ k) := by
  obtain ⟨s', t', r', hs, ht, _, _, _, _, _, _, _, _, _, _, _, _, v, _, hv, _⟩ :=
    etale_pullback_relation_presheaf s t hrel g
  subst s'
  subst t'
  have : Mono v := (NatTrans.mono_iff_mono_app _).2 (fun T ↦
    (CategoryTheory.mono_iff_injective _).2 (hv T.unop))
  exact reflection_of_mono _ F (v ≫ η)
/-- Convert the scheme-test presentation theorem into the representable-map predicates
and the covering-sieve formulation of local lifts. Source: Stacks, Spaces, Tag 02WV. -/
private theorem presentation_properties {S : Scheme.{u}} {R V : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g))
    (hrep : IsRepresentable (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) :
    IsEtale (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      IsSurjective (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      (∀ (T : Over S) (x : F.obj.obj (op T)),
        ∃ C : Sieve T, C ∈ (Scheme.etaleTopology.over S) T ∧
          ∀ (U : Over S) (f : U ⟶ T), C f →
            ∃ a : U ⟶ V,
              (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).app (op U) a =
                F.obj.map f.op x) := by
  have htest (T : Over S) (a : yoneda.obj T ⟶ F.obj) := hrep T a
  have hboth : ∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj),
      ∃ (P : Over S) (p : P ⟶ T) (b : yoneda.obj P ⟶ yoneda.obj V),
        IsPullback b (yoneda.map p)
          (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) a ∧
        Etale p.left ∧ Surjective p.left := by
    intro T a
    obtain ⟨P, p, b, hp, _⟩ := htest T a
    have hh := (Scheme.representable_etale_quotient_presentation s t hrel F η hη hrep
      T (yonedaEquiv a)).1 P p (yonedaEquiv b)
    simp only [Equiv.symm_apply_apply] at hh
    rw [show yoneda.map (yonedaEquiv b) = b from
      yonedaEquiv.injective (yonedaEquiv_yoneda_map _)] at hh
    exact ⟨P, p, b, hp, (hh hp).1, (hh hp).2.1⟩
  refine ⟨fun T a ↦ ?_, fun T a ↦ ?_, ?_⟩
  · obtain ⟨P, p, b, hp, he, _⟩ := hboth T a
    exact ⟨P, p, b, hp, he⟩
  · obtain ⟨P, p, b, hp, _, hs⟩ := hboth T a
    exact ⟨P, p, b, hp, hs⟩
  · intro T x
    have : Scheme.etalePrecoverage.IsStableUnderBaseChange :=
      inferInstanceAs (Scheme.precoverage @Etale).IsStableUnderBaseChange
    obtain ⟨I, E, g, b, hg, hb⟩ :=
      (Scheme.representable_etale_quotient_presentation s t hrel F η hη hrep T x).2
    refine ⟨Sieve.generate (Presieve.ofArrows E g), ?_, ?_⟩
    · rw [show Scheme.etaleTopology =
          (Scheme.etalePrecoverage.toGrothendieck) from rfl,
        over_toGrothendieck_eq_toGrothendieck_comap_forget]
      apply Precoverage.generate_mem_toGrothendieck
      rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
      exact hg
    · rintro U f ⟨W, k, _, ⟨i⟩, rfl⟩
      refine ⟨k ≫ b i, ?_⟩
      have hn := ConcreteCategory.congr_hom
        ((coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).naturality k.op) (b i)
      change (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).app (op U)
        (k ≫ b i) = F.obj.map k.op
          ((coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).app (op (E i)) (b i)) at hn
      rw [hn, hb i]
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
/-- Pull the diagonal back along the pair of scheme tests on their product.
Source: Stacks, Spaces, the representable-diagonal criterion following Tag 02WW. -/
private theorem representable_of_diagonal {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hdiag : IsRepresentable (prod.lift (𝟙 F) (𝟙 F)))
    (V : Over S) (q : yoneda.obj V ⟶ F) : IsRepresentable q := by
  intro T a
  let z : yoneda.obj (T ⨯ V) ⟶ F ⨯ F :=
    prod.lift (yoneda.map prod.fst ≫ a) (yoneda.map prod.snd ≫ q)
  obtain ⟨U, p, k, hp, _⟩ := hdiag (T ⨯ V) z
  refine ⟨U, p ≫ prod.fst, yoneda.map (p ≫ prod.snd), ?_, trivial⟩
  have hw₁ : yoneda.map p ≫ yoneda.map prod.fst ≫ a = k := by
    have he := hp.w =≫ prod.fst
    simpa only [Category.assoc, prod.lift_fst, Category.comp_id, z] using he.symm
  have hw₂ : yoneda.map p ≫ yoneda.map prod.snd ≫ q = k := by
    have he := hp.w =≫ prod.snd
    simpa only [Category.assoc, prod.lift_snd, Category.comp_id, z] using he.symm
  apply IsPullback.of_forall_isPullback_app
  intro W
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · exact congr_app (by simpa only [Functor.map_comp, Category.assoc] using
      (hw₂.trans hw₁.symm)) W
  · intro x y hxy
    have hpx : x ≫ p = y ≫ p := prod.hom_ext hxy.2 hxy.1
    have hk : k.app W x = k.app W y := by
      rw [← hw₁]
      change a.app W ((x ≫ p) ≫ prod.fst) = a.app W ((y ≫ p) ≫ prod.fst)
      rw [hpx]
    exact Types.ext_of_isPullback (hp.app W) hk hpx
  · intro b c hbc
    let d : W.unop ⟶ T ⨯ V := prod.lift c b
    have hm : yonedaEquiv.symm (q.app W b) ≫ prod.lift (𝟙 F) (𝟙 F) =
        yoneda.map d ≫ z := by
      apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst, Category.comp_id, z]
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
        change q.app W b = a.app W (prod.lift c b ≫ prod.fst)
        simpa only [prod.lift_fst] using hbc
      · simp only [Category.assoc, prod.lift_snd, Category.comp_id, z]
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
        change q.app W b = q.app W (prod.lift c b ≫ prod.snd)
        rw [prod.lift_snd]
    have he : (prod.lift (𝟙 F) (𝟙 F)).app W (q.app W b) = z.app W d := by
      simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
        using congrArg yonedaEquiv hm
    obtain ⟨r, hr, hpr⟩ := Types.exists_of_isPullback (hp.app W) (q.app W b) d he
    refine ⟨r, ?_, ?_⟩
    · change r ≫ p ≫ prod.snd = b
      change r ≫ p = d at hpr
      rw [← Category.assoc, hpr]
      exact prod.lift_snd _ _
    · change r ≫ p ≫ prod.fst = c
      change r ≫ p = d at hpr
      rw [← Category.assoc, hpr]
      exact prod.lift_fst _ _
/-- A representable open immersion is injective, tested against the section itself. -/
private theorem mono_of_open {S : Scheme.{u}} {G F : (Over S)ᵒᵖ ⥤ Type u}
    (f : G ⟶ F)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) f) : Mono f := by
  apply (NatTrans.mono_iff_mono_app _).2
  rintro ⟨T⟩
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y e
  obtain ⟨U, p, q, hp, hO⟩ := hf T (yonedaEquiv.symm (f.app (op T) x))
  have : IsOpenImmersion p.left := hO
  have : Mono p.left := inferInstance
  have : Mono p := Over.mono_of_mono_left p
  have hpb := hp.app (op T)
  have hx : f.app (op T) x = (yonedaEquiv.symm (f.app (op T) x)).app (op T) (𝟙 T) := by
    simp
  obtain ⟨a, ha, hpa⟩ := Types.exists_of_isPullback hpb x (𝟙 T) hx
  obtain ⟨b, hb, hpb⟩ := Types.exists_of_isPullback hpb y (𝟙 T) (e.symm.trans hx)
  have hab : a = b := (cancel_mono p).1 (hpa.trans hpb.symm)
  exact ha.symm.trans (hab ▸ hb)

/-- An étale equivalence relation has an algebraic-space quotient, with an étale
surjective quotient map, the given relation as kernel pair, étale-local lifts of every
section, and the universal property for maps to any fppf sheaf. The hypothesis `hη`
is exactly the universal property of the sheafification unit of the quotient presheaf;
`∃!` in the last clause is the bijection onto the maps equalizing `s` and `t`.
Source: Stacks, Spaces, Tags 02WW and 02WV
(blueprint: lem-trf-etale-relation-quotient).

Proof:
1. The kernel-pair lemma makes the quotient-presheaf unit injective. A restricted
   quotient presheaf embeds in it, by the pullback-relation lemma. Sheafify its image
   inside `F` using Mathlib’s subsheaf closure and its universal property. This
   constructs the coproduct-relation and chart-relation quotient sheaves in `Type u`.
2. Apply the affine quotient open-cover lemma to the standard affine open covering.
   For each chart, affine representability and the representable quotient presentation
   theorem supply a representable diagonal and a surjective étale atlas.
3. Form the sheaf coproduct using the coproduct-partition theorem. The chart maps to
   `F` are monic representable open immersions; their local covering property makes
   the coproduct map epi by sheaf separation. The algebraic-space coproduct and
   open-gluing theorems now show that `F` is an algebraic space.
4. Pull the representable diagonal back along a pair of scheme tests on their product
   to represent every base change of the quotient map. The representable quotient
   presentation theorem then gives étaleness, surjectivity, and étale-local lifts;
   pass from its covering family to the generated sieve on the over-site.
5. The kernel-pair lemma gives the asserted cartesian square. The coequalizer
   universal property followed by `hη` gives existence and uniqueness of the final
   factorization. -/
theorem etale_relation_quotient {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    IsAlgebraicSpace F ∧
    IsEtale (relationQuotientMap s t F η) ∧
    IsSurjective (relationQuotientMap s t F η) ∧
    IsPullback (yoneda.map s) (yoneda.map t)
      (relationQuotientMap s t F η) (relationQuotientMap s t F η) ∧
    (∀ (T : Over S) (x : F.obj.obj (op T)),
      ∃ C : Sieve T, C ∈ (Scheme.etaleTopology.over S) T ∧
        ∀ (U : Over S) (f : U ⟶ T), C f →
          ∃ a : U ⟶ V,
            (relationQuotientMap s t F η).app (op U) a = F.obj.map f.op x) ∧
    (∀ (G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (f : yoneda.obj V ⟶ G.obj),
      yoneda.map s ≫ f = yoneda.map t ≫ f →
        ∃! g : F.obj ⟶ G.obj, relationQuotientMap s t F η ≫ g = f) := by
  classical
  have hker := Scheme.etale_relation_kernel_pair s t hrel F η hη
  have : Mono η := quotient_unit_mono s t η hker
  let 𝒰 := V.left.affineCover
  have hcover := etale_quotient_affine_open_cover s t hrel 𝒰 F η hη
  obtain ⟨hincl, hgS, hgE, hm, hr, hs, ht, hi, hcharts⟩ := hcover
  have : Etale (AffineQuotientCover.map V 𝒰).left := hgE
  obtain ⟨Q, ηQ, hηQ⟩ := restricted_reflection s t hrel
    (AffineQuotientCover.map V 𝒰) F η
  have : Mono (prod.lift (AffineQuotientCover.source s t 𝒰)
      (AffineQuotientCover.target s t 𝒰)) := hm
  have : Etale (AffineQuotientCover.source s t 𝒰).left := hs
  have : Etale (AffineQuotientCover.target s t 𝒰).left := ht
  have hkerQ := Scheme.etale_relation_kernel_pair
    (AffineQuotientCover.source s t 𝒰) (AffineQuotientCover.target s t 𝒰) hr Q ηQ hηQ
  have : Mono ηQ := quotient_unit_mono _ _ ηQ hkerQ
  have hFi : ∀ i : 𝒰.I₀,
      ∃ (H : Sheaf (Scheme.fppfTopology.over S) (Type u))
        (ηH : coequalizer (yoneda.map (AffineQuotientCover.chartSource s t 𝒰 i))
          (yoneda.map (AffineQuotientCover.chartTarget s t 𝒰 i)) ⟶ H.obj),
        ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
          Function.Bijective (fun k : H.obj ⟶ G.obj ↦ ηH ≫ k) := by
    intro i
    have : IsOpenImmersion (AffineQuotientCover.inclusion V 𝒰 i).left := (hincl i).1
    exact restricted_reflection _ _ hr (AffineQuotientCover.inclusion V 𝒰 i) Q ηQ
  choose Fi ηi hηi using hFi
  obtain ⟨β, α, hβ, hβq, hα, hlocal⟩ := hcharts Q ηQ hηQ Fi ηi hηi
  have hpi (i : 𝒰.I₀) :
      IsRepresentable (coequalizer.π
        (yoneda.map (AffineQuotientCover.chartSource s t 𝒰 i))
        (yoneda.map (AffineQuotientCover.chartTarget s t 𝒰 i)) ≫ ηi i) ∧
      IsRepresentable (prod.lift (𝟙 (Fi i).obj) (𝟙 (Fi i).obj)) := by
    have : Mono (prod.lift (AffineQuotientCover.chartSource s t 𝒰 i)
      (AffineQuotientCover.chartTarget s t 𝒰 i)) := (hi i).1
    have : Etale (AffineQuotientCover.chartSource s t 𝒰 i).left := (hi i).2.2.1
    have : Etale (AffineQuotientCover.chartTarget s t 𝒰 i).left := (hi i).2.2.2
    have : IsAffine (AffineQuotientCover.chart V 𝒰 i).left :=
      inferInstanceAs (IsAffine (V.left.affineCover.X i))
    exact etale_affine_quotient_representable _ _ (hi i).2.1 (Fi i) (ηi i) (hηi i)
  have hpres (i : 𝒰.I₀) := by
    have : Mono (prod.lift (AffineQuotientCover.chartSource s t 𝒰 i)
      (AffineQuotientCover.chartTarget s t 𝒰 i)) := (hi i).1
    have : Etale (AffineQuotientCover.chartSource s t 𝒰 i).left := (hi i).2.2.1
    have : Etale (AffineQuotientCover.chartTarget s t 𝒰 i).left := (hi i).2.2.2
    exact presentation_properties _ _ (hi i).2.1 (Fi i) (ηi i) (hηi i) (hpi i).1
  let Xi : 𝒰.I₀ → AlgebraicSpace S := fun i ↦
    ⟨Fi i, (hpi i).2, AffineQuotientCover.chart V 𝒰 i,
      coequalizer.π _ _ ≫ ηi i, (hpres i).1, (hpres i).2.1⟩
  obtain ⟨H, j, ⟨hj⟩⟩ := (Scheme.fppfSheaf_coproduct_partition Fi).1
  let ι : ∀ i, Fi i ⟶ F := fun i ↦ ⟨α i ≫ β⟩
  let q : H ⟶ F := hj.desc (Cofan.mk F ι)
  have hfac : ∀ i, j i ≫ q = ι i := fun i ↦ Cofan.IsColimit.fac hj ι i
  have hopen : ∀ i, IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left) (ι i).hom := fun i ↦ (hα i).2
  have hmono : ∀ i, Mono (ι i) := by
    intro i
    have : Mono (ι i).hom := mono_of_open _ (hopen i)
    exact (sheafToPresheaf _ _).mono_of_mono_map (show Mono (ι i).hom from inferInstance)
  have hq : Epi q := by
    have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) q.hom := by
      constructor
      intro T x
      obtain ⟨C, hC, hloc⟩ := hlocal T x
      have hcov : Sieve.generate C ∈ (Scheme.fppfTopology.over S) T := by
        rw [Scheme.fppfTopology,
          over_toGrothendieck_eq_toGrothendieck_comap_forget Scheme.fppfPrecoverage]
        exact Precoverage.generate_mem_toGrothendieck hC
      apply (Scheme.fppfTopology.over S).superset_covering _ hcov
      apply (Sieve.generate_le_iff _ _).2
      intro W f hf
      obtain ⟨i, y, hy⟩ := hloc W f hf
      refine ⟨(j i).hom.app (op W) y, ?_⟩
      have he := ConcreteCategory.congr_hom (congr_app
        ((sheafToPresheaf _ _).congr_map (hfac i)) (op W)) y
      exact he.trans hy
    exact Sheaf.epi_of_isLocallySurjective' q
  have hcop : IsAlgebraicSpace H := algebraicSpace_coproduct 𝒰.I₀ Xi
    (AffineQuotientCover.chart V 𝒰) (fun i ↦ coequalizer.π _ _ ≫ ηi i)
    (fun i ↦ ⟨(hpres i).1, (hpres i).2.1⟩)
    (AffineQuotientCover.coproduct V 𝒰) (AffineQuotientCover.inclusion V 𝒰)
    ⟨coproductIsCoproduct _⟩ H j hj
  have hF := algebraicSpace_of_open_gluing F 𝒰.I₀ Fi H j hj ι q hfac hmono
    (fun i ↦ (Xi i).property) hopen hq hcop
  have hrep := representable_of_diagonal hF.1 V (relationQuotientMap s t F η)
  obtain ⟨he, hsurj, hlift⟩ := presentation_properties s t hrel F η hη hrep
  refine ⟨hF, he, hsurj, hker, hlift, ?_⟩
  intro G f hf
  obtain ⟨g, hg⟩ := (hη G).2 (coequalizer.desc f hf)
  change η ≫ g = coequalizer.desc f hf at hg
  have hgf : relationQuotientMap s t F η ≫ g = f := by
    simp only [relationQuotientMap, Category.assoc, hg, coequalizer.π_desc]
  refine ⟨g, hgf, ?_⟩
  · intro g' hg'
    apply (hη G).1
    apply coequalizer.hom_ext
    exact hg'.trans hgf.symm

end AlgebraicGeometry.AlgebraicSpace
