/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.TraceFormula.SectionProjModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
import Sheaf.TraceFormula.SectionProjModelPresentation
import Sheaf.TraceFormula.SectionProjModelComparison
import Sheaf.TraceFormula.SpaceLineProjEtaleDescent
import Sheaf.TraceFormula.EtaleLinePresentationSchemeRestriction
import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Descending the canonical section-algebra Proj embedding

Source: Stacks Project, Descent on Spaces, Tag 0D3C, proof of
`lemma-descending-property-ample`, section algebra through the open-immersion descent;
Divisors on Spaces, Tag 0D2Z; Constructions, Tag 01O9
(blueprint: lem-trf-section-proj-etale-embedding).

The adapter below identifies the affine presentation used by relative Proj with the
actual homogeneous section sheaves. Its evaluation is fixed on every homogeneous
section, rather than supplied as an unconstrained graded map. The theorem works with
any presentations of the local canonical objects and returns the normalized comparisons
to those very objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

private theorem representableWith_relative_iff
    (P : MorphismProperty (Over S)) [P.RespectsIso]
    {G F : (Over S)ᵒᵖ ⥤ Type u} (a : G ⟶ F) :
    IsRepresentableWith P a ↔ P.relative yoneda a := by
  constructor
  · intro h
    apply MorphismProperty.relative.of_exists
    intro T b
    obtain ⟨U, p, q, hq, hp⟩ := h T b
    exact ⟨U, q, p, hq, hp⟩
  · intro h T b
    exact ⟨h.rep.pullback b, h.rep.snd b, h.rep.fst b,
      h.rep.isPullback b, h.property_snd b⟩

private theorem isEtale_of_cartesian_scheme
    {F : (Over S)ᵒᵖ ⥤ Type u} {T T' U : Over S}
    {f : F ⟶ yoneda.obj T} {g : T' ⟶ T} {k : yoneda.obj U ⟶ F} {f' : U ⟶ T'}
    (h : IsPullback k (yoneda.map f') f (yoneda.map g)) (hg : Etale g.left) :
    IsEtale k := by
  let E : MorphismProperty (Over S) := MorphismProperty.inverseImage @Etale (Over.forget S)
  have : E.IsStableUnderBaseChange :=
    ⟨fun h hp ↦ MorphismProperty.of_isPullback (P := @Etale)
      (h.map (Over.forget S)) hp⟩
  have := MorphismProperty.relative_isStableUnderBaseChange E (F := yoneda)
  apply (representableWith_relative_iff E k).2
  exact (E.relative yoneda).of_isPullback h.flip (MorphismProperty.relative_map hg)

private theorem isEtale_of_iso {F G : (Over S)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) : IsEtale e.hom := by
  let E : MorphismProperty (Over S) := MorphismProperty.inverseImage @Etale (Over.forget S)
  exact (representableWith_relative_iff E e.hom).2 ((E.relative yoneda).of_isIso e.hom)

private theorem lineTestFamily_restriction (X : AlgebraicSpace S) (L : X.Modules)
    (hL : X.IsLineModule L) (W : X.EtaleSite) :
    Nonempty ((lineTestFamily X L hL).module W.obj ≅ (schemeRestriction X W).obj L) := by
  change Nonempty ((linePresentation X L hL).module W.obj ≅ (schemeRestriction X W).obj L)
  have hP : (linePresentation X L hL).line = L :=
    (exists_linePresentation X L hL).choose_spec.1
  simpa only [hP] using
    etaleLinePresentation_schemeRestriction X (linePresentation X L hL) W

/-- Étale-local everywhere-defined open canonical section-algebra maps descend to the
global canonical open immersion. In particular the algebraic space is a scheme.
The local models in the binders are presentations of the actual section algebras:
`SpaceSectionAlgebra.sections` is their compatible-section universal property and
`SectionProjModel.evaluation_eq` fixes their adjunction evaluations. Thus the hypothesis
is precisely the assertion about the local canonical maps, independently of presentation.

Source: Stacks, Tag 0D3C, proof of `lemma-descending-property-ample`, and Tag 0D2Z(3)
(blueprint: lem-trf-section-proj-etale-embedding).

Proof:
1. Obtain the normalized section algebra A and its etale base changes from
space_section_algebra_etale_base_change. Present A on the affine basis using
section_proj_model_presentation. The equality of section algebras retains the given
quasi-coherent degrees, products, unit, section universal property and evaluations.
2. For each local model use section_proj_model_comparison with the base-change
section algebra from Step 1. It gives agreement with ordinary schemes, beta, the
coefficientwise PullbackData D, its homogeneous section equation and IsBaseChange.
3. Apply space_line_proj_etale_descent to these data and the local canonical open
immersions. It proves that the generation open is top by local membership in a
subsheaf, identifies the canonical maps by their test formulas, and reduces the
open-immersion property to descent of an arbitrary compatible map into relative Proj.
4. Etaleness of each local scheme chart follows by base change of its etale base map.
The cartesian line presentation on each such chart is its actual Zariski restriction,
by etaleLinePresentation_schemeRestriction.
5. Test the representable open immersion over the identity of its scheme target.
The projection from this representing scheme to X is an isomorphism because it is a
pullback of the identity. Its inverse comparison is the required representation e;
the pullback commutativity equation gives yoneda.map q = e.hom followed by r. Apply
Step 4's restriction theorem also to the etale isomorphism e. Empty schemes, empty
covers and degree zero are included throughout. -/
theorem section_proj_etale_embedding
    (S : Scheme.{u}) (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hqc : IsQuasiCompactPresheafMap f) (hsep : IsSeparatedPresheafMap f)
    (L : X.Modules) (hL : X.IsLineModule L)
    (I : Type v) (Tᵢ Xᵢ : I → Over S) (g : ∀ i, Tᵢ i ⟶ T)
    (hget : ∀ i, Etale (g i).left)
    (hcover : ∀ (V : Over S) (x : V ⟶ T),
      ∃ R : Sieve V.left, R ∈ Scheme.fppfTopology V.left ∧
        ∀ (W : Over S) (a : W ⟶ V), R a.left →
          ∃ (i : I) (b : W ⟶ Tᵢ i), b ≫ g i = a ≫ x)
    (k : ∀ i, yoneda.obj (Xᵢ i) ⟶ X.obj.obj) (fᵢ : ∀ i, Xᵢ i ⟶ Tᵢ i)
    (hcart : ∀ i, IsPullback (k i) (yoneda.map (fᵢ i)) f (yoneda.map (g i)))
    (Mᵢ : ∀ i, SectionProjModel (yoneda.map (fᵢ i))
      ((lineTestFamily X L hL).pullback (k i)))
    (rᵢ : ∀ i, Xᵢ i ⟶ projOver (Tᵢ i) (Mᵢ i).affine)
    (hgen : ∀ i, (Mᵢ i).evaluation.IsGenerationOpen ⊤)
    (hcanonical : ∀ i, (Mᵢ i).evaluation.IsCanonicalMap ⊤
      ((⊤ : Subfunctor (yoneda.obj (Xᵢ i))).ι ≫ yoneda.map (rᵢ i)))
    (hopen : ∀ i, IsOpenImmersion (rᵢ i).left) :
    ∃ M : SectionProjModel f (lineTestFamily X L hL),
      M.sections.AgreesWithSchemes ∧ M.evaluation.IsGenerationOpen ⊤ ∧
      ∃ r : X.obj.obj ⟶ yoneda.obj (projOver T M.affine),
        M.evaluation.IsCanonicalMap ⊤ ((⊤ : Subfunctor X.obj.obj).ι ≫ r) ∧
        IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) r ∧
        (∀ i, (∃ hk : IsEtale (k i),
          Nonempty ((lineTestFamily X L hL).module (CostructuredArrow.mk (k i)) ≅
            (schemeRestriction X ⟨CostructuredArrow.mk (k i), hk⟩).obj L)) ∧
          (Mᵢ i).sections.AgreesWithSchemes ∧
          ∃ (β : SpaceSectionAlgebraBaseChange (k i) (g i) M.sections (Mᵢ i).sections)
            (D : Scheme.GradedAlgebraData.PullbackData (g i).left M.affine (Mᵢ i).affine),
            (∀ (V : T.left.affineOpens) (V' : (Tᵢ i).left.affineOpens)
              (h : V'.1 ≤ (g i).left ⁻¹ᵁ V.1) (n : ℕ) (s : Γ(M.sections.degree n, V.1)),
              D.map h (M.degreeIso V n s) =
                ((Mᵢ i).degreeIso V' n ((β.degree n).hom.app V'.1
                  (sectionAlgebraPullSection (g i).left (M.sections.degree n)
                    V.1 V'.1 h s)) : (Mᵢ i).affine.obj V')) ∧
            M.evaluation.IsBaseChange (k i) (g i) D (Mᵢ i).evaluation ∧
            IsPullback D.relProjComparison (Mᵢ i).affine.relProjHom
              M.affine.relProjHom (g i).left ∧
            (∀ (W : Over S) (a : W ⟶ Xᵢ i),
              (a ≫ rᵢ i).left ≫ D.relProjComparison =
                (r.app (op W) ((k i).app (op W) a)).left)) ∧
        ∃ (U : Over S) (e : yoneda.obj U ≅ X.obj.obj)
          (q : U ⟶ projOver T M.affine),
          IsOpenImmersion q.left ∧ yoneda.map q = e.hom ≫ r ∧
          ∃ he : IsEtale e.hom,
            Nonempty ((lineTestFamily X L hL).module (CostructuredArrow.mk e.hom) ≅
              (schemeRestriction X ⟨CostructuredArrow.mk e.hom, he⟩).obj L) := by
  classical
  obtain ⟨A, hA, hbc⟩ := space_section_algebra_etale_base_change S T X f hqc hsep L hL
  obtain ⟨M, hM⟩ := section_proj_model_presentation A
  have hAM : M.sections.AgreesWithSchemes := by simpa only [hM] using hA
  have hc (i : I) :
      (Mᵢ i).sections.AgreesWithSchemes ∧
        ∃ (β : SpaceSectionAlgebraBaseChange (k i) (g i) M.sections (Mᵢ i).sections)
          (D : Scheme.GradedAlgebraData.PullbackData (g i).left M.affine (Mᵢ i).affine),
          (∀ (V : T.left.affineOpens) (V' : (Tᵢ i).left.affineOpens)
            (h : V'.1 ≤ (g i).left ⁻¹ᵁ V.1) (n : ℕ) (s : Γ(M.sections.degree n, V.1)),
            D.map h (M.degreeIso V n s) =
              ((Mᵢ i).degreeIso V' n ((β.degree n).hom.app V'.1
                (sectionAlgebraPullSection (g i).left (M.sections.degree n)
                  V.1 V'.1 h s)) : (Mᵢ i).affine.obj V')) ∧
          M.evaluation.IsBaseChange (k i) (g i) D (Mᵢ i).evaluation := by
    obtain ⟨B, ⟨β⟩, hB⟩ := hbc (Tᵢ i) (g i) (hget i)
      (yoneda.obj (Xᵢ i)) (k i) (yoneda.map (fᵢ i)) (hcart i)
    have β' : SpaceSectionAlgebraBaseChange (k i) (g i) M.sections B := by
      simpa only [hM] using β
    exact section_proj_model_comparison (k i) (g i) (hcart i).w M (Mᵢ i) B β' hB
  choose hlocal β D hdegree hbase using hc
  obtain ⟨hgenM, r, hr, hopenr, hmap⟩ :=
    space_line_proj_etale_descent S T X f M.affine L hL M.evaluation
      I Tᵢ Xᵢ g hget hcover k fᵢ hcart (fun i ↦ (Mᵢ i).affine) D
      (fun i ↦ (Mᵢ i).evaluation) hbase rᵢ hgen hcanonical hopen
  refine ⟨M, hAM, hgenM, r, hr, hopenr, ?_, ?_⟩
  · intro i
    have hk : IsEtale (k i) := isEtale_of_cartesian_scheme (hcart i) (hget i)
    refine ⟨⟨hk, lineTestFamily_restriction X L hL
      ⟨CostructuredArrow.mk (k i), hk⟩⟩, hlocal i, β i, D i,
      hdegree i, hbase i, (D i).isPullback, hmap i⟩
  · obtain ⟨U, q, t, ht, hq⟩ := hopenr (projOver T M.affine) (𝟙 _)
    have : IsIso t := ht.isIso_fst_of_isIso
    let e : yoneda.obj U ≅ X.obj.obj := asIso t
    have he : IsEtale e.hom := isEtale_of_iso e
    refine ⟨U, e, q, hq, ?_, he,
      lineTestFamily_restriction X L hL ⟨CostructuredArrow.mk e.hom, he⟩⟩
    change yoneda.map q = t ≫ r
    simpa only [Category.comp_id] using ht.w.symm

end AlgebraicGeometry.AlgebraicSpace
