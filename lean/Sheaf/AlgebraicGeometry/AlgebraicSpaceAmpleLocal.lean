/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.EtalePointCoverFppfLifting
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import WeilConjectures.AlgebraicGeometry.AmpleIso
import Sheaf.TraceFormula.AmpleSchemeTestLinePreparation
import Sheaf.TraceFormula.AmpleChartSectionProjModel
import Sheaf.TraceFormula.SectionProjEmbeddingOrdinaryAmple

/-!
# Relative ampleness is étale local on an algebraic-space base

Source: Stacks Project, Descent on Spaces, Tag 0D3C; Divisors on Spaces, Tag 0D36;
Morphisms, Tag 01VH (blueprint: lem-trf-algebraic-space-ample-local).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

private theorem scheme_cover_lifting {S : Scheme.{u}} {I : Type v}
    (T : Over S) (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T)
    (het : ∀ i : I, Etale (g i).left)
    (hs : IsJointlySurjective (fun i : I ↦ yoneda.map (g i)))
    (V : Over S) (x : V ⟶ T) :
    ∃ R : Sieve V.left, R ∈ Scheme.fppfTopology V.left ∧
      ∀ (W : Over S) (a : W ⟶ V), R a.left →
        ∃ (i : I) (b : W ⟶ Tᵢ i), b ≫ g i = a ≫ x := by
  let B : I → (schemeSpace T).EtaleSite := fun i ↦
    ⟨CostructuredArrow.mk (yoneda.map (g i)),
      (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ _).2 (het i)⟩
  have h := (isJointlySurjective_iff_fppf_lifting B).mp hs V (yoneda.map x)
  let Q : Sieve V := Sieve.generate (fun (W : Over S) (a : W ⟶ V) ↦
    ∃ (i : I) (b : W ⟶ Tᵢ i),
      yoneda.map a ≫ yoneda.map x = yoneda.map b ≫ yoneda.map (g i))
  have hQ : Q ∈ (Scheme.fppfTopology.over S) V := h
  let R := Sieve.overEquiv V Q
  refine ⟨R, (Scheme.fppfTopology.mem_over_iff Q).mp hQ, ?_⟩
  intro W a ha
  have ha' : ((Sieve.overEquiv V).symm R) a := ha
  have haQ : Q a := by simpa only [R, OrderIso.symm_apply_apply] using ha'
  obtain ⟨Z, c, d, ⟨i, b, hb⟩, hcd⟩ := haQ
  refine ⟨i, c ≫ b, ?_⟩
  apply yoneda.map_injective
  simp only [Functor.map_comp, Category.assoc]
  rw [← hb, ← Category.assoc, ← Functor.map_comp, hcd]

/-- A line module which is relatively ample on a jointly surjective étale scheme
cover of the base makes the morphism representable. On every étale scheme test,
its restriction is ample over every affine open of the test scheme. In particular,
if the base is a scheme, its identity test gives a scheme representing the source
and the stated ampleness over all affine opens of the base.

The covering hypothesis uses the sieve of local factorizations through the members
of the family. Membership in the big fppf topology says that the family is jointly
surjective: for representable étale arrows this is precisely fppf-local lifting of
scheme-valued sections. It imposes no finiteness condition on the family.
`schemeRestriction` is restriction to Zariski opens, the ordinary invertible module
corresponding to the line module on the small étale site.

Source: Stacks, Tags 0D3C, 0D36 and 01VH
(blueprint: lem-trf-algebraic-space-ample-local).

Proof:
1. The residue-field cover equivalence changes the covering sieve hypothesis into
   the preparation theorem's point-lifting hypothesis. The open restriction/tensor
   isomorphism transports the local invertibility and ampleness hypotheses.
2. Apply exists_ampleSchemeTestLinePreparation on each arbitrary scheme test. Its
   result supplies the actual cartesian source, base-changed covers, descended line
   module, ordinary chart identifications, quasi-compactness and separatedness.
3. On each prepared scheme chart, exists_sectionProjModel_of_ample_chart supplies
   the everywhere-generated canonical section model and its open immersion. The
   point-cover equivalence supplies the embedding theorem's scheme fppf lifts.
4. Apply section_proj_etale_embedding to these local models. It gives the global
   canonical open immersion, its normalized section comparisons, and an etale
   representing isomorphism from a scheme.
5. Take the Yoneda preimage of the composite with the base projection. Transport
   the prepared cartesian square through the representing isomorphism. This works
   on all scheme tests and proves representability.
6. On an etale test the preparation identifies the descended line module with the
   pullback of M. Apply ordinary_ample_of_sectionProj_embedding to the global
   canonical embedding and this identification. Its ordinary restriction is exactly
   the schemeRestriction in the conclusion, on every inverse-image affine open. -/
theorem representable_and_ample_of_etale_cover
    {S : Scheme.{u}} {F Y : AlgebraicSpace S} (f : F ⟶ Y)
    (M : F.Modules) (hM : F.IsLineModule M)
    (I : Type v) (Yᵢ : I → Y.EtaleSite) (Xᵢ : I → F.EtaleSite)
    (pᵢ : ∀ i : I, (Xᵢ i).obj.left ⟶ (Yᵢ i).obj.left)
    (hcover : ∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj),
      Sieve.generate (fun (U : Over S) (k : U ⟶ T) ↦
        ∃ (i : I) (b : U ⟶ (Yᵢ i).obj.left),
          yoneda.map k ≫ a = yoneda.map b ≫ (Yᵢ i).obj.hom) ∈
            (Scheme.fppfTopology.over S) T)
    (hpb : ∀ i : I, IsPullback (Xᵢ i).obj.hom (yoneda.map (pᵢ i))
      f.hom.hom (Yᵢ i).obj.hom)
    (hample : ∀ (i : I) (W : (Y.etaleForget.obj (Yᵢ i)).Opens), IsAffineOpen W →
      ∃ hL : ((Scheme.Modules.restrictFunctor (((pᵢ i).left ⁻¹ᵁ W).ι)).obj
          ((F.schemeRestriction (Xᵢ i)).obj M)).IsInvertible,
        @Scheme.Modules.IsAmple ((pᵢ i).left ⁻¹ᵁ W).toScheme
          ((Scheme.Modules.restrictFunctor (((pᵢ i).left ⁻¹ᵁ W).ι)).obj
            ((F.schemeRestriction (Xᵢ i)).obj M)) hL) :
    IsRepresentable f.hom.hom ∧
      ∀ T : Y.EtaleSite, ∃ (X : F.EtaleSite) (p : X.obj.left ⟶ T.obj.left),
        IsPullback X.obj.hom (yoneda.map p) f.hom.hom T.obj.hom ∧
          ∀ W : (Y.etaleForget.obj T).Opens, IsAffineOpen W →
            ∃ hL : ((Scheme.Modules.restrictFunctor ((p.left ⁻¹ᵁ W).ι)).obj
                ((F.schemeRestriction X).obj M)).IsInvertible,
              @Scheme.Modules.IsAmple (p.left ⁻¹ᵁ W).toScheme
                ((Scheme.Modules.restrictFunctor ((p.left ⁻¹ᵁ W).ι)).obj
                  ((F.schemeRestriction X).obj M)) hL := by
  classical
  have hjoint := (isJointlySurjective_iff_fppf_lifting Yᵢ).mpr hcover
  have htensor : ∀ (i : I) (W : (Y.etaleForget.obj (Yᵢ i)).Opens), IsAffineOpen W →
      ∃ h : ((Scheme.Modules.tensorPullback ((pᵢ i).left ⁻¹ᵁ W).ι).obj
          ((F.schemeRestriction (Xᵢ i)).obj M)).IsInvertible,
        @Scheme.Modules.IsAmple ((pᵢ i).left ⁻¹ᵁ W).toScheme
          ((Scheme.Modules.tensorPullback ((pᵢ i).left ⁻¹ᵁ W).ι).obj
            ((F.schemeRestriction (Xᵢ i)).obj M)) h := by
    intro i W hW
    obtain ⟨hL, ha⟩ := hample i W hW
    let := hL
    let e := (Scheme.Modules.restrictFunctorIsoTensorPullback
      ((pᵢ i).left ⁻¹ᵁ W).ι).app ((F.schemeRestriction (Xᵢ i)).obj M)
    let := Scheme.Modules.IsInvertible.of_iso e
    exact ⟨inferInstance, (Scheme.Modules.isAmple_iff_of_iso e).mp ha⟩
  have test (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj) :
      ∃ (P : AmpleSchemeTestLinePreparation f M Yᵢ Xᵢ pᵢ T a)
        (A : SectionProjModel P.toT (lineTestFamily P.X P.N P.isLine))
        (r : P.X.obj.obj ⟶ yoneda.obj (projOver T A.affine)),
        A.sections.AgreesWithSchemes ∧ A.evaluation.IsGenerationOpen ⊤ ∧
        A.evaluation.IsCanonicalMap ⊤ ((⊤ : Subfunctor P.X.obj.obj).ι ≫ r) ∧
        IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) r ∧
        (∃ (U : Over S) (e : yoneda.obj U ≅ P.X.obj.obj), IsEtale e.hom) ∧
        (IsEtale a → AmpleTestEtaleComparison F P.X P.toF M P.N Xᵢ P.Xᵢ P.xF
          P.original P.identification) := by
    obtain ⟨P, hP⟩ := exists_ampleSchemeTestLinePreparation
      f M hM I Yᵢ Xᵢ pᵢ hjoint hpb htensor T a
    have local_models (i : I) := exists_sectionProjModel_of_ample_chart
      P.X P.N P.isLine (P.Tᵢ i) (P.Xᵢ i) (P.xT i)
      ((Scheme.Modules.tensorPullback (P.xF i).left).obj
        ((F.schemeRestriction (Xᵢ i)).obj M))
      (P.invertible i) (P.identification i) (P.ample i)
    choose Aᵢ rᵢ hgen hcan hopen using local_models
    obtain ⟨A, hagrees, hgenA, r, hcanA, hopenA, _hbase, U, e, _q, _hq, _heq,
      he, _hline⟩ := section_proj_etale_embedding S T P.X P.toT P.quasiCompact
        P.separated P.N P.isLine I P.Tᵢ (fun i ↦ (P.Xᵢ i).obj.left) P.tT
        P.baseEtale (scheme_cover_lifting T P.Tᵢ P.tT P.baseEtale P.baseSurjective)
        (fun i ↦ (P.Xᵢ i).obj.hom) P.xT P.sourceCartesian Aᵢ rᵢ hgen hcan hopen
    exact ⟨P, A, r, hagrees, hgenA, hcanA, hopenA, ⟨U, e, he⟩, hP⟩
  constructor
  · intro T a
    obtain ⟨P, _A, _r, _hagrees, _hgen, _hcan, _hopen, ⟨U, e, _he⟩, _hP⟩ := test T a
    let p := yoneda.preimage (e.hom ≫ P.toT)
    refine ⟨U, p, e.hom ≫ P.toF.hom.hom, ?_, trivial⟩
    have hp : yoneda.map p = e.hom ≫ P.toT := yoneda.map_preimage _
    exact P.cartesian.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simpa using hp.symm) (by simp) (by simp)
  · intro T
    obtain ⟨P, A, r, hagrees, hgen, hcan, hopen, ⟨U, e, he⟩, hP⟩ :=
      test T.obj.left T.obj.hom
    let p := yoneda.preimage (e.hom ≫ P.toT)
    have hp : yoneda.map p = e.hom ≫ P.toT := yoneda.map_preimage _
    have hk := P.etale_toF T.property
    obtain ⟨z, _hz, _hunique⟩ := hP T.property hk
    refine ⟨⟨CostructuredArrow.mk (e.hom ≫ P.toF.hom.hom),
      isEtale_comp _ _ he hk⟩, p, ?_, ?_⟩
    · exact P.cartesian.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simpa using hp.symm) (by simp) (by simp)
    · exact ordinary_ample_of_sectionProj_embedding P.X T.obj.left P.toT
        P.quasiCompact P.separated P.N P.isLine A hagrees hgen r hcan hopen
        U e he p hp F P.toF hk M z

end AlgebraicGeometry.AlgebraicSpace
