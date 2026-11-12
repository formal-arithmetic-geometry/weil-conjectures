/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomologyEvaluationRestrictionComparison
import WeilConjectures.Algebra.Homology.HomologyEvaluationRoofNaturality

/-! # Compatibility of homology evaluation with a quasi-isomorphism roof

Source: Stacks Project, Tags 0A8X, 0A95, and 08DL. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

-- Reuse the native Abelian structures without repeating the sheafification instance search.
noncomputable local instance homologyEvaluationRoofComparisonAbelian (X : Scheme.{u}) :
    Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf

noncomputable local instance homologyEvaluationRoofComparisonOverAbelian
    (X : Scheme.{u}) (U : X.Opens) : Abelian (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  SheafOfModules.instAbelian (X.ringCatSheaf.over U)

private theorem homComplex_precomp_homology_isIso
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    {A B K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (t : A ⟶ B) [K.IsKInjective] [QuasiIso t] (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map t.op).app K) n) := by
  have h := quasiIso_homComplex_map (𝟙 K) t
  simp only [Functor.map_id, Category.comp_id] at h
  let : QuasiIso (((homComplexFunctor (R := R)).map t.op).app K) := h
  infer_instance

private theorem homologyEvaluation_compose_roof_square
    {C : Type*} [Category* C] {M N U V P Q Z Y : C}
    (e : M ⟶ N) (g : U ⟶ V) (f : P ⟶ Q)
    (a₀ : M ≅ U) (b₀ : N ≅ V) (aq : U ≅ Z) (ap : P ≅ Z)
    (bq : V ≅ Y) (bp : Q ≅ Y)
    (h₀ : e ≫ b₀.hom = a₀.hom ≫ g)
    (hs : g ≫ bq.hom = aq.hom ≫ ap.inv ≫ f ≫ bp.hom) :
    e ≫ (b₀ ≪≫ bq ≪≫ bp.symm).hom =
      (a₀ ≪≫ aq ≪≫ ap.symm).hom ≫ f := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    _ = ((e ≫ b₀.hom) ≫ bq.hom) ≫ bp.inv := by simp only [Category.assoc]
    _ = a₀.hom ≫ (g ≫ bq.hom) ≫ bp.inv := by rw [h₀]; simp only [Category.assoc]
    _ = _ := by rw [hs]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Restriction and a quasi-isomorphism roof identify cycle evaluations by a
commutative square. No finite-freeness, zero-differential, concentration, or
invertibility hypothesis on the model evaluation is used.

Source: Stacks Project, Tag 0A8X, Hom-complex projections; Tag 0A95,
quasi-isomorphism invariance into K-injectives; Tag 08DL, open restriction.
(blueprint: new-v4-homology-evaluation-roof-comparison).

Proof: Write F for the two restrictions and K = F(J). Exactness of restriction
identifies F(H^n(Hom(T,J))) with H^n(Hom(F(T),K)), and identifies restricted
homology and internal Hom with the corresponding objects on the over site.
Construct the comparison from the fixed projections: overHomObjIso and
internalHom_overEquiv supply natural isomorphisms on each internal-Hom factor.
Restriction preserves these products sectionwise; the open equivalence preserves
all limits. The product universal property gives degreewise isomorphisms with
the specified projection equations. Applying each target projection and the
Hom differential formula proves compatibility with the differentials. The factor
comparisons reindex the same local linear maps, so evaluation on local sections
is preserved. Thus this comparison carries he to evaluation on F(T); a bare
existential isomorphism of Hom complexes alone would not give that compatibility.
Apply Hom(-,K) to q and p. K-injectivity and quasi-isomorphism invariance give
isomorphisms on homology from Hom(F(T),K) and Hom(E,K) to Hom(L,K).
Their composite supplies a, oriented from the restricted source to the model
source. Homology(q) and Homology(p) are isomorphisms; applying the internal-Hom
bifunctor and the restriction comparison supplies b with the same orientation.
The product-projection naturality equation identifies evaluation after
precomposition with q or p on cycle representatives. The first identity for c
identifies the resulting K-cycle, and the second identifies its homology class
with f applied to the Hom class. Thus both routes in the asserted square agree
on Hom-cycles and on source cycles. All homology classes lift locally to cycles,
so separatedness of the target sheaf and of internal Hom gives equality of
morphisms. This proves the square without assuming that f is invertible.
No basis, support bound, concentration hypothesis, or nonzero open is used. -/
theorem homologyEvaluation_roof_comparison (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (E L : CochainComplex (SheafOfModules (V.toScheme.ringCatSheaf.over W)) ℤ)
    (q : L ⟶ (moduleOpenOverComplexFunctor X V W).obj T)
    (p : L ⟶ E) (hq : QuasiIso q) (hp : QuasiIso p) :
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let P := homComplex (R := V.toScheme.sheaf.over W) E K
    let π := (Classical.choose
      (homComplex_projections_exists (R := V.toScheme.sheaf.over W)))
      E K n (-n) 0 (by omega)
    ∀ (f : P.homology n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        (E.homology (-n)) (K.homology 0))
      (c : P.cycles n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        (E.cycles (-n)) (K.cycles 0)),
      c ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (E.iCycles (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (E.homologyπ (-n)) (𝟙 _) →
      ∃ a : ((Scheme.Modules.restrictFunctor V.ι).obj
          ((homComplex (R := X.sheaf) T J).homology n)).over W ≅ P.homology n,
        ∃ b : ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := X.sheaf)
            (T.homology (-n)) (J.homology 0))).over W ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (E.homology (-n)) (K.homology 0),
        (((Scheme.Modules.restrictFunctor V.ι).map e).over W) ≫ b.hom =
          a.hom ≫ f := by
  dsimp only
  intro f c hc hc'
  have : ((moduleOpenOverComplexFunctor X V W).obj J).IsKInjective := hI
  have : QuasiIso q := hq
  have : QuasiIso p := hp
  let Qmap : (homComplex (R := V.toScheme.sheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T)
      ((moduleOpenOverComplexFunctor X V W).obj J)).homology n ⟶
      (homComplex (R := V.toScheme.sheaf.over W) L
        ((moduleOpenOverComplexFunctor X V W).obj J)).homology n :=
    HomologicalComplex.homologyMap
    (((homComplexFunctor (R := V.toScheme.sheaf.over W)).map q.op).app
      ((moduleOpenOverComplexFunctor X V W).obj J)) n
  let Pmap : (homComplex (R := V.toScheme.sheaf.over W) E
      ((moduleOpenOverComplexFunctor X V W).obj J)).homology n ⟶
      (homComplex (R := V.toScheme.sheaf.over W) L
        ((moduleOpenOverComplexFunctor X V W).obj J)).homology n :=
    HomologicalComplex.homologyMap
    (((homComplexFunctor (R := V.toScheme.sheaf.over W)).map p.op).app
      ((moduleOpenOverComplexFunctor X V W).obj J)) n
  have : IsIso Qmap :=
    homComplex_precomp_homology_isIso (R := V.toScheme.sheaf.over W)
      (K := ((moduleOpenOverComplexFunctor X V W).obj J)) q n
  have : IsIso Pmap :=
    homComplex_precomp_homology_isIso (R := V.toScheme.sheaf.over W)
      (K := ((moduleOpenOverComplexFunctor X V W).obj J)) p n
  obtain ⟨a₀, b₀, g, d, hd, hd', h₀⟩ :=
    homologyEvaluation_restriction_comparison X T J n e he V W
  let bq : SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
      (((moduleOpenOverComplexFunctor X V W).obj T).homology (-n))
      (((moduleOpenOverComplexFunctor X V W).obj J).homology 0) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W) (L.homology (-n))
        (((moduleOpenOverComplexFunctor X V W).obj J).homology 0) :=
    (((SheafOfModules.homFunctor (V.toScheme.sheaf.over W)).mapIso
    (asIso (HomologicalComplex.homologyMap q (-n))).op).app
      (((moduleOpenOverComplexFunctor X V W).obj J).homology 0))
  let bp : SheafOfModules.homObj (R := V.toScheme.sheaf.over W) (E.homology (-n))
      (((moduleOpenOverComplexFunctor X V W).obj J).homology 0) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W) (L.homology (-n))
        (((moduleOpenOverComplexFunctor X V W).obj J).homology 0) :=
    (((SheafOfModules.homFunctor (V.toScheme.sheaf.over W)).mapIso
    (asIso (HomologicalComplex.homologyMap p (-n))).op).app
      (((moduleOpenOverComplexFunctor X V W).obj J).homology 0))
  have hs : g ≫ bq.hom = Qmap ≫ inv Pmap ≫ f ≫ bp.hom := by
    let π := Classical.choose
      (homComplex_projections_exists.{u, u, u, u} (R := V.toScheme.sheaf.over W))
    have hπ := Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (R := V.toScheme.sheaf.over W))
    exact homologyEvaluation_roof_naturality (R := V.toScheme.sheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T) E L
      ((moduleOpenOverComplexFunctor X V W).obj J)
      π hπ.2.1 hπ.2.2 n q p g d f c hd hd' hc hc'
  refine ⟨a₀ ≪≫ asIso Qmap ≪≫ (asIso Pmap).symm, b₀ ≪≫ bq ≪≫ bp.symm, ?_⟩
  exact homologyEvaluation_compose_roof_square (((Scheme.Modules.restrictFunctor V.ι).map e).over W)
    g f a₀ b₀ (asIso Qmap) (asIso Pmap) bq bp h₀ hs

end CategoryTheory
