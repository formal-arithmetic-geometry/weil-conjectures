/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.Paper.CechRefinementPushforwardTotal
import Sheaf.Paper.CechPushforwardLambdaColumns
import Sheaf.Algebra.Homology.FirstQuadrantTotalComparison

/-! # Augmentation compatibility for the canonical refinement map

Source: Stacks Project, Tag 01FD, the resolution double-complex diagram.
(blueprint: lem-sc-cech-refinement-resolution-canonical-beta)
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option linter.privateModule false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem scheme_section_forget_eq (X : Scheme.{v}) :
    forget₂ (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{v} =
      forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v} := rfl

private noncomputable def sections_forget_homology_iso {X : Scheme.{v}}
    (K : CochainComplex X.Modules ℕ) (p : ℕ) :
    let Γ := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)
    let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
    (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ e).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology p ≅ e.obj ((Γ.obj K).homology p) :=
  ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
      (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v})

private theorem sections_forget_homology_iso_hom {X : Scheme.{v}}
    (K : CochainComplex X.Modules ℕ) (p : ℕ) :
    (sections_forget_homology_iso K p).hom =
      (((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
          (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v})).hom := rfl

private theorem sections_forget_homology_iso_inv {X : Scheme.{v}}
    (K : CochainComplex X.Modules ℕ) (p : ℕ) :
    (sections_forget_homology_iso K p).inv =
      (((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
          (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v})).inv := rfl

attribute [irreducible] sections_forget_homology_iso

private theorem alpha_forget_naturality {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {K L : CochainComplex X.Modules ℕ} (ψ : K ⟶ L) (p : ℕ) :
    let Γ := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
     (ComplexShape.up ℕ)
    let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
    HomologicalComplex.homologyMap
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ e).mapHomologicalComplex
         (ComplexShape.up ℕ)).map ψ) p ≫
        (((Γ.obj L).sc p).mapHomologyIso e).hom ≫
        e.map (HomologicalComplex.homologyMap (moduleCechComplexAlpha U L) p) =
      (((Γ.obj K).sc p).mapHomologyIso e).hom ≫
        e.map (HomologicalComplex.homologyMap (moduleCechComplexAlpha U K) p) ≫
        e.map (HomologicalComplex.homologyMap ((moduleCechTotalFunctor U).map ψ) p) := by
  intro Γ e
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ p).map (Γ.map ψ)) e
  change HomologicalComplex.homologyMap
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ e).mapHomologicalComplex
       (ComplexShape.up ℕ)).map ψ) p ≫
      (((Γ.obj L).sc p).mapHomologyIso e).hom =
    (((Γ.obj K).sc p).mapHomologyIso e).hom ≫
      e.map (HomologicalComplex.homologyMap (Γ.map ψ) p) at hn
  rw [← Category.assoc, hn, Category.assoc, ← e.map_comp,
    ← HomologicalComplex.homologyMap_comp,
    ← moduleCechComplexAlpha_naturality U ψ, HomologicalComplex.homologyMap_comp,
    e.map_comp]

private theorem augmentation_map_cycle {C : Type*} [Category* C] [HasZeroMorphisms C]
    {K L : CochainComplex C ℕ} (ψ : K ⟶ L) {F : C} (a : F ⟶ K.X 0)
    (ha : a ≫ K.d 0 1 = 0) : (a ≫ ψ.f 0) ≫ L.d 0 1 = 0 := by
  rw [Category.assoc, ψ.comm 0 1, ← Category.assoc, ha, zero_comp]

private theorem resolution_beta_naturality {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (I : InjectiveResolution F)
    (K : CochainComplex X.Modules ℕ) (b : F ⟶ K.X 0) (hb : b ≫ K.d 0 1 = 0)
    (ψ : I.cocomplex ⟶ K) (hψ : I.ι.f 0 ≫ ψ.f 0 = b) :
    moduleCechBeta U I ≫ (moduleCechTotalFunctor U).map ψ =
      moduleCechComplexBeta U K b hb := by
  have h := moduleCechComplexBeta_naturality U (F := F) (I.ι.f 0) (by simp)
    b hb ψ hψ
  simpa only [moduleCechComplexBeta_resolution U I] using h

private theorem beta_forget_comparison {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (I : InjectiveResolution F)
    (P K : CochainComplex X.Modules ℕ) (a : F ⟶ P.X 0)
    (ha : a ≫ P.d 0 1 = 0) (β : I.cocomplex ⟶ K) (l : P ⟶ K)
    (hβ : I.ι.f 0 ≫ β.f 0 = a ≫ l.f 0) (p : ℕ) :
    let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
    e.map (HomologicalComplex.homologyMap (moduleCechBeta U I) p) ≫
        e.map (HomologicalComplex.homologyMap ((moduleCechTotalFunctor U).map β) p) =
      e.map (HomologicalComplex.homologyMap (moduleCechComplexBeta U P a ha) p) ≫
        e.map (HomologicalComplex.homologyMap ((moduleCechTotalFunctor U).map l) p) := by
  intro e
  have hb := augmentation_map_cycle l a ha
  have h₁ := resolution_beta_naturality U I K (a ≫ l.f 0) hb β hβ
  have h₂ := moduleCechComplexBeta_naturality U a ha (a ≫ l.f 0) hb l rfl
  have h := h₁.trans h₂.symm
  simpa only [HomologicalComplex.homologyMap_comp, Functor.map_comp] using
    congrArg (fun k ↦ e.map (HomologicalComplex.homologyMap k p)) h

private theorem replace_last_map {C : Type*} [Category* C] {A B D : C}
    {f : A ⟶ D} {g : A ⟶ B} {h h' : B ⟶ D}
    (hf : f = g ≫ h) (hh : h' = h) : f = g ≫ h' :=
  hf.trans (congrArg (fun m ↦ g ≫ m) hh.symm)

private theorem refinement_diagram_cancel {C : Type*} [Category* C]
    {J₀ J₁ P₀ P₁ I₀ I₁ K₀ TJ TP TK TI CJ CI : C}
    (eJ : J₀ ≅ J₁) (eP : P₀ ≅ P₁) (eI : I₀ ≅ I₁)
    (aj : J₁ ≅ TJ) (ap : P₁ ⟶ TP) (ai : I₁ ⟶ TI)
    (αk : K₀ ⟶ TK) (gb : J₀ ⟶ K₀) (gl : P₀ ⟶ K₀)
    (a : I₀ ⟶ P₀) (a' : P₀ ⟶ I₀) (haa : a ≫ a' = 𝟙 _)
    (g : I₀ ≅ K₀) (hg : a ≫ gl = g.hom)
    (b : TJ ⟶ TK) (l : TP ≅ TK) (s : TP ⟶ TI)
    (bj : CJ ⟶ TJ) (bp : CJ ⟶ TP) (bi : CI ⟶ TI) (γ : CJ ⟶ CI)
    (hab : gb ≫ αk = eJ.hom ≫ aj.hom ≫ b)
    (hal : gl ≫ αk = eP.hom ≫ ap ≫ l.hom)
    (has : ap ≫ s = eP.inv ≫ a' ≫ eI.hom ≫ ai)
    (hbb : bj ≫ b = bp ≫ l.hom) (hbs : bp ≫ s = γ ≫ bi) :
    bj ≫ aj.inv ≫ eJ.inv ≫ gb ≫ g.inv ≫ eI.hom ≫ ai = γ ≫ bi := by
  have hK : g.hom ≫ αk ≫ l.inv ≫ s = eI.hom ≫ ai := by
    rw [← hg, Category.assoc, ← Category.assoc gl αk, hal]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [has]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc a a', haa, Category.id_comp]
  have hK' : αk ≫ l.inv ≫ s = g.inv ≫ eI.hom ≫ ai := by
    rw [← hK]
    simp only [Iso.inv_hom_id_assoc]
  have hα : aj.hom ≫ b ≫ l.inv ≫ s = eJ.inv ≫ gb ≫ g.inv ≫ eI.hom ≫ ai := by
    apply (cancel_epi eJ.hom).1
    simp only [Iso.hom_inv_id_assoc]
    calc
      eJ.hom ≫ aj.hom ≫ b ≫ l.inv ≫ s = (gb ≫ αk) ≫ l.inv ≫ s := by
        rw [hab]
        simp only [Category.assoc]
      _ = gb ≫ g.inv ≫ eI.hom ≫ ai := by
        simp only [Category.assoc]
        rw [hK']
  have ht : aj.inv ≫ eJ.inv ≫ gb ≫ g.inv ≫ eI.hom ≫ ai = b ≫ l.inv ≫ s := by
    rw [← hα]
    simp only [Iso.inv_hom_id_assoc]
  rw [ht, ← Category.assoc bj b, hbb]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hbs

attribute [local irreducible] HomologicalComplex.homologyMap ShortComplex.mapHomologyIso
attribute [local irreducible] moduleCechComplexAlpha moduleCechComplexBeta
  moduleCechAlpha moduleCechBeta

/-- Augmentation compatibility for the total-homology map transported through source alpha.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1, augmentation pentagon.
(blueprint: lem-sc-cech-refinement-resolution-canonical-beta)

Proof: apply the Cech double-complex functor to D.beta and D.lambda. Its coefficient
maps commute with restriction and augmentation. The latter map is a quasi-isomorphism
on resolution columns: on each intersection, pushforward injectives and injectives
are section-acyclic, so sections preserve the quasi-isomorphism D.lambda. Transpose
and use first-quadrant total column comparison to invert it on total homology.
Compose the map induced by D.beta, this inverse, and tuplewise pullback/restriction
from the pushforward complex to the target family. D.compatible gives the augmentation
pentagon. The tuplewise composite on the augmented row is gamma by hgamma. Taking
homology gives the beta equation for this zigzag map. Restriction naturality gives
its alpha square; D.sections identifies the global sections of the pushforward with
those on X'. Cancelling the invertible sections map of D.lambda gives the raw map r
in that square. Since source H(alpha) is invertible, the zigzag map equals the displayed
explicit map. Substituting it into the beta equation proves the claim. No target
cover is needed; empty target families and zero modules yield zero target complexes. -/
theorem cechRefinement_resolution_canonical_beta (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) [F.IsQuasicoherent]
    [EnoughInjectives X.Modules] [EnoughInjectives X'.Modules]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor X'.toRingedSpace).Additive] (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (D : ModuleCohomologyFMapData f F ((tensorPullback f).obj F)
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F)) :
    let r := (((RingedSpace.globalSectionsComplex D.J).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).inv ≫
      HomologicalComplex.homologyMap
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.β) p ≫
      inv (I := D.invertible p) (HomologicalComplex.homologyMap (D.a.hom ≫
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          forget₂ _ AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda) p) ≫
      (((RingedSpace.globalSectionsComplex D.I).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).hom
    letI := moduleCechAlpha_isIso U hU D.J p
    let t := (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).map
        (inv (HomologicalComplex.homologyMap (moduleCechAlpha U D.J) p)) ≫ r ≫
      (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p)
    (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat).map
        (HomologicalComplex.homologyMap (moduleCechBeta U D.J) p) ≫ t =
      cechRefinementHomology gamma p ≫
        (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat).map
          (HomologicalComplex.homologyMap (moduleCechBeta U' D.I) p) := by
  intro r
  have hs := @exists_cechRefinement_pushforward_total.{v} X X' f ι ι' U U'
    refine hrefine F D.I p gamma hgamma D.a D.sections
  obtain ⟨s, hsα, hsβ⟩ := hs
  dsimp only
  let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
  let e' := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
  let Γ := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let ΓAb := (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let P := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D.I.cocomplex
  let TJ := e.obj (((moduleCechTotalFunctor U).obj D.J.cocomplex).homology p)
  let TP := e.obj (((moduleCechTotalFunctor U).obj P).homology p)
  let TK := e.obj (((moduleCechTotalFunctor U).obj D.K).homology p)
  let CJ := e.obj (((cechComplexFunctor U).obj F.presheafModuleCat).homology p)
  let b : TJ ⟶ TK := e.map (HomologicalComplex.homologyMap ((moduleCechTotalFunctor U).map D.β) p)
  have hl : QuasiIso ((moduleCechTotalFunctor U).map D.lambda) :=
    HomologicalComplex₂.quasiIso_totalMap_of_columns
      ((moduleCechDoubleFunctor U).map D.lambda)
      (cech_pushforward_lambda_columns f U D.I.cocomplex D.K D.I.injective
        D.injective D.lambda D.quasiIso)
  let : QuasiIso ((moduleCechTotalFunctor U).map D.lambda) := hl
  let l : TP ≅ TK := e.mapIso (asIso
    (HomologicalComplex.homologyMap ((moduleCechTotalFunctor U).map D.lambda) p))
  let aj : e.obj ((RingedSpace.globalSectionsComplex D.J).homology p) ≅ TJ :=
    e.mapIso (@asIso _ _ _ _
    (HomologicalComplex.homologyMap (moduleCechAlpha U D.J) p)
    (moduleCechAlpha_isIso U hU D.J p))
  let ai := e'.map (HomologicalComplex.homologyMap (moduleCechAlpha U' D.I) p)
  let eJ := sections_forget_homology_iso D.J.cocomplex p
  let eP := sections_forget_homology_iso P p
  let eI := sections_forget_homology_iso D.I.cocomplex p
  let ap := e.map (HomologicalComplex.homologyMap (moduleCechComplexAlpha U P) p)
  let bj : CJ ⟶ TJ := e.map (HomologicalComplex.homologyMap (moduleCechBeta U D.J) p)
  let bp : CJ ⟶ TP := e.map (HomologicalComplex.homologyMap
    (moduleCechComplexBeta U P (cechPushforwardAugmentation f F D.I)
      (cechPushforwardAugmentation_d f F D.I)) p)
  let bi := e'.map (HomologicalComplex.homologyMap (moduleCechBeta U' D.I) p)
  let αk := (sections_forget_homology_iso D.K p).hom ≫
    e.map (HomologicalComplex.homologyMap (moduleCechComplexAlpha U D.K) p)
  let gb := HomologicalComplex.homologyMap (ΓAb.map D.β) p
  let gl := HomologicalComplex.homologyMap (ΓAb.map D.lambda) p
  let g := @asIso _ _ _ _ _ (D.invertible p)
  have hαb : gb ≫ αk = eJ.hom ≫ aj.hom ≫ b := by
    simpa only [gb, αk, eJ, aj, b, ΓAb, Γ, e,
      RingedSpace.globalSectionsComplex, sections_forget_homology_iso_hom,
      scheme_section_forget_eq,
      moduleCechComplexAlpha_resolution U D.J,
      Functor.mapIso_hom, asIso_hom] using (alpha_forget_naturality U D.β p)
  have hαl : gl ≫ αk = eP.hom ≫ ap ≫ l.hom := by
    simpa only [gl, αk, eP, ap, l, ΓAb, Γ, e, sections_forget_homology_iso_hom,
      scheme_section_forget_eq,
      Functor.mapIso_hom, asIso_hom] using (alpha_forget_naturality U D.lambda p)
  have hc : D.J.ι.f 0 ≫ D.β.f 0 =
      cechPushforwardAugmentation f F D.I ≫ D.lambda.f 0 := by
    exact D.compatible.trans (Category.assoc _ _ _).symm
  have hβ₀ := beta_forget_comparison U D.J P D.K (cechPushforwardAugmentation f F D.I)
    (cechPushforwardAugmentation_d f F D.I) D.β D.lambda hc p
  have lh : l.hom = e.map
      (HomologicalComplex.homologyMap ((moduleCechTotalFunctor U).map D.lambda) p) := rfl
  have hβ : bj ≫ b = bp ≫ l.hom :=
    replace_last_map hβ₀ lh
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p
  have haa : HomologicalComplex.homologyMap D.a.hom p ≫
      HomologicalComplex.homologyMap D.a.inv p = 𝟙 _ := (H.mapIso D.a).hom_inv_id
  have hg : HomologicalComplex.homologyMap D.a.hom p ≫ gl = g.hom :=
    by
      simpa only [gl, g, asIso_hom,
        HomologicalComplex.homologyFunctor_map] using
        (HomologicalComplex.homologyMap_comp D.a.hom (ΓAb.map D.lambda) p).symm
  have hsα' : ap ≫ s = eP.inv ≫ HomologicalComplex.homologyMap D.a.inv p ≫
      eI.hom ≫ ai := by
    simpa only [ap, eP, eI, ai, sections_forget_homology_iso_inv,
      sections_forget_homology_iso_hom, P, e, e', Γ,
      RingedSpace.globalSectionsComplex, scheme_section_forget_eq] using hsα
  have h := refinement_diagram_cancel eJ eP eI aj ap ai αk gb gl
    (HomologicalComplex.homologyMap D.a.hom p)
    (HomologicalComplex.homologyMap D.a.inv p) haa g hg b l s
    bj bp bi (cechRefinementHomology gamma p) hαb hαl hsα' hβ hsβ
  dsimp only [r]
  simpa only [bj, aj, eJ, gb, g, eI, ai, bi, ΓAb, e, e',
    sections_forget_homology_iso_inv, sections_forget_homology_iso_hom,
    RingedSpace.globalSectionsComplex, Functor.mapIso_inv, asIso_inv,
    HomologicalComplex.homologyFunctor_map,
    scheme_section_forget_eq, Category.assoc] using h

end
end AlgebraicGeometry.Scheme.Modules
