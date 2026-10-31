/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.CategoryTheory.Sites.SmallSheafCoproductLabels

/-!
# Covering lifts characterize epimorphic families

Source: Stacks Project, Sites, Tag 0D06, the forward proof before quasi-compactness,
and Tag 00WT, the covering-surjectivity argument
(blueprint: lem-trf-site-epimorphic-family-cover-lifts).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open Opposite CategoryTheory.Limits

namespace CategoryTheory

-- Covering sieves contain actual covers under the recorded covering-presieve axioms.
private theorem cover_lifts_covering_refinement
    {D : Type u} [Category.{v} D] (J : Precoverage D) (hJ : J.IsSiteForCoverings)
    {V : D} {S : Sieve V} (hS : S ∈ J.toGrothendieck V) :
    ∃ T ∈ J V, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : D, {a : Z ⟶ X // R a}
    let V : I → D := fun i ↦ i.1
    let a : ∀ i : I, V i ⟶ X := fun i ↦ i.2.1
    have heq : Presieve.ofArrows V a = R := by
      funext Z b
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.2.2
      · intro hb
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨Z, b, hb⟩
    obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 I X V a (heq ▸ hR) Y f
    refine ⟨Presieve.ofArrows P p, hp, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hle _ _ i.2.2) (q i)
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have hh : ∀ (Y : D) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg

/-- A family over a sheafified representable is epimorphic exactly when its
canonical section lifts to individual summands over a covering of the site object.
The `ULift` in the Yoneda presheaf only places its hom sets in the common universe.
Source: Stacks Project, Sites, Tags 0D06 and 00WT
(blueprint: lem-trf-site-epimorphic-family-cover-lifts).

Proof:
1. Suppose the coproduct map is epi. By
   `lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, lift the section
   eta_U(id_U) locally to sections t_b of the coproduct. Naturality of the unit
   identifies their images with eta_U(v_b).
2. Apply `lem-trf-small-sheaf-coproduct-labels` to the family. Its coproduct
   model C is canonically isomorphic to the chosen coproduct S: the maps
   alpha : C -> S and beta : S -> C preserve each injection, and their
   composites are identities by the colimit uniqueness of
   `def-weil-pbc-category-colimit`. Locally label beta(t_b), then apply alpha
   to obtain sections s_bc of individual summands whose injections equal
   the restrictions of t_b. Naturality and p j_i = p_i give
   p_i(s_bc) = eta_U(v_b w_bc). Compose the two coverings using
   `def-weil-pbc-sites-and-cohomology` and take their dependent-sum index.
3. Conversely, take sheaf maps f,g out of H_U with p f = p g. Composing
   with coproduct injections gives p_i f = p_i g. On the given covering,
   naturality and the lift equations identify the restrictions of
   f_U(eta_U(id_U)) and g_U(eta_U(id_U)). Sheaf separatedness makes these
   sections equal, including when the covering is empty.
4. For every v : T -> U, naturality gives eta_U(v) = H_U(v)(eta_U(id_U)).
   Naturality of f,g and the equality in step 3 imply f eta_U = g eta_U
   componentwise. The unique factorization property of
   `def-weil-pbc-sheafification` gives f = g, the cancellation condition Epi.
-/
theorem site_epimorphic_family_iff_cover_lifts
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings) (U : C) {I : Type w}
    (F : I → Sheaf J.toGrothendieck (Type (max u v w)))
    (p : ∀ i : I, F i ⟶
      (presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
        (uliftYoneda.{max u w}.obj U)) :
    Epi (Sigma.desc p) ↔
      ∃ (A : Type (max u v w)) (V : A → C) (a : ∀ b : A, V b ⟶ U)
        (ι : A → I) (s : ∀ b : A, (F (ι b)).obj.obj (op (V b))),
        Presieve.ofArrows V a ∈ J U ∧
          ∀ b : A, (p (ι b)).hom.app (op (V b)) (s b) =
            (toSheafify J.toGrothendieck (uliftYoneda.{max u w}.obj U)).app
              (op (V b)) (ULift.up (a b)) := by
  classical
  let K := J.toGrothendieck
  let H := (presheafToSheaf K (Type (max u v w))).obj
    (uliftYoneda.{max u w}.obj U)
  let unit : uliftYoneda.{max u w}.obj U ⟶ H.obj :=
    toSheafify K (uliftYoneda.{max u w}.obj U)
  let e := unit.app (op U) (ULift.up (𝟙 U))
  have unit_res (V : C) (a : V ⟶ U) :
      H.obj.map a.op e = unit.app (op V) (ULift.up a) := by
    have h := congrArg
      (fun k : (uliftYoneda.{max u w}.obj U).obj (op U) ⟶ H.obj.obj (op V) ↦
        k (ULift.up (𝟙 U))) (unit.naturality a.op)
    simpa [e, uliftYoneda] using h.symm
  constructor
  · intro hp
    have : Epi (Sigma.desc p) := hp
    obtain ⟨S, eta, c, hc, _, _, hfam, _, _, hlocal, _⟩ :=
      small_sheaf_coproduct_labels J _hJ F
    obtain ⟨q, hq⟩ := (hfam H).2 p
    have hfac : Sigma.desc c ≫ q = Sigma.desc p := by
      apply Sigma.hom_ext
      intro i
      simpa using congrFun hq i
    have : Epi q := epi_of_epi_fac hfac
    have : Sheaf.IsLocallySurjective q := (Sheaf.isLocallySurjective_iff_epi q).2
      inferInstance
    have : Presheaf.IsLocallySurjective K eta := by
      constructor
      intro V t
      obtain ⟨R, hR, hlabel⟩ := hlocal V t
      apply K.superset_covering _ (J.generate_mem_toGrothendieck hR)
      apply (Sieve.generate_le_iff _ _).2
      intro W a ha
      obtain ⟨i, s, hs⟩ := hlabel W a ha
      exact ⟨⟨i, s⟩, hs⟩
    obtain ⟨R, hR, hle⟩ := cover_lifts_covering_refinement J _hJ
      (Presheaf.imageSieve_mem K (eta ≫ q.hom) (U := op U) e)
    let A : Type (max u v w) := ULift.{w} (Σ V : C, {a : V ⟶ U // R a})
    let V : A → C := fun b ↦ b.down.1
    let a : ∀ b : A, V b ⟶ U := fun b ↦ b.down.2.1
    have hrep (b : A) : ∃ (i : I) (s : (F i).obj.obj (op (V b))),
        (p i).hom.app (op (V b)) s = unit.app (op (V b)) (ULift.up (a b)) := by
      obtain ⟨⟨i, s⟩, hs⟩ := hle _ _ b.down.2.2
      refine ⟨i, s, ?_⟩
      have heq := congrArg (fun f : F i ⟶ H ↦ f.hom.app (op (V b)) s)
        (congrFun hq i)
      change q.hom.app _ ((c i).hom.app _ s) = _ at heq
      rw [hc] at heq
      exact heq.symm.trans (hs.trans (unit_res (V b) (a b)))
    choose i s hs using hrep
    refine ⟨A, V, a, i, s, ?_, hs⟩
    have heq : Presieve.ofArrows V a = R := by
      funext W f
      apply propext
      constructor
      · rintro ⟨b⟩
        exact b.down.2.2
      · intro hf
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨⟨W, f, hf⟩⟩
    exact heq ▸ hR
  · rintro ⟨A, V, a, i, s, hcover, hs⟩
    constructor
    intro G f g hfg
    have hpi (j : I) : p j ≫ f = p j ≫ g := by
      have h := congrArg (fun k ↦ Sigma.ι F j ≫ k) hfg
      simpa using h
    have he : f.hom.app (op U) e = g.hom.app (op U) e := by
      have hsheaf := (isSheaf_iff_isSheaf_of_type K G.obj).mp G.property
      apply (hsheaf.isSheafFor_of_mem_precoverage hcover).isSeparatedFor.ext
      rintro W b ⟨j⟩
      dsimp
      rw [← NatTrans.naturality_apply f.hom, ← NatTrans.naturality_apply g.hom,
        unit_res, ← hs j]
      exact congrArg (fun k : F (i j) ⟶ G ↦ k.hom.app (op (V j)) (s j)) (hpi (i j))
    apply Sheaf.hom_ext
    apply sheafify_hom_ext K f.hom g.hom G.property
    apply uliftYonedaEquiv.{max u w}.injective
    exact he

end CategoryTheory
