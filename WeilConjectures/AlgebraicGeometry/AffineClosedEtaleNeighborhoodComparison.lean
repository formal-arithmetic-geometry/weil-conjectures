/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.AffineClosedHenselianRingPresentation
import WeilConjectures.AlgebraicGeometry.SpecRingCohomologyDiagram
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.Gabber

/-! # Cohomology comparison with affine etale neighborhoods

Source: Stacks Project, Tag 0A51, affine case of the proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- Cohomology on a closed subscheme of an affine scheme is the filtered colimit of
cohomology on its affine étale neighbourhoods, for a torsion sheaf of modules, with all maps
the canonical pullback maps. There is no injectivity hypothesis and no restriction on the
degree.

Precisely: there is a directed system of étale maps `v a : Y a ⟶ X` with transition maps
`w f`, together with factorizations `i = s a ≫ v a` compatible with the transitions, such that
the diagram `H` of the groups `Hᵠ(Y a, (v a)^* G)` (with `G` the underlying abelian sheaf of
`J`), whose transition maps are pullback along `w f`, has a colimit cocone whose legs, followed
by an isomorphism `e` onto `Hᵠ(Z, i^* G)`, are pullback along `s a`.

Source: Stacks Project, Tag 0A51, first paragraph of the proof; Tags 09YQ and 09ZI.
(blueprint: lem-weil-pbc-affine-closed-etale-neighborhood-comparison)

Proof: present X as Spec B and Z as Spec B/K. The pair henselization A = Bʰ is the
filtered colimit of etale B-algebras C whose quotient by K is B/K; their spectra are the
neighbourhoods, and Z → Spec(B/K) → Spec A → Spec C gives the factorizations s. Continuity
(09YQ) identifies the colimit of the cohomology of the pullbacks of G to the spectra Spec C,
with the pullback transition maps, with the cohomology on Spec A, the legs being pullback
maps. Gabber's comparison (09ZI) says that pullback along Spec(A/K) → Spec A is bijective on
the cohomology of the pullback of J, which is torsion; the underlying abelian sheaf of the
module pullback is the abelian pullback of G. The composite of these bijections with the
continuity cocone is the required comparison; by functoriality of pullback maps and the
associativity of the pullback composition isomorphisms its legs are pullback along s.
No acyclicity is used: the same argument applies in degree zero and to noninjective torsion
sheaves.
-/
theorem Etale.affine_closed_etale_neighborhood_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf J] (q : ℕ) :
    let G := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (Y : I → Scheme.{u}) (v : ∀ a, Y a ⟶ X) (w : ∀ {a b : I}, (a ⟶ b) → (Y b ⟶ Y a))
      (hw : ∀ {a b : I} (f : a ⟶ b), v b = w f ≫ v a)
      (s : ∀ a, Z ⟶ Y a) (hs : ∀ a, i = s a ≫ v a),
      (∀ a, Etale (v a)) ∧ (∀ {a b : I} (f : a ⟶ b), s b ≫ w f = s a) ∧
      ∃ (H : I ⥤ AddCommGrpCat.{u + 1})
        (eH : ∀ a, H.obj a ≅
          AddCommGrpCat.of (Sheaf.H (((v a)^*[AddCommGrpCat.{u + 1}]).obj G) q)),
        (∀ {a b : I} (f : a ⟶ b), H.map f =
          (eH a).hom ≫
            AddCommGrpCat.ofHom (cohomologyMap (w f) (((v a)^*[AddCommGrpCat.{u + 1}]).obj G) q) ≫
            AddCommGrpCat.ofHom (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} (w f) (v a)
              (v b) (hw f)).inv.app G) q) ≫ (eH b).inv) ∧
        ∃ (c : Cocone H) (_ : Nonempty (IsColimit c))
          (e : c.pt ≅ AddCommGrpCat.of (Sheaf.H (((i)^*[AddCommGrpCat.{u + 1}]).obj G) q)),
          ∀ a, c.ι.app a ≫ e.hom =
            (eH a).hom ≫
              AddCommGrpCat.ofHom
                (cohomologyMap (s a) (((v a)^*[AddCommGrpCat.{u + 1}]).obj G) q) ≫
              AddCommGrpCat.ofHom (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} (s a) (v a)
                i (hs a)).inv.app G) q) := by
  intro G
  obtain ⟨I, _, _, _, R, c, hc, K, _, t, e, hi, v, wv, wt, hev⟩ :=
    Etale.affine_closed_henselian_ring_presentation i
  obtain ⟨H, eH, hH, B, eB, hB⟩ :=
    Etale.exists_spec_ring_cohomology_diagram R c hc X G v wv t wt q
  obtain ⟨hcol⟩ := Etale.nonempty_isColimit_etale_cohomology_spec_ring_colimit
    R c hc X G v wv t wt q H eH hH B eB hB
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  let kk := e.hom ≫ k
  have hi' : i = kk ≫ t := by rw [hi, Category.assoc]
  let s : ∀ a, Z ⟶ Spec (R.obj a) := fun a ↦ kk ≫ Spec.map (c.ι.app a)
  have hs (a : I) : i = s a ≫ v a := by simp only [hi', wt a, s, kk, Category.assoc]
  have hiso {W : Scheme.{u}} {F F' : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (α : F ≅ F') : Function.Bijective (Sheaf.H.map α.hom q) :=
    Function.bijective_iff_has_inverse.mpr ⟨Sheaf.H.map α.inv q,
      fun x ↦ by rw [← Sheaf.H.map_comp_apply, α.hom_inv_id]; simp,
      fun x ↦ by rw [← Sheaf.H.map_comp_apply, α.inv_hom_id]; simp⟩
  let tG := ((t)^*[AddCommGrpCat.{u + 1}]).obj G
  have hk : Function.Bijective (cohomologyMap k tG q) := by
    let F := ((t)^*[ModuleCat.{u + 1} Λ]).obj J
    have hgab := bijective_cohomologyMap_of_henselianRing Λ K F q
    obtain ⟨ef⟩ := pullback_forget_modules_iso Λ t J
    have heq : ⇑(cohomologyMap k tG q) =
        ⇑(Sheaf.H.map (((k)^*[AddCommGrpCat.{u + 1}]).map ef.hom) q) ∘
          ⇑(cohomologyMap k ((sheafCompose _
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) ∘
          ⇑(Sheaf.H.map ef.inv q) := by
      funext x
      have hx : Sheaf.H.map ef.hom q (Sheaf.H.map ef.inv q x) = x := by
        rw [← Sheaf.H.map_comp_apply, ef.inv_hom_id, Sheaf.H.map_id_apply]
      calc cohomologyMap k tG q x
          = cohomologyMap k tG q (Sheaf.H.map ef.hom q (Sheaf.H.map ef.inv q x)) := by rw [hx]
        _ = _ := cohomologyMap_map k q ef.hom (Sheaf.H.map ef.inv q x)
    rw [heq]
    exact (hiso (((k)^*[AddCommGrpCat.{u + 1}]).mapIso ef)).comp (hgab.comp (hiso ef.symm))
  have hkk : Function.Bijective (cohomologyMap kk tG q) := by
    have heq : ⇑(cohomologyMap kk tG q) =
        ⇑(Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} e.hom k).inv.app tG) q) ∘
          ⇑(cohomologyMap e.hom (((k)^*[AddCommGrpCat.{u + 1}]).obj tG) q) ∘
          ⇑(cohomologyMap k tG q) := by
      funext x
      simp only [Function.comp_apply]
      rw [(cohomologyPullbackFunctorial e.hom k tG q).2.1 x, ← Sheaf.H.map_comp_apply,
        Iso.hom_inv_id_app]
      rw [Sheaf.H.map_id_apply]
      rfl
    rw [heq]
    exact (hiso ((upperStarComp AddCommGrpCat.{u + 1} e.hom k).app tG).symm).comp
      ((cohomologyMap_bijective e.hom _ q).comp hk)
  let φ : Sheaf.H tG q →+ Sheaf.H (((i)^*[AddCommGrpCat.{u + 1}]).obj G) q :=
    (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} kk t i hi').inv.app G) q).comp
      (cohomologyMap kk tG q)
  have hφ : Function.Bijective φ :=
    (hiso ((upperStarComp AddCommGrpCat.{u + 1} kk t i hi').app G).symm).comp hkk
  let E : B.pt ≅ AddCommGrpCat.of (Sheaf.H (((i)^*[AddCommGrpCat.{u + 1}]).obj G) q) :=
    eB ≪≫ (AddEquiv.ofBijective φ hφ).toAddCommGrpIso
  refine ⟨I, inferInstance, inferInstance, inferInstance, fun a ↦ Spec (R.obj a), v,
    fun f ↦ Spec.map (R.map f), fun f ↦ wv _ _ f, s, hs, hev, ?_, H, eH,
    fun f ↦ hH _ _ f, B, ⟨hcol⟩, E, ?_⟩
  · intro a b f
    simp only [s, Category.assoc, ← Spec.map_comp, c.w f]
  · intro a
    have hE : E.hom = eB.hom ≫ AddCommGrpCat.ofHom φ := rfl
    rw [hE, ← Category.assoc, hB a]
    ext x
    simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
      Function.comp_apply, φ]
    rw [cohomologyMap_map]
    erw [(cohomologyPullbackFunctorial kk (Spec.map (c.ι.app a))
      (((v a)^*[AddCommGrpCat.{u + 1}]).obj G) q).2.1]
    rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
    congr 2
    erw [Etale.upperStarComp_hom_app_map_upperStarComp_inv_app_assoc AddCommGrpCat.{u + 1}
      kk (Spec.map (c.ι.app a)) (v a) (s a) t i rfl (wt a) (hs a) G, Iso.hom_inv_id_app,
      Category.comp_id]

end AlgebraicGeometry
