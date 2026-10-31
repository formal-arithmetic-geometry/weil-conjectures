/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.EtaleHenselianRingLift

/-! # A pointed presentation of a henselian ind-etale algebra

Source: Stacks Project, Tags 08HQ and 04GW.
(blueprint: lem-trf-henselian-ind-etale-pointed-presentation).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace Algebra

private theorem etale_lift
    (R B S K : Type u) [CommRing R] [CommRing B] [CommRing S] [Field K]
    [Algebra R B] [Algebra R S] [Algebra R K] [Algebra.Etale R B]
    [HenselianLocalRing S] (ε : S →ₐ[R] K)
    (hs : Function.Surjective ε) (hk : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal S)
    (q : B →ₐ[R] K) : ∃! f : B →ₐ[R] S, ε.comp f = q := by
  obtain ⟨f, hf, hu⟩ := etale_henselian_ring_lift
    (.of R) (.of B) (.of S) (CommRingCat.ofHom (algebraMap R B))
    ((AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance))
    (CommRingCat.ofHom (algebraMap R S)) K ε.toRingHom hs hk q.toRingHom (by
      ext r
      exact (q.commutes r).trans (ε.commutes r).symm)
  let f' : B →ₐ[R] S := { __ := f, commutes' := DFunLike.congr_fun hf.1 }
  refine ⟨f', ?_, ?_⟩
  · exact AlgHom.coe_ringHom_injective hf.2
  · intro g hg
    apply AlgHom.coe_ringHom_injective
    exact hu g.toRingHom ⟨RingHom.ext g.commutes, congrArg AlgHom.toRingHom hg⟩

/-- A henselian local ind-etale algebra with its specified residue field is the full
pointed-etale colimit.
Source: Stacks Project, Tags 08HQ and 04GW.
(blueprint: lem-trf-henselian-ind-etale-pointed-presentation).

Proof: each pointed etale R-algebra has a unique henselian lift into S. Uniqueness
makes these lifts natural, hence a cocone. Choose a filtered etale presentation of S
and point every stage using epsilon. The henselian lifts of these stages are the
presentation maps by uniqueness. Given any cocone on all pointed algebras, restrict
it to these stages and descend using their colimit. Each etale R-algebra is finitely
presented, so its lift into S factors through a stage. This factorization respects
the pointing and cocone naturality proves the required equation. Uniqueness follows
on the stages. The pointing cocone descends to epsilon because it does so on every
leg, giving the requested specified residue map. -/
theorem strictHenselizationPresentationIn_of_henselian_indEtale
    (R K S : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing S] [Algebra R S] [HenselianLocalRing S] [Algebra.IndEtale R S]
    (ε : S →ₐ[R] K) (hs : Function.Surjective ε)
    (hk : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal S) :
    ∃ P : Algebra.StrictHenselizationPresentationIn.{u, u} R K S,
      P.residueMap = ε.toRingHom := by
  classical
  let D := Algebra.strictHenselizationPointedDiagramIn.{u, u} R K
  let PE := ObjectProperty.FullSubcategory
    (fun t : Over (CommAlgCat.of R K) ↦ Algebra.Etale R t.left)
  have hlift (t : PE) : ∃! f : t.obj.left →ₐ[R] S, ε.comp f = t.obj.hom.hom := by
    let := t.property
    exact etale_lift R _ S K ε hs hk _
  let l (t : PE) := (hlift t).choose
  have hl (t : PE) : ε.comp (l t) = t.obj.hom.hom := (hlift t).choose_spec.1
  have hu (t : PE) (f : t.obj.left →ₐ[R] S) (hf : ε.comp f = t.obj.hom.hom) :
      f = l t := (hlift t).choose_spec.2 f hf
  let c : Cocone D := {
    pt := CommAlgCat.of R S
    ι := {
      app := fun t ↦ CommAlgCat.ofHom (l t)
      naturality := by
        intro t v f
        apply CommAlgCat.hom_ext
        change (l v).comp f.hom.left.hom = l t
        apply hu
        rw [← AlgHom.comp_assoc, hl]
        exact congrArg CommAlgCat.Hom.hom (Over.w f.hom) } }
  obtain ⟨I, _, _, Q, hQ⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := R) (S := S)
  let F : I ⥤ PE := {
    obj := fun i ↦ ⟨Over.mk (CommAlgCat.ofHom (ε.comp (Q.ι.app i).hom)), hQ i⟩
    map := fun f ↦ ObjectProperty.homMk (Over.homMk (Q.diag.map f) (by
      apply CommAlgCat.hom_ext
      change (ε.comp (Q.ι.app _).hom).comp (Q.diag.map f).hom = _
      rw [AlgHom.comp_assoc]
      exact congrArg (ε.comp ·) (congrArg CommAlgCat.Hom.hom (Q.cocone.w f)))) }
  have hleg (i : I) : c.ι.app (F.obj i) = Q.ι.app i := by
    apply CommAlgCat.hom_ext
    exact (hu (F.obj i) (Q.ι.app i).hom rfl).symm
  have hc : IsColimit c := {
    desc := fun s ↦ Q.isColimit.desc (s.whisker F)
    fac := by
      intro s t
      have : IsFinitelyPresentable.{u} (D.obj t) :=
        (CommAlgCat.finitePresentation_le_isFinitelyPresentable R) _
          (RingHom.finitePresentation_algebraMap.mpr (show
            Algebra.FinitePresentation R t.obj.left from by
              let := t.property
              infer_instance))
      obtain ⟨i, f, hf⟩ := IsFinitelyPresentable.exists_hom_of_isColimit Q.isColimit
        (c.ι.app t)
      let g : t ⟶ F.obj i := ObjectProperty.homMk (Over.homMk f (by
        apply CommAlgCat.hom_ext
        change (ε.comp (Q.ι.app i).hom).comp f.hom = t.obj.hom.hom
        rw [AlgHom.comp_assoc]
        have hh := congrArg CommAlgCat.Hom.hom hf
        exact (congrArg (ε.comp ·) hh).trans (hl t)))
      rw [← hf, Category.assoc]
      exact (congrArg (fun a ↦ f ≫ a) (Q.isColimit.fac (s.whisker F) i)).trans
        (s.w g)
    uniq := by
      intro s m hm
      apply Q.isColimit.hom_ext
      intro i
      rw [Q.isColimit.fac]
      rw [← hleg i]
      exact hm (F.obj i) }
  let P : Algebra.StrictHenselizationPresentationIn.{u, u} R K S :=
    ⟨c, hc, Iso.refl _⟩
  refine ⟨P, ?_⟩
  have he : hc.desc (Algebra.strictHenselizationPointingCoconeIn R K) =
      CommAlgCat.ofHom ε := by
    apply hc.hom_ext
    intro t
    rw [hc.fac]
    apply CommAlgCat.hom_ext
    exact (hl t).symm
  change (𝟙 (CommAlgCat.of R S) ≫
    hc.desc (Algebra.strictHenselizationPointingCoconeIn R K)).hom.toRingHom = _
  rw [Category.id_comp, he]
  rfl

end Algebra
