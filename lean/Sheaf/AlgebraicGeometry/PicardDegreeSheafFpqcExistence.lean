/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Degree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Sheaf.AlgebraicGeometry.PicardSheafFpqc

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Existence of an fpqc amalgamation for the fppf sheafification of a fixed fibrewise-degree
subfunctor. The full relative Picard sheaf is an fpqc sheaf, by normalized invertible-module
descent after a finite separable point extension. Map the compatible family into this sheaf
and glue it. Its degree is `d`, since degree commutes with base change and the fpqc cover is
jointly surjective. Locally for the fppf topology the glued section has a Picard-presheaf
representative; its degree is `d`, so the representative belongs to the given subfunctor.
These local preimages glue in its fppf sheafification, using injectivity of the sheafified
inclusion. Their image is the glued full Picard section, and injectivity verifies the
required amalgamation. Source: Stacks Project, Tags 0D28, 0D2B and 023T; degree base change
is provided by the existing Picard degree theory.
(blueprint: lem-pd-degree-picard-sheaf-fpqc-existence) -/
theorem exists_amalgamation_fpqc_sheafify_picardDegree
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (d : ℤ) (S : Subfunctor (picardPresheaf f))
    (hS : ∀ (T : Over (Spec (.of k))) (L : (picardPresheaf f).obj (op T)),
      L ∈ S.obj (op T) ↔ ∀ t, picardPresheafDegree f L t = d)
    {T : Over (Spec (.of k))} (R : Sieve T)
    (hR : R ∈ (Scheme.fpqcTopology.over (Spec (.of k))) T)
    (x : Presieve.FamilyOfElements
      ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
        S.toFunctor).obj R.arrows)
    (hx : x.Compatible) :
    ∃ t, x.IsAmalgamation t := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) f
  let J := Scheme.fppfTopology.over (Spec (.of k))
  letI : Presheaf.IsLocallySurjective J (toPicardFunctor f) := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ _)
    infer_instance
  let Q := ((presheafToSheaf J (Type (u + 1))).obj S.toFunctor).obj
  let τ : Q ⟶ (picardFunctor f).obj := sheafifyMap J S.ι
  have hτ : ∀ U, Function.Injective (τ.app U) := by
    intro U
    change Function.Injective
      (((presheafToSheaf J (Type (u + 1))).map S.ι).hom.app U)
    have h : Sheaf.IsLocallyInjective
        ((presheafToSheaf J (Type (u + 1))).map S.ι) := by
      rw [Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
      infer_instance
    exact (Sheaf.isLocallyInjective_iff_injective _).1 h U
  have hτ_unit (U : Over (Spec (.of k))) (L : S.toFunctor.obj (op U)) :
      τ.app (op U) ((toSheafify J S.toFunctor).app (op U) L) =
        (toPicardFunctor f).app (op U) L.1 := by
    exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (toSheafify_naturality J S.ι) (op U)) L).symm
  have hdeg (U : Over (Spec (.of k))) (s : Q.obj (op U)) (u : U.left) :
      picardDegree f (τ.app (op U) s) u = d := by
    obtain ⟨Z, g, ⟨L, hL⟩, _, _, z, hz⟩ :=
      Scheme.exists_flat_mem_of_mem_fppfTopology_over
        (Presheaf.imageSieve_mem J (toSheafify J S.toFunctor) s) u
    rw [← hz, ← picardDegree_map f g, ← NatTrans.naturality_apply τ g.op s, ← hL,
      hτ_unit, picardDegree_toPicardFunctor]
    exact (hS Z L.1).1 L.2 z
  let y := x.map τ
  have hy := hx.map τ
  obtain ⟨t, ht, _⟩ :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqc_picardFunctor_of_curve f)) R hR y hy
  have htd (u : T.left) : picardDegree f t u = d := by
    obtain ⟨Z, g, hg, z, hz⟩ := Scheme.exists_mem_of_mem_fpqcTopology
      ((GrothendieckTopology.mem_over_iff _ _).1 hR) u
    let U : Over (Spec (.of k)) := Over.mk (g ≫ T.hom)
    let a : U ⟶ T := Over.homMk g
    have ha : R a := (Sieve.overEquiv_iff _ _).1 hg
    rw [← hz]
    change picardDegree f t (a.left z) = d
    rw [← picardDegree_map f a t, ht a ha]
    exact hdeg U (x a ha) z
  have hImage : Presheaf.imageSieve τ t ∈ J T := by
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J (toPicardFunctor f) t)
    intro U g hg
    obtain ⟨L, hL⟩ := hg
    have hLS : L ∈ S.obj (op U) := (hS U L).2 fun u ↦ by
      rw [← picardDegree_toPicardFunctor f L, hL, picardDegree_map]
      exact htd (g.left u)
    exact ⟨(toSheafify J S.toFunctor).app _ ⟨L, hLS⟩, (hτ_unit U ⟨L, hLS⟩).trans hL⟩
  let v : Presieve.FamilyOfElements Q (Presheaf.imageSieve τ t).arrows :=
    fun _ g hg ↦ Presheaf.localPreimage τ t g hg
  have hv : v.Compatible := by
    intro U₁ U₂ W a₁ a₂ g₁ g₂ hg₁ hg₂ h
    apply hτ (op W)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    change (picardFunctor f).obj.map a₁.op
        (τ.app _ (Presheaf.localPreimage τ t g₁ hg₁)) =
      (picardFunctor f).obj.map a₂.op
        (τ.app _ (Presheaf.localPreimage τ t g₂ hg₂))
    rw [Presheaf.app_localPreimage, Presheaf.app_localPreimage,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h]
  obtain ⟨s, hs, _⟩ := ((isSheaf_iff_isSheaf_of_type _ _).1
    ((presheafToSheaf J (Type (u + 1))).obj S.toFunctor).property)
      (Presheaf.imageSieve τ t) hImage v hv
  have hst : τ.app (op T) s = t := by
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctor f).property).isSeparated
      _ hImage).ext
    intro U g hg
    rw [← NatTrans.naturality_apply τ g.op s, hs g hg]
    exact Presheaf.app_localPreimage τ t g hg
  refine ⟨s, ?_⟩
  intro U g hg
  apply hτ (op U)
  rw [NatTrans.naturality_apply, hst]
  exact ht g hg

end AlgebraicGeometry
