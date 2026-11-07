/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Submission.WeilConjectures.RingTheory.ProEtale.IndEtale

import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootProductBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineFpIsoIndEtaleDescent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finite-stage descent of punctured root charts

Source: Stacks Project, Tags 0EYG and 05N9.
(blueprint: lem-sbc-punctured-root-charts-ind-etale-descent)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite collection of punctured root charts descends from an ind-etale algebra.

Source: Stacks Project, Tag 0EYG, the finite-presentation descent paragraph;
Tag 05N9 (2), (3) for descent of morphisms and their identities.
(blueprint: lem-sbc-punctured-root-charts-ind-etale-descent)

Proof: Present H as a filtered colimit of etale R-algebras S_i using ι.IndEtale.
Since p is affine and locally of finite presentation, write Y=Spec B with B a
finitely presented R-algebra. Each punctured product of root algebras is affine
and finitely presented over its base: it is the finite product of monic polynomial
quotients followed by the one-element localization at the image of g. The product,
quotients, and localization commute with this filtered base change.

Use Tag 05N9 (2) to descend the coordinate maps of the given isomorphism and its
inverse to a common stage. Use (3) to descend both inverse identities and the
identities with the base algebra. These yield an isomorphism over Spec S_i, hence
exactly the displayed projection identity after applying Spec. The finitely many
units e(k) have inverses in H; descend their inverses and multiplication identities
to a later common stage. The map S_i→H pulls the given point x back to a point z
of Spec S_i. The cocone identity implies Spec(φ)(z)=Spec(ι)(x)=y. Every stage is
etale over R. Retain the original m and e; in particular retain φ(g), rather than
an unspecified associated divisor equation, in every root polynomial.

Edge cases: m=0 gives the zero product ring and empty chart. The inverse maps and
identities still descend for zero rings, so an empty limit fibre becomes empty at
a later stage. No regularity or nonzerodivisor hypothesis is needed. Positive
e(k) is retained unchanged; unit witnesses alone require advancing the stage.
The point x prevents an empty limit spectrum but its puncture may be empty. -/
theorem punctured_root_charts_descend_indEtale
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H) (hι : ι.IndEtale)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hp : IsAffineHom p ∧ LocallyOfFinitePresentation p)
    (x : Spec H) (y : Spec R) (hx : (Spec.map (CommRingCat.ofHom ι)) x = y)
    (m : ℕ) (e : Fin m → ℕ) (he : ∀ k, 0 < e k ∧ IsUnit (e k : H))
    (hmodel :
      let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap H (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap H (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))) (ι g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι))) :
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S),
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧
      (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨hqaff, hqfp, hbase⟩ := punctured_root_product_base_change R g m e
  obtain ⟨γ, hγ⟩ := hmodel
  obtain ⟨δH, hδH⟩ := hbase H ι
  have hcomparison : ∃ α : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅
      pullback (puncturedRootProductMap R g m e) (Spec.map (CommRingCat.ofHom ι)),
      α.hom ≫ pullback.snd (puncturedRootProductMap R g m e)
          (Spec.map (CommRingCat.ofHom ι)) =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
    refine ⟨γ ≪≫ δH.symm, ?_⟩
    change (γ.hom ≫ δH.inv) ≫ _ = _
    rw [Category.assoc, ← hδH, Iso.inv_hom_id_assoc]
    exact hγ
  have ha : ∀ k, IsUnit (ι (e k : R)) := by
    intro k
    simpa only [map_natCast] using (he k).2
  obtain ⟨S, φ, ψ, hφψ, hφ, hunit, α, hα⟩ :=
    affine_fp_iso_descend_indEtale R H ι hι p (puncturedRootProductMap R g m e)
      hp ⟨hqaff, hqfp⟩ m (fun k ↦ (e k : R)) ha hcomparison
  obtain ⟨δS, hδS⟩ := hbase S φ
  refine ⟨S, φ, (Spec.map (CommRingCat.ofHom ψ)) x, hφ, ?_, ?_, α ≪≫ δS, ?_⟩
  · rw [← Scheme.Hom.comp_apply]
    have hcomp : Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ι) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom hφψ)
    rw [hcomp]
    exact hx
  · intro k
    exact ⟨(he k).1, by simpa only [map_natCast] using hunit k⟩
  · change (α.hom ≫ δS.hom) ≫ puncturedRootProductMap S (φ g) m e = _
    rw [Category.assoc, hδS]
    exact hα

end AlgebraicGeometry.Scheme
