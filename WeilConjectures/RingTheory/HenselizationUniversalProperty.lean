/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.HenselizationStageMap

/-!
# Universal property of the henselization of a pair

The henselization of a pair `(B, J)` is initial among henselian pairs under `(B, J)`.

## Implementation details

The colimit cocone `c` represents `(Bʰ, Jʰ)`, and `c.pt.hom.hom` is its structural map
`η : B → Bʰ`; the ideal in the colimit is `J.map c.pt.hom.hom`. The factorization is built
stagewise: for each étale stage `C`, the algebra `A' ⊗[B] C` is étale over `A'`, and its reduced
section lifts by the Gabber root criterion; uniqueness of each section follows from the
idempotent splitting of the étale diagonal and the fact that idempotents are determined modulo
the Jacobson radical. The colimit universal property then gives existence and uniqueness, and
`Jʰ = JBʰ` gives the ideal inclusion.

## References

* [Stacks, Tag 0A02]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The henselization `(Bʰ, Jʰ)` of a pair `(B, J)` has the universal property of a henselian
pair: every map `φ : B → A'` to a henselian pair `(A', I')` carrying `J` into `I'` factors
uniquely through `η : B → Bʰ`, and the factorization carries `Jʰ` into `I'`.
-/
theorem henselization_universal_property (B : Type u) [CommRing B] (J : Ideal B)
    (c : Cocone (ObjectProperty.ι (fun C : Under (CommRingCat.of B) ↦
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
        Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
          (Ideal.le_comap_map)))))
    (hc : Nonempty (IsColimit c))
    (A' : Type u) [CommRing A'] (I' : Ideal A') [HenselianRing A' I']
    (φ : B →+* A') (hφ : J.map φ ≤ I') :
    ∃ ψ : c.pt.right →+* A',
      RingHom.comp ψ (CommRingCat.Hom.hom c.pt.hom) = φ ∧
        (J.map (CommRingCat.Hom.hom c.pt.hom)).map ψ ≤ I' ∧
        ∀ ψ' : c.pt.right →+* A', RingHom.comp ψ' (CommRingCat.Hom.hom c.pt.hom) = φ → ψ' = ψ := by
  classical
  let P := fun C : Under (CommRingCat.of B) ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        (Ideal.le_comap_map))
  have hs (C : ObjectProperty.FullSubcategory P) :
      ∃! τ : C.obj.right →+* A', τ.comp C.obj.hom.hom = φ :=
    existsUnique_henselization_stage_map B J C.obj.right C.obj.hom.hom
      C.property.1 C.property.2 A' I' φ hφ
  choose τ hτ huniq using hs
  let d : Cocone (ObjectProperty.ι P) :=
    { pt := Under.mk (CommRingCat.ofHom φ)
      ι :=
        { app := fun C ↦ Under.homMk (CommRingCat.ofHom (τ C))
            (by apply CommRingCat.hom_ext; exact hτ C)
          naturality := by
            intro C D g
            apply Under.UnderMorphism.ext
            apply CommRingCat.hom_ext
            change (τ D).comp g.hom.right.hom = τ C
            apply huniq C
            rw [RingHom.comp_assoc]
            have hg : g.hom.right.hom.comp C.obj.hom.hom = D.obj.hom.hom :=
              congrArg CommRingCat.Hom.hom (Under.w g.hom)
            rw [hg, hτ D] } }
  let H := hc.some
  let m := H.desc d
  have hm : m.right.hom.comp c.pt.hom.hom = φ :=
    congrArg CommRingCat.Hom.hom (Under.w m)
  refine ⟨m.right.hom, hm, ?_, ?_⟩
  · rw [Ideal.map_map, hm]
    exact hφ
  · intro ψ' hψ'
    let m' : c.pt ⟶ d.pt := Under.homMk (CommRingCat.ofHom ψ')
      (by apply CommRingCat.hom_ext; exact hψ')
    have heq : m' = m := by
      apply H.hom_ext
      intro C
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      change ψ'.comp (c.ι.app C).right.hom =
        m.right.hom.comp (c.ι.app C).right.hom
      have hstage (q : c.pt.right →+* A') (hq : q.comp c.pt.hom.hom = φ) :
          q.comp (c.ι.app C).right.hom = τ C := by
        apply huniq C
        rw [RingHom.comp_assoc]
        have hi : (c.ι.app C).right.hom.comp C.obj.hom.hom = c.pt.hom.hom :=
          congrArg CommRingCat.Hom.hom (Under.w (c.ι.app C))
        rw [hi, hq]
      rw [hstage ψ' hψ', hstage m.right.hom hm]
    exact congrArg (fun q ↦ q.right.hom) heq

end RingTheory
