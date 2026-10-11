/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.CategoryTheory.SiteCechComplex
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Čech complex of a finite affine étale covering and its disjoint union

Source: Stacks Project, `literature/stacks-project/etale-cohomology.tex`,
Lemma Tag 03OZ (blueprint: lem-sc-etale-standard-cover-cech).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite affine étale covering may be replaced by its disjoint-union cover, and
this replacement identifies the associated Čech complexes of every abelian sheaf.
Source: Stacks Project, Lemma Tag 03OZ (blueprint: lem-sc-etale-standard-cover-cech).

Proof: the finite coproduct is affine and its induced map is étale and surjective;
etale maps are flat, and a flat map with surjective spectrum is faithfully flat.
The fibre products of the coproduct distribute over the finite family of fibre products.
The sheaf equalizer axiom for the coproduct summands gives the product of section groups,
and the distribution isomorphisms commute with all face maps, hence induce an isomorphism
of Čech complexes. -/
theorem etale_standard_cover_cech
    (A : CommRingCat.{u}) (X : Scheme.{u})
    (hX : X = AlgebraicGeometry.Spec A) (I : Type u) [Finite I]
    (U : I → X.Etale)
    (hU : ∀ i : I, IsAffine (U i).left)
    (f : ∀ i : I, U i ⟶ Scheme.Etale.mk (𝟙 X))
    (hcover : Sieve.ofArrows U f ∈ X.smallEtaleTopology _)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ (V : X.Etale) (fV : V ⟶ Scheme.Etale.mk (𝟙 X)),
      V.left = (∐ fun i : I => (U i).left) ∧
      IsAffine V.left ∧ Surjective V.hom ∧ Etale V.hom ∧
      RingHom.FaithfullyFlat ((Scheme.Γ.map V.hom.op).hom) ∧
      ∃ (S₁ : CategoryTheory.SiteCechComplex U f)
        (S₂ : CategoryTheory.SiteCechComplex (fun _ : Fin 1 => V)
          (fun _ : Fin 1 => fV)),
        Nonempty (S₂.complex F.obj ≅ S₁.complex F.obj) := by
  sorry

end AlgebraicGeometry
