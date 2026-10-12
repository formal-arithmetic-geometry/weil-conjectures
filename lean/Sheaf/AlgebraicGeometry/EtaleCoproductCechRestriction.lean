/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.EtaleFibreProductCoproduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-!
# Bijectivity of restrictions to the summands of a coproduct Čech product

Source: Stacks Project, Étale Cohomology, Tag 03OZ, equation-sheaf-coprod.
(blueprint: lem-sc-etale-coproduct-cech-restriction-bijective)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restrictions from an iterated product of a disjoint union to the indexed
iterated products of its summands give a bijection on sheaf sections.
Source: Stacks Project, Étale Cohomology, Tag 03OZ, equation-sheaf-coprod.
(blueprint: lem-sc-etale-coproduct-cech-restriction-bijective)

Proof: the colimit hypothesis identifies V with the scheme coproduct of the U i,
with c i its coprojections. Apply etale_fibre_product_coproduct to their maps to X.
The universal properties of S₁ and S₂ identify its products with the chosen products
in this statement, including degree zero. Under these identifications g t is the
inclusion of the t-indexed summand: its projections are exactly pr followed by c.
The summands are disjoint open subschemes and cover the entire singleton product,
so they form an étale covering. Apply the proved upstream theorem
Scheme.Etale.isIso_piLift_of_disjoint to this monic disjoint covering. Its proof is
the sheaf equalizer argument: Restrictions on
self-intersections impose no condition; intersections of distinct summands are empty.
An abelian sheaf has zero sections on the empty scheme by the empty covering axiom.
Thus every tuple of sections glues uniquely, and the restriction map is bijective.
The sections indexed by maps to Fin 1 are a single section, since those maps are unique.
For empty I the singleton product is empty and both sides have one zero section.
No affineness, joint surjectivity over X, or differential compatibility is used. -/
theorem etale_coproduct_cech_restriction_bijective
    (X : Scheme.{u}) (I : Type u) [Finite I]
    (U : I → X.Etale) (f : ∀ i, U i ⟶ Scheme.Etale.mk (𝟙 X))
    (V : X.Etale) (fV : V ⟶ Scheme.Etale.mk (𝟙 X))
    (c : ∀ i, U i ⟶ V)
    (hc : IsColimit (Cofan.mk V.left (fun i => (c i).left)))
    (hw : ∀ i, c i ≫ fV = f i)
    (S₁ : SiteCechComplex U f)
    (S₂ : SiteCechComplex (fun _ : Fin 1 => V) (fun _ => fV))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    (g : ∀ t : Fin (p + 1) → I, S₁.W p t ⟶ S₂.W p (fun _ => 0))
    (hg : ∀ t k, g t ≫ S₂.pr p (fun _ => 0) k = S₁.pr p t k ≫ c (t k)) :
    Function.Bijective (fun s : S₂.cochains F.obj p =>
      (fun t => F.obj.map (g t).op (s (fun _ => 0)) : S₁.cochains F.obj p)) := by
  sorry

end AlgebraicGeometry
