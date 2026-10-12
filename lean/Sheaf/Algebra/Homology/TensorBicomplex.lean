/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The unsigned tensor bicomplex

Source: Stacks Project, Algebra, Tag 00M3, first paragraph of the proof.
(blueprint: def-weil-pbc-tensor-bicomplex)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

/-- The commuting tensor bicomplex, with terms `Pᵢ ⊗ Qⱼ` and no totalization signs.
Source: Stacks Project, Algebra, Tag 00M3, proof, first paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
def tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ofGradedObject (.down ℕ) (.down ℕ)
    (fun pq => P.X pq.1 ⊗ Q.X pq.2)
    (fun p p' q => P.d p p' ⊗ₘ 𝟙 (Q.X q))
    (fun p q q' => 𝟙 (P.X p) ⊗ₘ Q.d q q')
    (by intro p p' h q; simp [P.shape p p' h])
    (by intro p q q' h; simp [Q.shape q q' h])
    (by
      intro p p' p'' q
      simp only [tensorHom_comp_tensorHom, HomologicalComplex.d_comp_d, Category.comp_id]
      simp)
    (by
      intro p q q' q''
      simp only [tensorHom_comp_tensorHom, HomologicalComplex.d_comp_d, Category.comp_id]
      simp)
    (by
      intro p p' q q'
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp])

/-- A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
def tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') : tensorBicomplex P Q ⟶ tensorBicomplex P' Q' :=
  homMk (fun pq => a.f pq.1 ⊗ₘ b.f pq.2)
    (by intro p p' q h; simp only [tensorBicomplex, ofGradedObject_d_f, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, a.comm p p'])
    (by intro p q q' h; simp only [tensorBicomplex, ofGradedObject_X_d, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, b.comm q q'])

/-- The tensor of a chain map with a module map, formed by mapping the chain map
and then the module map.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
def chainTensorMap {P P' : ChainComplex (ModuleCat.{u} R) ℕ}
    {N N' : ModuleCat.{u} R} (a : P ⟶ P') (g : N ⟶ N') :
    ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P ⟶
      ((tensorRight N').mapHomologicalComplex (.down ℕ)).obj P' :=
  ((tensorRight N).mapHomologicalComplex (.down ℕ)).map a ≫
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
      (.down ℕ)).app P'

end HomologicalComplex₂
