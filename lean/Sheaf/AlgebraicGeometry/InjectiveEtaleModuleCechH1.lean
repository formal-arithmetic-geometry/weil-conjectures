/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Degree-one Čech acyclicity of injective étale module sheaves

Source: Stacks Project, Cohomology on Sites, Lemma 03FC, used in Lemma 03FD.
(blueprint: lem-weil-pbc-injective-etale-module-cech-h1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The underlying abelian presheaf of an injective module sheaf has vanishing Čech H¹
on every étale covering, including coverings with an infinite index set.

Source: Stacks Project, Cohomology on Sites, Lemma 03FC
(lemma-injective-module-trivial-cech), proof, and Lemma 03FD, second paragraph.
(blueprint: lem-weil-pbc-injective-etale-module-cech-h1)

Proof: Let O be the constant ring sheaf associated to Λ. Extend the constant Λ-action
on J to O locally and glue; this identifies sheaves valued in Λ-modules with sheaves
of O-modules, preserving injectivity and the underlying abelian sheaf. Sheafification
of module presheaves is exact and left adjoint to inclusion, so J is injective among
module presheaves (03FB). For the covering V → U, form the free O-module presheaf
chain complex K on its iterated fibre products, with alternating deletion maps.
Evaluated at W, partition its basis by the composite W → U. In each summand the basis
in degree p consists of (p+1)-tuples of lifts of that composite to the covering. If
there are no lifts all terms are zero; otherwise adjoining a chosen lift contracts
the complex in positive degree (03F5). Thus K is exact in positive degree. Yoneda
identifies Hom(K_p, J) with the product of sections on the corresponding fibre
products. Under this identification precomposition by deletion is restriction, so
the Hom complex is the Čech complex, including its differential. Exactness of Hom
into the injective module presheaf makes its positive cohomology zero (03FC).
Forgetting scalars changes neither sections nor restrictions (03FD). The resulting
complex is the stated `cechComplexFunctor` complex in the slice Over U, and its
first homology object is therefore zero. No injectivity as an abelian sheaf is used. -/
theorem isZero_cech_H_one_of_injective_module_sheaf
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J]
    (U : Y.Etale) {I : Type (u + 1)} (V : I → Y.Etale) (f : ∀ i : I, V i ⟶ U)
    (hcover : Sieve.ofArrows V f ∈ Y.smallEtaleTopology U) :
    IsZero (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙ ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J).obj)).homology 1) := by
  sorry

end AlgebraicGeometry.Scheme
