/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology

/-!
# Second-variable naturality of the locally free Ext comparison

Source: Stacks Project, Derived Categories, Tag 06XR, and Cohomology, Tag 01DZ
(blueprint: lem-sc-ext-locally-free-second-naturality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical Ext-cohomology isomorphism for a finite locally free first argument
intertwines postcomposition on Ext with cohomology of the dual tensor morphism.
Source: Stacks Project, Tags 06XR, 015M, 015E and 01DZ
(blueprint: lem-sc-ext-locally-free-second-naturality).

Proof:
1. Compute Ext using an injective resolution of G
   (lem-weil-pbc-ext-via-injective-resolution). The comparison of lem-sc-ext-locally-free
   is evaluation (lem-sc-ext-evaluation), followed by global sections of internal Hom
   (def-pur-sheaf-hom) and the derived-composite comparison (lem-sc-ext-derived-composite).
   Scheme modules have enough injectives (lem-weil-pbc-scheme-modules-enough-injectives).
2. The dual of F is finite locally free, so its tensor functor T is exact
   (lem-sc-ext-tensor-exact). Evaluation identifies T(I) with Hom(F,I). Tensor-Hom
   adjunction and tensor commutativity (lem-weil-pbc-module-tensor-hom-adjunction,
   lem-weil-pbc-module-tensor-comm) make T preserve injectives
   (lem-sp-right-adjoint-preserves-injectives), hence global-sections acyclic objects
   (lemma-weil-pbc-leray-acyclicity). Thus T of either injective resolution is acyclic.
3. Lift phi to a map psi of injective resolutions (def-sp-injective-resolutions).
   The explicit Ext formula identifies postcomposition by phi[i] with cohomology of
   Hom(F,psi) (lem-weil-pbc-ext-via-injective-resolution).
4. Coefficient naturality of evaluation (lem-sc-ext-evaluation), followed by global
   sections (def-pur-sheaf-hom), identifies this map with cohomology of Gamma(T(psi)).
5. Naturality of the acyclic-resolution comparison (lem-sc-acyclic-comparison-natural)
   identifies the latter map with H of T(phi) (def-sc-sheaf-cohomology-functor).
   Composing these squares gives the equality under the canonical equivalences. -/
theorem locallyFreeExtAddEquivH_second_naturality
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (F G G' : X.Modules) [F.IsFiniteLocallyFree]
    (φ : G ⟶ G') (i : ℕ) (z : Ext F G i) :
    locallyFreeExtAddEquivH F G' i (z.comp (Abelian.Ext.mk₀ φ) (Nat.add_zero i)) =
      H.map (Fᵛ ◁ φ) i (locallyFreeExtAddEquivH F G i z) := sorry

end AlgebraicGeometry.Scheme.Modules
