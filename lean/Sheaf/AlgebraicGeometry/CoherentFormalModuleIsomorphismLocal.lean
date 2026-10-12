/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.Topology.GlueSheavesOfModules

/-!
# Isomorphisms of coherent formal modules are local

Source: Stacks Project, Cohomology of Schemes, Lemma 30.23.2 (Tag 087X),
the locality assertion following the construction of kernels and cokernels
(blueprint: lem-weil-pbc-coherent-formal-modules-isomorphism-local).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Isomorphisms in Coh(X,I) are detected on any open covering. The index `op n`
is positive level `n + 1`; restriction is the usual restriction of module sheaves.
Source: Stacks Project, Lemma 30.23.2 (Tag 087X), locality in part (3).
(blueprint: lem-weil-pbc-coherent-formal-modules-isomorphism-local)

Proof (the node's three steps): Fix a level. The inverses on the cover restrict to
inverses on overlaps, hence agree there by uniqueness of a two-sided inverse.
Glue these maps using lem-weil-pbc-glue-sheaves-of-modules (1). The same uniqueness
clause, applied to the two composites, makes the glued map an inverse globally.
Next, conjugate the compatibility equation for alpha with these inverses to show
that the inverses commute with every transition map. Finally, they define a morphism
of Coh(X,I), by def-weil-pbc-coherent-formal-module; composition and identities are
componentwise, so the two global inverse identities follow. At each level the inverse
is precisely the inverse already constructed, giving the final component identities. -/
theorem coherentFormalModule_isIso_of_isIso_restrict
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    {F G : CoherentFormalModule X I} (α : F ⟶ G)
    (hα : ∀ (j : J) (n : ℕ),
      IsIso ((Scheme.Modules.restrictFunctor (U j).ι).map (α.hom.app (op n)))) :
    IsIso α ∧ ∃ β : G ⟶ F,
      α ≫ β = 𝟙 F ∧ β ≫ α = 𝟙 G ∧
      ∀ n : ℕ, ∃ e : F.obj.obj (op n) ≅ G.obj.obj (op n),
        e.hom = α.hom.app (op n) ∧ e.inv = β.hom.app (op n) := by
  sorry

end AlgebraicGeometry
