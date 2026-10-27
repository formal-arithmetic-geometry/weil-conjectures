/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Category.Preorder

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Hom from a finitely presented module on a qcqs algebraic space

Source: Stacks Project, Cohomology of Spaces, Tag 07U7
(blueprint: lem-sfb-space-fp-module-hom-colimit).

The diagram is in all module sheaves on the small étale site. The canonical comparison
is the descent map of the Hom cocone, so its value at a stage is postcomposition with
the specified colimit coprojection.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Hom from a locally finitely presented module commutes with directed colimits, with
stagewise factorization and equality at a common upper stage.
Source: Stacks Project, Cohomology of Spaces, Tag 07U7; Modules on Sites, Tags 0GMZ and 0GN0
(blueprint: lem-sfb-space-fp-module-hom-colimit).

Proof:
1. Form the internal Hom sheaves Hom(G,M_i) using def-pur-sheaf-hom. Their global
   sections are module morphisms. The size convention supplies small models of the
   étale site and its slices. Apply lem-cbc-sieve-module-sheafification with integers
   and lem-weil-pbc-site-sheafification-iso-locally-bijective on these sites. Forgetting
   commutativity preserves ring sheaves since sections and unique gluings coincide.
2. A nonempty directed preorder is filtered. Apply
   lem-weil-pbc-site-finite-presentation-internal-hom-colimit to G, identifying the
   colimit of these internal Homs with Hom(G,c.pt). The comparison sends a local map
   g to g followed by the specified coprojection, as in Stacks Tag 0GMZ.
3. By lem-weil-pbc-module-sheaves-colimits-forgetful the underlying abelian sheaf is
   the corresponding abelian colimit. Apply lem-sfb-space-cohomology-filtered-colimit
   in degree zero, using quasi-compactness and the absolute diagonal hypothesis.
   Global sections are additive and left exact; identify their zeroth derived functor
   with global sections by lem-weil-pbc-left-exact-injective-resolution-degree-zero.
4. Compose this global-section comparison with that of step 2. It is exactly the
   displayed colimit.desc, since both send g at stage i to g followed by c.ι.app i.
   Apply lem-weil-pbc-abelian-groups-forget-filtered-colimits and
   lem-weil-pbc-filtered-colimit-sets-elementwise to obtain bijectivity, stage
   representatives, and equality at a common later stage. No quasi-coherence of the
   diagram terms is used. -/
theorem finitePresentation_hom_directed_colimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [CompactSpace (Point X.obj.obj)] (hqs : IsAbsolutelyQuasiSeparated X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ X.Modules) (c : Cocone D) (hc : IsColimit c)
    (G : X.Modules) [G.IsFinitePresentation] :
    Function.Bijective
      (colimit.desc (D ⋙ coyoneda.obj (op G)) ((coyoneda.obj (op G)).mapCocone c)) ∧
      (∀ f : G ⟶ c.pt, ∃ (i : I) (g : G ⟶ D.obj i), g ≫ c.ι.app i = f) ∧
      (∀ (i j : I) (g : G ⟶ D.obj i) (h : G ⟶ D.obj j),
        g ≫ c.ι.app i = h ≫ c.ι.app j →
        ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
          g ≫ D.map (homOfLE hik) = h ≫ D.map (homOfLE hjk)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
