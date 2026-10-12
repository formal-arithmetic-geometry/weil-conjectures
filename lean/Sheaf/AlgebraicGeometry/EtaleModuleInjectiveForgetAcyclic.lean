/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion
import Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic

/-!
# Underlying abelian acyclicity of injective module-valued étale sheaves

Source: Stacks Project, Cohomology on Sites, Tag 03FD, second paragraph of its proof.
(blueprint: lem-weil-pbc-etale-module-injective-forget-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian sheaf of an injective module-valued étale sheaf is acyclic
for global sections. Its underlying abelian sheaf need not be injective.
Source: Stacks Project, Tag 03FD, second paragraph, via Tags 03FC and 03F9.
(blueprint: lem-weil-pbc-etale-module-injective-forget-acyclic).

Proof:
1. Identify sheaves valued in `ModuleCat Λ` with modules over the constant ring sheaf.
Global scalars act sectionwise. Conversely, sections of the constant ring sheaf are
locally represented by scalars; act using representatives and glue. Local equality
makes the action independent of representatives. The sheaf condition proves the
module identities and the inverse equivalence. The equivalence commutes with the
underlying abelian sheaf and preserves injectives.
2. On every object and every covering of the small étale site, positive Čech cohomology
of an injective module sheaf is zero. Use the ringed-site injective-module Čech theorem:
its free Čech chain complex is exact in positive degrees, and Hom into an injective
presheaf of modules is exact. Forgetting module actions leaves the same section groups,
restriction maps, and Čech differential.
3. Apply the abelian Čech vanishing criterion with all étale objects and all covering
families. All covering objects and fibre products belong to this collection, and each
covering refines itself. Step 2 supplies the Čech vanishing hypothesis. Hence positive
right derived evaluation of the underlying abelian sheaf vanishes on every object.
4. The identity of `Y` is terminal in the small étale site. Evaluation there is naturally
abelian global sections; transport the vanishing through this natural isomorphism of
left exact functors and their right derived functors. Take degree `n + 1`. -/
theorem isZero_rightDerived_globalSections_forget_of_injective
    (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G] (n : ℕ) :
    IsZero (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      (n + 1)).obj ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)) := by
  sorry

end AlgebraicGeometry.Scheme
