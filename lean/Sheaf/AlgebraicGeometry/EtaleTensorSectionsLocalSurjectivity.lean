/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Local lifting of tensor sections of an epimorphism

Source: Stacks Project, Tags 070S(2), 03FH(1), and 0096.
(blueprint: lem-sc-etale-tensor-sections-local-surjectivity)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Tensor sections of a module epimorphism are locally surjective on the small etale site.
Source: Stacks Project, Descent, Tag 070S(2), and Tag 03FH(1); pullback adjunction
Tag 0096. (blueprint: lem-sc-etale-tensor-sections-local-surjectivity)

Proof: Fix an etale object U and a section of the pullback of H. Tensor pullback
along U to X is a left adjoint, hence takes the epimorphism psi to an epimorphism
of module sheaves on U. Such an epimorphism is locally surjective: its cokernel
is the sheafification of the sectionwise cokernel, so each section of the target
has lifts on a Zariski covering of U. View each open in that covering as an etale
object over X. Pullback along its open immersion agrees with restriction of the
module sheaf. Under this identification, the unit-normalized composition maps
in the tensor-section presheaf identify those lifts with lifts of the restriction
of the original section. Naturality identifies their images under beta with that
restriction. Thus the image sieve contains this etale covering sieve and is
covering. Lifting and lowering a section through ULift does not change its image
sieve. Empty objects and zero modules obey the same local criterion. No
quasi-coherence or flatness is needed. -/
theorem etaleTensorSections_locallySurjective {X : Scheme.{u}} {G H : X.Modules}
    (ψ : G ⟶ H) [Epi ψ]
    (β : etaleTensorSectionsPresheaf G ⟶ etaleTensorSectionsPresheaf H)
    (hβ : ∀ U : X.Etaleᵒᵖ, β.app U = ((tensorPullback U.unop.hom).map ψ).app ⊤) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u}) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
