/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Edge compatibility for the resolution-normalized comparison

Source: Stacks Project, Tags 03FD, 01FB and 01F7.
(blueprint: new-module-cohomology-ext-resolution-edge)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- The concrete resolution comparison intertwines the direct-image edge map.
This asserts an equality for the constructed `moduleCohomologyExtResolutionEquiv`,
not for arbitrary natural equivalences.
Source: Stacks Project, Tag 03FD, Lemma 21.12.4; Tag 01FB, Remark 20.14.2;
Tag 01F7, Section 20.14.
(blueprint: new-module-cohomology-ext-resolution-edge)

Proof: Let D be the choices defining moduleCohomologyFMap f (identity).
Its resolutions I of F and J of f_*F, injective replacement K of f_*I,
and augmentation lift beta give the section diagram in 01FB. The canonical
restriction at f inverse(Y)=X is D.a, fixed by D.sections. The vertical map
mu=D.a followed by sections(lambda) induces an isomorphism by D.invertible.
Forgotten injective module terms are acyclic on every open by 03FD, hence
compute the same derived abelian direct image and its global sections.
The comparison used in moduleCohomologyExtResolutionEquiv is the inverse of
the augmentation-preserving acyclic-resolution comparison, so it may be
computed on I and J instead of the standard resolutions: lift identities
between these resolutions and apply homotopy invariance and acyclic-comparison
naturality. Thus the section diagram also computes Ext cohomology after
forgetting modules. Under the free-abelian-terminal-source isomorphism,
evaluation at the identity generator becomes evaluation at 1. Exact abelian
inverse image and its counit therefore calculate that same diagram: applying
inverse image to an Ext class and then postcomposing with coeff(f,identity)
is the canonical abelian cohomology map of the identity f-map. Its section map
is restriction at f inverse(Y)=X, with precisely the constant-sheaf comparison
constIso(f).symm. Both maps compose with H(mu) to H(sections(beta)); cancel the
invertible H(mu). Transport back using the resolution isomorphisms. Independence
of augmentation lifts follows from homotopy invariance. This uses neither
exact module pullback nor acyclicity of f_*F; in degree zero it is the same
section identity, including empty schemes and zero coefficients. -/
theorem moduleCohomologyExtResolutionEquiv_edge
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)
    (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj
      ((pushforward f).obj F)) :
    moduleCohomologyExtResolutionEquiv X F p (moduleCohomologyEdgeMap f F p x) =
      Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p
          (moduleCohomologyExtResolutionEquiv Y ((pushforward f).obj F) p x)) := by sorry

end AlgebraicGeometry.Scheme.Modules
