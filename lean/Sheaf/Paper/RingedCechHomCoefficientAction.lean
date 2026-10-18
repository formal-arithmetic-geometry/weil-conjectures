/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.FlatRingedCechBaseChange
public import Sheaf.CategoryTheory.RingedCompletionUnit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap

/-! # The target-ring action on a derived Hom complex

Source: Stacks Project, algebraization.tex, Tag 099I.
(blueprint: lem-weil-pbc-ringed-cech-hom-coefficient-action).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The internal Hom from a restricted B-complex has a B-action by precomposition.
An augmented comparison identifies its evaluation with the R-completion unit.
This assertion concerns arbitrary augmented complexes; it assumes neither flatness,
finite generation, quotient isomorphism nor local completeness.

Source: Stacks Project, algebraization.tex, Tag 099I, construction of E prime and the
last displayed composite, with its omitted compatibility expanded.
(blueprint: lem-weil-pbc-ringed-cech-hom-coefficient-action).

Proof: choose the functorial K-injective replacement q_E of an R-complex E and form
Hom_R(r KB, I(E)). Give it the B-action (b h)(k) = h(b k). The action laws follow from
those on KB and commutativity of B; restrictions commute with this action, and its
linearity for the Hom differential follows from d(b k) = b d(k). Functorial replacement
maps induce B-linear Hom maps. Naturality of q and two-out-of-three make a replacement
of a quasi-isomorphism a quasi-isomorphism between K-injective complexes. Hom invariance
therefore makes these Hom maps quasi-isomorphisms, also over B since restriction leaves
underlying additive cohomology unchanged. Localize to obtain F. Forgetting the B-action
identifies rF with RHom_R(r KB,-). Precomposition with the quasi-isomorphism u gives the
natural isomorphism theta with RHom_R(K,-).
For a B-complex M, send homogeneous m to the cochain k -> q(epsilon_B(k)m), with zero
components when k has degree other than zero. This is B-linear by the stated action.
The chain-map equation follows from epsilon_B d = 0 and d q = q d, including the possible
degree minus one contribution, which vanishes. These maps are natural in complexes and
descend by localization to beta. Precomposing with u gives
x -> q(phi(epsilon(x))m) = epsilon(x) q(m), by augmentation compatibility. This is exactly
the cochain defining the completion unit, including the canonical evaluation-at-one
identification in ringedDerivedHomUnit. It gives the asserted equation in the derived
category. For KB = 0 or K = 0 the Hom functors and maps are zero, and the same equations
hold; there is no boundedness or completeness assumption to check. -/
theorem ringed_cech_hom_coefficient_action
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))]
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ))]
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (KB : ringedSiteComplex B) (εB : KB ⟶ ringedSiteRingComplex B)
    (u : K ⟶ ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj KB)
    (hu : QuasiIso u)
    (hε : u ≫ ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map εB = ε ≫ siteRingComplexScalarUnit φ) :
    let r : ringedSiteDerived B ⥤ ringedSiteDerived R :=
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory
    ∃ (F : ringedSiteDerived R ⥤ ringedSiteDerived B)
      (θ : F ⋙ r ≅ ringedCechCompletionFunctor R K)
      (β : 𝟭 (ringedSiteDerived B) ⟶ r ⋙ F),
      ∀ M : ringedSiteDerived B,
        r.map (β.app M) ≫ θ.hom.app (r.obj M) =
          ringedCechCompletionUnit R K ε (r.obj M) := by
  sorry

end CategoryTheory
