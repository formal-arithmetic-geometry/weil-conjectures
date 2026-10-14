/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation

/-! # Comparing module replacements with the abelian counit lift

Source: Stacks Project, Tags 01FB, 013P, 013S and 03FD.
(blueprint: new-abelian-replacement-section-homotopies)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

/-- Two section-complex homotopies compare a module replacement with the abelian lift.
This asserts no equality involving Ext, and applies to any augmentation-compatible lift.
Source: Stacks Project, Remark 01FB; Tags 013P, 013S and 03FD.
(blueprint: new-abelian-replacement-section-homotopies)

Proof: Write T for forgetting modules, R for the standard abelian injective resolution
of T(F), and r:T(I)→R for forgottenResolutionMap. The inverse-image adjunction is
exact on the left, so direct image preserves abelian injectives. Therefore f_*R is
termwise injective. Forget l to the quasi-isomorphism T(f_*I)→T(K). Lift f_*r
across it up to homotopy into f_*R using the bounded below comparison theorem 013P.
Call the resulting map k:T(K)→f_*R. The augmentation equation for beta and the
augmentation equation for the counit lift show that T(beta) followed by k and
counitResolutionAdjoint have the same localized augmentation. Maps from a resolution
into f_*R with that augmentation are homotopic by 013S. Taking sections and the
restriction identification produces the first homotopy in the assertion. Taking
sections of the lifting homotopy and using ha produces the second one. Let q be
sections of k followed by abelianPushforwardSectionsIso. By 03FD the terms of T(I)
are section-acyclic, so sections of r is a quasi-isomorphism by 015E. The section
map of l is a quasi-isomorphism by the common-section comparison of 01FB. The second
homotopy and the two-out-of-three property imply that q is a quasi-isomorphism.
All choices occur only as existentially quantified maps in this theorem; no
cohomology comparison is defined from an arbitrary existence witness. Empty schemes,
zero coefficients and degree zero need no additional assumptions. -/
theorem abelian_replacement_section_homotopies {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      QuasiIso q ∧
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) ∧
      Nonempty (Homotopy
        ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
          (forgottenResolutionMap X I))) := by sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
