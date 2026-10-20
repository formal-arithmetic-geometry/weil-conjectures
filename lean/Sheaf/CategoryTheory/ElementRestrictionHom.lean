/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData

import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The closed exact restriction functors on the element site and its further
localizations, including the comparison with the original site-object slices.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4;
sites-cohomology.tex, Tags 08FI and 08JB; sites.tex, Tag 00Y1.
(blueprint: lem-weil-pbc-element-restriction-hom).

Proof: the element-site extension-by-zero functor is exact and left adjoint to
restriction, so restriction preserves K-injectives, as proved already by
presentationElementRestriction_kInjective. It is also left adjoint to
module direct image, hence preserves colimits, and its sectionwise construction
preserves finite limits and addition. At an element (U,s), the further slice is
C/U: the section on an arrow V → U is forced to be s restricted to V. Thus sheaf
Hom restricts sectionwise. Restriction preserves products, so the products and
the differential dφ = d_I φ - (-1)^n φ d_L in the Hom complex restrict as well.
Compute derived Hom with a K-injective target to obtain its natural comparison.
Repeat on an element site for a map B → A. Both successive restrictions evaluate
M at the same underlying U and give the canonical relocalization isomorphism.
Finally the fibre/extension equivalence over the sheafified representable
identifies the ring with R|U, the module restriction with the usual overFunctor,
and their Hom computations. Transport the module operations through this
fibre equivalence to get the indicated exact module equivalence. -/
theorem element_restriction_hom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (s : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
        RingedPresentationCore (presentationElementRing R A) (presentationElementRing R B)
          (elementModulePullbackOver.{u, u} (localCoefficientRings R) b
            (presentationElementRestriction_continuous b))),
      (∀ A : Sheaf J (Type u),
        Nonempty (presentationRHom R ⋙
          presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
            (presentationElementRestriction_additive R A)
            (presentationElementRestriction_exact R A).1
            (presentationElementRestriction_exact R A).2.1 ≅
          ((presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1).op.prod
            (presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1)) ⋙
            presentationRHom (presentationElementRing R A))) ∧
      (∀ {A B : Sheaf J (Type u)} (b : B ⟶ A), (s b).unit = Iso.refl _) ∧
      ∀ U : C,
        ∃ E : RingedPresentationEquivalenceCore (R.over U)
          (presentationElementRing R ((presheafToSheaf J (Type u)).obj (yoneda.obj U))),
          Nonempty (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U ⋙
            E.modules.functor ≅ elementModulePullback.{u, u} (localCoefficientRings R)
              ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) := by
  sorry

end CategoryTheory
