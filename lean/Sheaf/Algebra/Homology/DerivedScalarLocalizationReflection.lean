/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Reflection by derived scalar localization

Source: Stacks Project, Modules on Sites, Tags 03ET, 03CY and 03CZ;
Derived Categories, Tags 015F, 0FND and 09T5; Cohomology on Sites, Tags 06YS and 07A6.
The derived-reflection argument is the agent argument extracted from the returned parent
proof, steps 2–3; it is not a verbatim assertion of Tag 03ET.
(blueprint: lem-sfb-derived-scalar-localization-reflection)
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r wR wS

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

/-- Derived localization is reflective, with the scalar-unit and multiplication normalization
on every complex. The model `m` is the existing universal derived-change-of-rings pair;
its ordinary functor has the prescribed sheafified tensor objects and maps. Thus quantifying
over `m` chooses no new tensor or derived extension. The two module categories may have
independent derived morphism universes.

The ordinary unit and counit formulas use the actual abelian sheafification map on pure
tensors. The natural comparison `c` is the universal counit `m.ε`, now invertible everywhere.
The comparison for restriction is Mathlib's `mapDerivedCategoryFactors`. The two equations
following `c.hom = m.ε` express the derived unit and counit in exactly these identifications.
The equivalence `e` records both the precomposition map and its specified inverse.

Source: Stacks Project, Modules on Sites, Tags 03ET, 03CY, 03CZ; Derived Categories,
Tags 015F, 0FND, 09T5; Cohomology on Sites, Tags 06YS, 07A6.
(blueprint: lem-sfb-derived-scalar-localization-reflection)

Proof:
1. `lem-weil-pbc-scalar-localization-sheaf-exact` gives exactness of actual sheafified
scalar extension, and `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` gives exact
restriction and the ordinary adjunction. Its Hom formula gives the unit `1 ⊗ x` and
multiplication counit `b ⊗ x ↦ b • x` by the balancing relation.
2. `lem-weil-pbc-exact-functor-derived-factorization` and
`lem-weil-pbc-exact-functor-derived-functor` factor both exact termwise functors through
localization, on the full unbounded derived categories. Uniqueness of universal derived
pairs identifies this extension with `m.T`, and its comparison with `m.ε`.
3. Descend the degreewise ordinary unit and counit using
`lem-weil-pbc-localization-universal-property`. The ordinary triangle identities descend
as well, because transformations are determined after precomposition with localization.
4. Compare this adjunction with `lem-pur-sheaf-ring-derived-coefficient-adjunction` on
flat-term K-flat representatives, using the tensor switch if the tensor order is reversed.
The universal comparisons agree. `lem-pc-kflat-resolution` and naturality extend the
unit formula to every complex; essential surjectivity from
`lem-sfb-derived-localization-additive` extends it to every derived object. The unit
fixes the Hom correspondence and hence the counit, proving the two normalization formulas.
5. For an S-module T, the R-linear map j(x) = 1 ⊗ x commutes with the inverse of s,
because multiplication by s is invertible on both sides. It is therefore linear over
the section-localization presheaf, and `lem-pc-sites-module-sheafification-interface`
makes it S-linear. Multiplication composed with j is the identity, and j composed with
multiplication is the identity on pure tensors, hence on their sheafification.
6. These inverse maps commute with differentials. Multiplication is thus invertible on
every complex. The derived counit formula and essential surjectivity show it is an
isomorphism on every object of D(S).
7. The triangle identities and invertibility of the counit give
F(η_A) = ε_(FA)⁻¹, hence UF(η_A) = η_(UFA).
8. Define Ψ(h) = Uε_N ∘ UF(h). Naturality and the right triangle identity give
Ψ(h) ∘ η_A = h. For q : UFA ⟶ UN, step 7 and naturality give
Ψ(q ∘ η_A) = Uε_N ∘ UF(q) ∘ η_(UFA) = q. These are the two inverse equations.
All constructions allow unbounded complexes, the zero ring, and zero or nilpotent s. -/
theorem derivedScalarLocalizationReflection
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (ringedLocalizationRingOfUniverses R s)))] :
    ∃ (_ : PreservesFiniteLimits (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
            (ringedLocalizationRingUnitOfUniverses R s))))
      (_ : PreservesFiniteColimits (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
            (ringedLocalizationRingUnitOfUniverses R s)))),
    ∀ m : DerivedChangeOfRingsCochainModel.{uC, vC, r, wR, wS}
        (ringedLocalizationRingUnitOfUniverses R s),
      PreservesFiniteLimits m.E ∧ PreservesFiniteColimits m.E ∧
      ∃ a : m.E ⊣ restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
            (ringedLocalizationRingUnitOfUniverses R s)),
        (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
          (V : Cᵒᵖ) (x : M.val.obj V),
          ((a.unit.app M ≫ (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                (ringedLocalizationRingUnitOfUniverses R s))).map
                  (eqToHom (m.obj_eq M))).val.app V) x =
            (CategoryTheory.toSheafify J
              (changeOfRingsPresheaf
                (ringedLocalizationRingUnitOfUniverses R s) M).presheaf).app V
              ((1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) ⊗ₜ[R.obj.obj V,
                ((ringedLocalizationRingUnitOfUniverses R s).hom.app V).hom] x)) ∧
        (∀ (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J
              (ringedLocalizationRingOfUniverses R s)))
          (V : Cᵒᵖ) (b : (ringedLocalizationRingOfUniverses R s).obj.obj V)
          (x : N.val.obj V),
          ((eqToHom (m.obj_eq ((restrictScalars
                ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                  (ringedLocalizationRingUnitOfUniverses R s))).obj N)).symm ≫
              a.counit.app N).val.app V)
            ((CategoryTheory.toSheafify J
                (changeOfRingsPresheaf (ringedLocalizationRingUnitOfUniverses R s)
                  ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      (ringedLocalizationRingUnitOfUniverses R s))).obj N)).presheaf).app V
              (b ⊗ₜ[R.obj.obj V,
                ((ringedLocalizationRingUnitOfUniverses R s).hom.app V).hom] x)) = b • x) ∧
        ∃ (d : m.T ⊣ (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory)
          (c : DerivedCategory.Q ⋙ m.T ≅
            m.E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q),
          c.hom = m.ε ∧
          (∀ M : CochainComplex
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ,
            d.unit.app (DerivedCategory.Q.obj M) ≫
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                      (c.hom.app M) ≫
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategoryFactors.hom.app
                      ((m.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
              DerivedCategory.Q.map ((a.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M)) ∧
          (∀ N : CochainComplex (ringedSiteModules.{r}
              (derivedChangeRingIndependentCoefficients J
                (ringedLocalizationRingOfUniverses R s))) ℤ,
            d.counit.app (DerivedCategory.Q.obj N) =
              m.T.map ((restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategoryFactors.hom.app
                      N) ≫
                c.hom.app (((restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj N) ≫
                DerivedCategory.Q.map
                  ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app N)) ∧
          (∀ N : DerivedCategory (ringedSiteModules.{r}
              (derivedChangeRingIndependentCoefficients J
                (ringedLocalizationRingOfUniverses R s))), IsIso (d.counit.app N)) ∧
          (∀ (A : DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)))
            (N : DerivedCategory (ringedSiteModules.{r}
              (derivedChangeRingIndependentCoefficients J
                (ringedLocalizationRingOfUniverses R s)))),
            ∃ e : ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj
                        (m.T.obj A) ⟶
                    (restrictScalars
                      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                        (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj N) ≃
                  (A ⟶ (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj N),
              (∀ q, e q = d.unit.app A ≫ q) ∧
              (∀ h, e.symm h =
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                      (m.T.map h) ≫
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                      (d.counit.app N))) ∧
          (∀ A : DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)),
            (restrictScalars
                ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                  (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                    (m.T.map (d.unit.app A)) =
              d.unit.app ((restrictScalars
                ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                  (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj
                    (m.T.obj A))) := by
  sorry

end SheafOfModules
