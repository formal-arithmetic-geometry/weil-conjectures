/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Injective models for global sections with closed pro-etale support

Source: Stacks Project, etale-cohomology.tex, Tags 09XQ and 09XP, with the ordinary
pro-etale module adaptation in the DAG proof
(blueprint: lem-pur-proetale-injective-support-global-model).

Constant-coefficient module sheaves use the published `Sheaf ... (ModuleCat A)`
presentation. The comparison with the intrinsic constant-ring presentation is the
one in `ProEtaleFiniteModules`. The equality of section complexes is expressed by
its natural, inclusion-normalized isomorphism, since the chosen categorical kernels
and the global-section limit need not have definitionally identical carriers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The closed supported inverse image is right adjoint to exact closed direct image,
preserves injectives, and computes supported global cohomology on injective models.

The first equality fixes the sheaf counit. The natural isomorphism `c` identifies
`Γ(Z,i^!₀(-))` with the actual kernel-of-restriction functor; its normalization says
that the identification followed by the kernel inclusion is global sections of the
support counit, using `Γ(Z,-) ≅ Γ(X,i_*(-))` and evaluation at the terminal object.
Applying `c` termwise gives the displayed equality of complexes, with the induced
differentials and naturality in every chain map.

The isomorphism `e` is the consequent natural derived comparison. The last equation
normalizes it on every bounded-below injective representative by the three standard
right-derived units. Their invertibility states both model computations. Applying
`DerivedCategory.Plus.homologyFunctor (ModuleCat A) r` to `e` gives the comparison
of cohomology modules in every integer degree, including negative degrees.

Source: Stacks Project, Tags 09XQ (Hom argument) and 09XP (supported sections),
and the ordinary pro-etale adaptation in this node
(blueprint: lem-pur-proetale-injective-support-global-model).

Proof, following the seven steps of the node:
1. On the stated small sites the module-sheaf categories are Grothendieck abelian
by lem-weil-pbc-ring-sheaves-grothendieck, hence have enough injectives by
lem-sp-grothendieck-enough-injectives. All functors here are additive.
2. For N on Z, every map i_*N → M has zero composite with the open adjunction unit,
since j^*i_*N = 0 by lem-weil-pbc-proetale-ringed-open-closed. Factor uniquely through
G_ZM = ker(M → j_*j^*M). The canonical isomorphism q:G_ZM ≅ i_*i^!₀M of
def-pur-flasque-support and full faithfulness of closed direct image from
lem-exc-proetale-closed-fully-faithful give the natural Hom adjunction. Its counit
is q⁻¹ followed by the kernel inclusion, precisely supportModelInclusion.
3. Exactness of i_* and lem-sp-right-adjoint-preserves-injectives imply preservation
of injective objects by i^!₀. Additivity preserves every lower bound. Termwise
application gives the differential i^!₀(d), so its square is zero.
4. Apply lem-weil-pbc-right-derived-plus-injective first to i^!₀ and then to Γ(Z,-).
The first image complex is again bounded below and injective, so both derived units
are invertible. Thus Γ(Z,i^!₀I) computes RΓ(Z,SK).
5. The direct-image formula of def-weil-pbc-proetale-operations identifies sections
on Z with those of i_* on X. The inverse of q identifies the latter with sections
of G_ZI. Its section formula from def-pur-flasque-support is exactly the kernel of
I(X) → I(U), namely def-pur-support-cohomology. This gives c with its displayed
normalization. Naturality of q, restriction, and direct image makes these comparisons
commute with all differentials and all chain maps, without splittings or sign changes.
6. Apply lem-weil-pbc-right-derived-plus-injective to Γ_Z(X,-). Its derived unit
is invertible on I. Invert the first two units, apply the chain identification from
step 5, then apply this third unit; the resulting comparison is e.
7. By lem-weil-pbc-dplus-injective-representative every D⁺ object has such a model.
By lem-weil-pbc-kinjective-hom-derived a derived map is represented by a unique
homotopy class of maps between injective models. Additive functors preserve homotopies;
step 5 commutes with them. Hence e is independent of representatives and lifts and is
natural on D⁺. Apply degree-r cohomology to obtain an isomorphism of A-modules. -/
theorem proEtaleInjectiveSupportGlobalModel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hPair : IsCompl (Set.range i) (Set.range j)) :
    ∃ adj : lowerStar (ModuleCat.{u + 1} A) i ⊣ finiteClosedUpperShriek A i j,
      adj.counit = supportModelInclusion A i j hPair ∧
      (finiteClosedUpperShriek A i j).PreservesInjectiveObjects ∧
      ∃ c : finiteClosedUpperShriek A i j ⋙
          Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ≅ supportSections i A,
        (∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
          c.hom.app M ≫ kernel.ι (M.obj.map (supportRestrictionArrow i).op) =
            (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).inv.app
                ((finiteClosedUpperShriek A i j).obj M) ≫
              (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
                ((supportModelInclusion A i j hPair).app M) ≫
              (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
                (ModuleCat.{u + 1} A) (Scheme.ProEt.isTerminalMkId X)).hom.app M) ∧
        ∃ e : (finiteClosedUpperShriek A i j).rightDerivedFunctorPlus ⋙
            (Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus ≅ derivedSupportSections i A,
          ∀ I : HomotopyCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
            (∀ r : ℤ, Injective (I.obj.as.X r)) →
            (∀ n : ℤ, CochainComplex.IsStrictlyGE I.obj.as n →
              CochainComplex.IsStrictlyGE
                (((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                  I.obj.as) n) ∧
            (∀ r : ℤ, Injective
              ((((finiteClosedUpperShriek A i j).mapHomologicalComplex (.up ℤ)).obj
                I.obj.as).X r)) ∧
            IsIso ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ∧
            IsIso ((Sheaf.Γ (Scheme.ProEt.topology Z)
              (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I)) ∧
            IsIso ((supportSections i A).rightDerivedFunctorPlusUnit.app I) ∧
            (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlusUnit.app
                ((finiteClosedUpperShriek A i j).mapHomotopyCategoryPlus.obj I) ≫
              (Sheaf.Γ (Scheme.ProEt.topology Z)
                (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
                ((finiteClosedUpperShriek A i j).rightDerivedFunctorPlusUnit.app I) ≫
              e.hom.app (DerivedCategory.Plus.Qh.obj I) =
              DerivedCategory.Plus.Qh.map
                ((Functor.mapHomotopyCategoryPlusCompIso c).hom.app I) ≫
                (supportSections i A).rightDerivedFunctorPlusUnit.app I := by
  sorry

end AlgebraicGeometry.ProEtale
