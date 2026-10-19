/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.UnboundedProperOpenInterchange
public import Sheaf.AlgebraicGeometry.OpenSectionClopen
public import Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import Sheaf.AlgebraicGeometry.DerivedCounitKInjectiveTermwise
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The adjoint of proper/open refinement is the component projection

Source: Stacks Project, Tag 0F7B, lemma-shriek-proper-and-open, with the clopen-section
calculation of the blueprint (blueprint: lem-asd-proper-open-refinement-adjoint-projection).

The sheaf projection and its descent are specified by their component and localization
formulas. In particular, the projection is characterized independently of the derived mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The comparison of Tag 0F7B for the refinement square, with the identity direct-image
compositor inserted. The selected witness has the K-injective normalization in
`unboundedProperOpenInterchange`; this is not a choice of an unnormalized isomorphism.
Source: Stacks Project, Tag 0F7B
(blueprint: lem-asd-proper-open-refinement-adjoint-projection). -/
def unboundedProperOpenRefinementComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    D((j₂)_!open[ModuleCat.{u + 1} A]) ≅
      D((j₁)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm) _ ≪≫
    (unboundedProperOpenInterchange A).choose_spec.choose j₁ (𝟙 U) p j₂
      ⟨h.trans (Category.id_comp j₂).symm⟩

/-- The clopen-section projection is natural, descends degreewise to all unbounded
complexes, and is the adjoint of the specified proper/open comparison.
Source: Stacks Project, Tags 0F7B, 03S6, 01KT and 015F; explicit clopen calculation in
(blueprint: lem-asd-proper-open-refinement-adjoint-projection).

Proof:
1. Form W = V₁ ×[V₂] U. The lift (j₁,id) is an open section of W → U.
   The latter is proper by proper base change, hence separated. By open_section_clopen,
   W splits into the section and its complementary open. Open-extension base change
   identifies p* j₂! M with extension from W of the pullback of M. The finite clopen
   sheaf decomposition defines its projection: identity on the section and zero on
   the complement. It is natural in M. The first displayed formula expresses identity
   on the section using the inverse-image compositor and the two open units; the
   second expresses zero on every disjoint open, including the complementary component.
2. Exact inverse image and exact extension by zero preserve quasi-isomorphisms.
   Apply the projection degreewise and descend through localization. The third formula
   specifies this descent on every complex, without any bound.
3. Choose K-injective J on U and a K-injective resolution rho: j₁!J → I.
   The normalized comparison is j₂!J = p_*j₁!J → p_*I. The canonical derived
   counit at QI is represented by the ordinary counit p*p_*I → I
   (lem-asd-derived-counit-k-injective-termwise). Naturality along rho reduces its
   composite with the comparison to the ordinary counit composite at j₁!J.
   Proper-support composition identifies j₂!M = p_*j₁!M. Restricting to W gives
   q*q_*s_*M → s_*M for the section s and projection q, with qs = id. Under the
   clopen sheaf decomposition this is identity on s(U) and zero on its complement,
   precisely the projection of step 1, with the inverse base-change normalization.
   Outside W both maps vanish. Naturality and resolution independence give the final
   equality of natural transformations on the entire unbounded derived category. -/
theorem properOpenRefinement_adjoint_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V₁ V₂ : Scheme.{u}} [IsNoetherian U] [IsNoetherian V₁] [IsNoetherian V₂]
    (p : V₁ ⟶ V₂) [IsProper p] (j₁ : U ⟶ V₁) (j₂ : U ⟶ V₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ p = j₂) :
    ∃ (π : (j₂)_!open[ModuleCat.{u + 1} A] ⋙ (p)^*[ModuleCat.{u + 1} A] ⟶
        (j₁)_!open[ModuleCat.{u + 1} A])
      (Dπ : D((j₂)_!open[ModuleCat.{u + 1} A]) ⋙ D((p)^*[ModuleCat.{u + 1} A]) ⟶
        D((j₁)_!open[ModuleCat.{u + 1} A])),
      (∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        (j₁)^*[ModuleCat.{u + 1} A].map (π.app M) =
          (upperStarComp (ModuleCat.{u + 1} A) j₁ p j₂ h.symm).inv.app
              ((j₂)_!open[ModuleCat.{u + 1} A].obj M) ≫
            inv ((openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j₂).unit.app M) ≫
            (openImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) j₁).unit.app M) ∧
      (∀ (C : Scheme.{u}) (c : C ⟶ V₁) [IsOpenImmersion c],
        Disjoint (Set.range c) (Set.range j₁) →
          ∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
            (c)^*[ModuleCat.{u + 1} A].map (π.app M) = 0) ∧
      (∀ J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        D((p)^*[ModuleCat.{u + 1} A]).map
            (((j₂)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J) ≫
          ((p)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((j₂)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app J) =
        Dπ.app (DerivedCategory.Q.obj J) ≫
          ((j₁)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J) ∧
      Functor.whiskerRight (unboundedProperOpenRefinementComparison A p j₁ j₂ h).hom
          D((p)^*[ModuleCat.{u + 1} A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft D((j₁)_!open[ModuleCat.{u + 1} A])
          (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit ≫
        (Functor.rightUnitor _).hom = Dπ := by
  sorry

end AlgebraicGeometry.Etale
