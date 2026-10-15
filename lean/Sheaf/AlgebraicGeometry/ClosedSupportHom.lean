/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.CategoryTheory.KInjectiveTotalDerived

/-!
# Closed support as a relative section complex

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md (blueprint: lem-amb-closed-support-hom).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Ordinary global derived Hom from `i_* A_D` is the shifted cone of restriction of
ordinary derived global sections to the complementary open. The existential `q` is fixed
in every degree by the existing global-section pullback map, so is not an arbitrary arrow.
The cone is computed on the functorial K-injective resolution, and the final equation is
naturality in every map of complexes. Both sides invert quasi-isomorphisms, hence this
also expresses naturality on the derived category. No boundedness is assumed.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-closed-support-hom.md
(blueprint: lem-amb-closed-support-hom).

Proof:
1. Apply lem-weil-pbc-open-closed-short-exact to the constant coefficient sheaf, obtaining
   `0 → v_! A_V → A_T → i_* A_D → 0`. Inverse image identifies the coefficient sheaves
   (prop-weil-pbc-inverse-image-modules-exact). No finite-type assumption on v is needed.
2. The module sheaf category is Grothendieck abelian
   (lem-weil-pbc-module-sheaves-grothendieck-abelian). Use the functorial, degreewise injective
   K-injective resolution of lem-pur-kinjective-degreewise-existence.
3. Apply Hom into each injective term to get a short exact sequence of complexes C → E → B
   (def-sp-injective-resolutions). Extension-by-zero adjunction identifies B with sections
   of v^*I, and maps from the rank-one constant sheaf identify E with sections of I
   (lem-weil-pbc-extension-by-zero-adjunction, def-weil-pbc-constant-sheaf and
   def-weil-pbc-global-sections-functor). The map E → B is precisely restriction.
4. Exactness of v_! and the adjunction make v^* preserve K-injectives
   (lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-right-adjoint-preserves-kinjective).
   Thus E and B compute RΓ(T,K) and RΓ(V,v^*K), and C computes ordinary RHom, by
   lem-weil-pbc-kinjective-total-derived.
5. For a degreewise surjection q:E → B, inclusion c ↦ (0,c) gives a quasi-isomorphism
   C → Cone(q)[-1]. With differential (b,e) ↦ (-d_B b-q(e),d_E e), lift -b to a in E to
   reduce any cocycle to (0,e-d_E a). If (0,c) is a boundary of (b,e), lift b to a and
   then c=d_E(e+d_E a) in C. This proves bijectivity on cohomology. The inclusion commutes
   with all resolution maps, giving the displayed naturality. By
   lem-weil-pbc-kinjective-hom-derived, quasi-isomorphisms between the resolutions are
   homotopy equivalences. A homotopy h induces on shifted cones H(b,e)=(-h_B b,h_E e);
   its off-diagonal term is -q' h_E+h_B q=0. Thus both sides and the comparison descend
   to the localization of complexes (def-weil-abstract-derived-category).
-/
theorem closedSupportHom (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    ∃ q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ),
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (n : ℤ), (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n)) ∧
      ∃ e : ∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (f : K ⟶ L),
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).map (DerivedCategory.Q.map f) ≫
          (e L).hom =
        (e K).hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (-1 : ℤ)).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm)) := by
  sorry

end AlgebraicGeometry.Etale
