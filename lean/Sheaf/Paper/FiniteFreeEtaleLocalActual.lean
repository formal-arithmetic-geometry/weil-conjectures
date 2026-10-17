/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Homotopy
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
import Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.SiteRestrictionExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact

/-!
# Local chain representatives for finite free constant complexes

Source: Stacks Project, sites-cohomology.tex, Tag 08FR, assertions (1) and (2)
(blueprint: lem-weil-pbc-finite-free-etale-local-actual).

Constant coefficients are expressed as sheaves valued in `ModuleCat B`, the usual
constant-ring-module encoding. Étale inverse image is restriction to the localized site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Derived maps from a bounded finite free constant complex have local chain
representatives, and a chain map vanishing in the derived category is locally homotopic
to zero. Source: Stacks Project, Tag 08FR (lemma-local-actual), assertions (1) and (2)
(blueprint: lem-weil-pbc-finite-free-etale-local-actual).

Proof:
1. Sheafify finite bases termwise. Finite coproducts and zero terms are preserved, so
   the constant source is bounded with finite free terms. Finite-free internal Hom is
   exact, including rank zero (lem-sc-finite-free-internal-hom-exact-sequence).
2. Resolve the arbitrary target by a K-injective complex. Boundedness of the source and
   exactness of its termwise Hom functors make the induced Hom-complex map a
   quasi-isomorphism (lem-pc-bounded-exact-term-hom-quasi-iso).
3. Degree-zero cohomology of sections of the Hom complex consists of chain maps modulo
   homotopy. Exact sheafification identifies its associated sheaf with internal Hom
   cohomology. The map to the resolved target is therefore locally bijective
   (lem-weil-pbc-site-sheafification-iso-locally-bijective); the exact forgetful functor
   compares module cohomology with abelian sheaf cohomology.
4. Identify the site localized at an étale object with its small étale site. Exact
   restriction preserves quasi-isomorphisms and homotopies, and induces derived
   restriction (lem-weil-pbc-etale-site-localization-open,
   lem-weil-pbc-site-restriction-exact).
5. Represent a derived morphism into the K-injective resolution by a chain map.
   Local surjectivity from step 3 gives chain representatives into the original target;
   cancel the restricted resolution quasi-isomorphism in the derived category.
6. If a chain map is zero after localization, its composite into the resolution is
   null-homotopic by the K-injective Hom bijection. Local injectivity from step 3 makes
   its original homotopy class zero locally, giving a single homotopy on every cover
   member. Its components satisfy alpha^i = d_F h^i + h^(i+1) d_P simultaneously.
-/
theorem finiteFree_etale_local_actual
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (P : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (P.X n ≅ ModuleCat.of B (Fin r → B)))
    (F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
    (∀ φ : DerivedCategory.Q.obj
        (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶ DerivedCategory.Q.obj F,
      ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
        ∃ α :
          (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ⟶
          (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F),
          DerivedCategory.Q.map α =
            (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapDerivedCategoryFactors.inv.app
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapDerivedCategory.map φ ≫
            (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapDerivedCategoryFactors.hom.app F) ∧
    (∀ α :
        (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶ F,
      DerivedCategory.Q.map α = 0 →
      ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
        Nonempty (Homotopy
          (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) 0)) := by
  sorry

end AlgebraicGeometry
