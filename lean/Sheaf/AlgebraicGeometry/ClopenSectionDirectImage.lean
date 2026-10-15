/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Direct image from an open and closed section

Source: blueprint, sec-smooth-purity/sk-def-sf-operations,
lemma lem-weil-pbc-clopen-section-direct-image
(blueprint: lem-weil-pbc-clopen-section-direct-image).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Restriction to an open and closed section gives `Rp_* s_! ≅ id` on bounded below
étale derived categories with finite coefficients. Source: blueprint,
sec-smooth-purity/sk-def-sf-operations, lemma lem-weil-pbc-clopen-section-direct-image
(blueprint: lem-weil-pbc-clopen-section-direct-image).

The equation characterizes the canonical isomorphism: after the unit identifying `K`
with `s^* s_! K`, its component is restriction along `s`, namely the derived unit for
`s^* ⊣ s_*`, followed by `Rp_* Rs_* ≅ R(ps)_* ≅ id`.

Proof: (1) Split V into the image of s and its open complement. Apply
lem-weil-pbc-etale-sheaf-clopen-product to abelian sheaves; scalar endomorphisms and
ring identities are componentwise, so this also gives the module-sheaf equivalence.
(2) In this product s_! is insertion (F,0), by
lem-weil-pbc-extension-by-zero-adjunction. It is also right adjoint to the exact first
projection, so lem-sp-right-adjoint-preserves-injectives shows it preserves injectives.
Its exactness is lem-weil-pbc-extension-by-zero-exact.
(3) For every étale W over X, use lem-weil-pbc-etale-inverse-image-restriction to evaluate
s_!F on V ×_X W. Its two components are W and the complement, with sections F(W) and
zero. Restriction gives p_*s_!F ≅ F, naturally in both W and F, including scalar actions.
(4) Use lem-weil-pbc-module-sheaves-enough-injectives and
lem-weil-pbc-dplus-injective-representative to represent K by a bounded below injective
complex I. Then s_!I is again bounded below injective. By
lem-weil-pbc-right-derived-plus-injective, Rp_*s_!K is represented by p_*s_!I ≅ I.
(5) The degreewise restriction commutes with differentials and the derived comparison.
The Hom bijection of lem-weil-pbc-kinjective-hom-derived proves naturality on derived
morphisms and independence of I. The adjunction unit is restriction to the component,
which gives the displayed characterization. -/
theorem clopenSectionDirectImage (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X V : Scheme.{u}} (p : V ⟶ X) (s : X ⟶ V) [IsOpenImmersion s]
    (hs : IsClosed (Set.range s.base)) (hsp : s ≫ p = 𝟙 X) :
    ∃ e : (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p ≅
          𝟭 (DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        @Eq
          (((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ⟶
          ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)))
          (e.hom.app K ≫
            (Functor.mapDerivedCategoryPlusIdIso
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).inv.app K ≫
            (Functor.mapDerivedCategoryPlusNatIso
              (asIso (openImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} Λ) s).unit)).hom.app K ≫
            (Functor.mapDerivedCategoryPlusCompIso
              (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
              (upperStar (ModuleCat.{u + 1} Λ) s)).hom.app K)
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map
            ((Adjunction.derivedPlus
              (L := upperStar (ModuleCat.{u + 1} Λ) s)
              (R := lowerStar (ModuleCat.{u + 1} Λ) s)
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s)).unit.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ≫
          (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (lowerStar (ModuleCat.{u + 1} Λ) s) (lowerStar (ModuleCat.{u + 1} Λ) p) _ _ _ _
            (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s))
            (lowerStarComp (ModuleCat.{u + 1} Λ) s p (𝟙 X) hsp.symm)).hom.app
              ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
                ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj K)) ≫
          (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
              ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.obj
                K))) := by
  sorry

end AlgebraicGeometry.Etale
