/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility

/-!
# Finiteness of proper direct images on the small etale site

Source: Stacks Project, Tag 095U (vanishing) and Tag 0GL0 (constructibility), with
identity compactification in the proper case.
(blueprint: lem-weil-pbc-etale-proper-direct-image-finiteness)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Proper direct images of constructible module sheaves are constructible and vanish
above twice the geometric fibre dimension. The Noetherian hypotheses mean finite affine
covers by spectra of Noetherian rings; finite dimensionality permits the empty scheme.
Source: Stacks Project, Tags 095U and 0GL0.
(blueprint: lem-weil-pbc-etale-proper-direct-image-finiteness)

Proof:
1. Finite affine Noetherian covers make X and Y locally Noetherian and quasi-compact
   (pqf-def-locnoeth, lem-sc-affine-noetherian-underlying-space); they are quasi-separated
   by lem-weil-pbc-locally-noetherian-quasi-separated. Properness gives separatedness and
   finite type, hence finite presentation over the locally Noetherian base
   (pqf-lem-lft-fp-locnoeth). The finite ring is Noetherian and annihilated by a positive N.
2. Choose the identity compactification (def-weil-pbc-projection-compactification).
   Identity extension by zero is the identity (def-weil-pbc-extension-by-zero).
   F in degree zero has bounded below constructible cohomology
   (def-weil-pbc-derived-categories, def-weil-pbc-etale-constructible-sheaf).
3. Apply lem-weil-pbc-etale-compactification-constructibility to this compactification.
   Since Rf_! is Rf_*, all higher direct images are constructible
   (def-weil-pbc-direct-image).
4. Every geometric fibre is finite type over an algebraically closed field
   (lem-pod-separated-finite-type-base-change). Embed an algebraic closure of the residue
   field in the geometric field (lem-weil-pbc-algebraic-extension-embeds-algebraically-closed).
   Dimension is unchanged by field extension (lem-sc-fibre-dimension-after-base-change).
   Apply lem-sf-separably-closed-torsion-cd and thm-sc-finite-type-torsion-cd to its
   N-torsion abelian sheaf: cohomology vanishes above 2e (def-sc-etale-torsion-cd).
   Transfer this to module cohomology by lem-weil-pbc-etale-module-cohomology-forget.
   On an empty fibre every module sheaf and all cohomology are zero.
5. Proper base change (cor-weil-pbc-geometric-fiber-finite) identifies geometric stalks
   with fibre cohomology. Sections on an algebraically closed point are stalks
   (lem-weil-pbc-geometric-point-cohomology), hence exact
   (prop-weil-pbc-geometric-stalks-exact). Exactness commutes with cohomology
   (lem-sp-exact-functor-preserves-homology); a pushed-forward injective resolution
   computes the fibre cohomology (def-weil-pbc-direct-image).
6. For q > 2e the underlying abelian higher direct image
   (lem-sbc-higher-direct-image-forget-comparison) has zero geometric stalks, so is zero
   by lemma-weil-pbc-geometric-stalk-conservative. Its module sheaf is therefore zero. -/
theorem proper_directImage_finiteness
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hXdim : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hYdim : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (hfib : ∀ y : Y,
      topologicalKrullDim ↥(pullback f (Y.algClosurePoint y)) ≤ (e : WithBot ℕ∞))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℤ, 0 ≤ q → Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f q F)) ∧
    (∀ q : ℤ, (2 * e : ℤ) < q → IsZero (higherDirectImage Λ f q F)) := by
  classical
  -- The compact-support and torsion bounds do not need these extra hypotheses.
  have _ := hXdim
  have _ := hYdim
  have _ := hΛ
  clear hXdim hYdim hΛ
  let A := ModuleCat.{u + 1} Λ
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  have hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K.obj) := by
    intro q
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    by_cases hq : q = 0
    · subst q
      have : Scheme.IsConstructibleSheaf F :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
      exact Scheme.IsConstructibleSheaf.of_iso (F := F)
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm
    · apply Scheme.IsConstructibleSheaf.of_isZero
      change IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))
      by_cases hneg : q < 0
      · exact ((_root_.DerivedCategory.singleFunctor _ 0).obj F).isZero_of_isGE 0 q hneg
      · exact ((_root_.DerivedCategory.singleFunctor _ 0).obj F).isZero_of_isLE 0 q (by omega)
  refine ⟨?_, ?_⟩
  · intro q _hq
    have hc := isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate
      Λ f (Compactification.ofIsProper f) K hK q
    have e₀ : openImmersionLowerShriek A (𝟙 X) ≅ 𝟭 _ :=
      (upperStarIsoOpenImmersionLowerShriekInv A (Iso.refl X)).symm ≪≫ upperStarId A X
    have e : (rightDerivedLowerShriekOfCompactification A
        (Compactification.ofIsProper f)).obj K.obj ≅
        (lowerStar A f).rightDerivedFunctor.obj K.obj :=
      (lowerStar A f).rightDerivedFunctor.mapIso
        ((Functor.mapDerivedCategoryNatIso e₀ ≪≫ Functor.mapDerivedCategoryIdIso _).app K.obj)
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((lowerStar A f).rightDerivedFunctor.obj K.obj)) := by
      have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hc
      exact Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    exact Scheme.IsConstructibleSheaf.of_iso
      (F := (_root_.DerivedCategory.homologyFunctor _ q).obj
        ((lowerStar A f).rightDerivedFunctor.obj K.obj))
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((lowerStar A f).rightDerivedFunctorPlusCompatibility.app K).symm)
  · intro q hq
    refine isZero_of_forall_isZero_upperStar_algClosurePoint Λ _ fun y ↦ ?_
    let x := Y.algClosurePoint y
    let sq := IsPullback.of_hasPullback f x
    have := isIso_geometricFiber_finite Λ f _ x K
    have hvan := isZero_higherDirectImage_of_two_mul_lt
      (fun z : Λ ↦ isOfFinAddOrder_of_finite z) (pullback.snd f x)
      (pullback.snd f x) (𝟙 _) (Category.comp_id _) e (hfib y)
      ((upperStar A (pullback.fst f x)).obj F) q hq
    refine IsZero.of_iso hvan
      (((upperStar A x).mapDerivedCategoryPlusHomologyFunctorIso q).app
          ((lowerStar A f).rightDerivedFunctorPlus.obj K) ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
          (asIso ((derivedBaseChangeMapPlus A sq.toCommSq).app K)) ≪≫
        (_root_.DerivedCategory.Plus.homologyFunctor _ q).mapIso
          ((lowerStar A (pullback.snd f x)).rightDerivedFunctorPlus.mapIso
            (((upperStar A (pullback.fst f x)).mapDerivedCategoryPlusSingleFunctor 0).app F)))

end AlgebraicGeometry.Etale
