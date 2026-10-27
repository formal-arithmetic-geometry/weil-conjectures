/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest

/-!
# A supplied relative bound gives a direct-image Tor interval

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.17,
residue-projection argument; abstract supplied-bound form from the DAG proof.
(blueprint: lem-pur-etale-residue-direct-image-tor-window).

The morphism is arbitrary. The higher-direct-image bound and bounded constructibility
of its derived image are hypotheses. All categories are ordinary small-etale derived
categories with constant finite-level p-adic coefficients.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Use the same quotient-ring instance path as the residue criterion.
attribute [local instance 20000] CommRing.toRing
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory

-- Use the published functor interfaces without unfolding their chosen models.
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor lowerStar finiteConstantProjectionMap

private theorem directImage_tensor_window
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : ℤ) (hc : 0 ≤ c)
    (hcd : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      c < (q : ℤ) → IsZero (((lowerStar (ModuleCat.{u + 1} A) f).rightDerived q).obj M))
    (a b : ℤ) (_hab : a ≤ b) (K : DerivedCategoryModule A X)
    (hupper : ∃ t : ℤ, ∀ i : ℤ, t < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (hTor : DerivedCategory.hasTorAmplitudeIn A X a b K)
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    ∀ i : ℤ, i < a ∨ b + c < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)))) := by
  let G := lowerStar (ModuleCat.{u + 1} A) f
  let R := G.rightDerivedFunctor
  have hnat (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) (hq : c.toNat < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)).obj
        (R.obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))) := by
    exact (hcd F q (by omega)).of_iso
      (G.homologyRightDerivedFunctorObjSingleFunctorIso F q)
  have hheart (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (i : ℤ) (hi : i < 0 ∨ c < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj
        (R.obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))) := by
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ 0).1
        (G.isGE_rightDerivedFunctor_obj_singleFunctor F) i hi
    · obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i := ⟨i.toNat, by omega⟩
      exact hnat F q (by omega)
  let L : DerivedCategoryModule A X :=
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
      ((_root_.DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))
  have hL (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj L) := hTor _ i hi
  have hLa : L.IsGE a := (_root_.DerivedCategory.isGE_iff L a).2
    (fun i hi ↦ hL i (.inl hi))
  have hLb : L.IsLE b := (_root_.DerivedCategory.isLE_iff L b).2
    (fun i hi ↦ hL i (.inr hi))
  have hbounded : _root_.DerivedCategory.TStructure.t.bounded L :=
    ⟨⟨a, hLa⟩, ⟨b, hLb⟩⟩
  have hlo : (R.obj L).IsGE (a + 0) := _root_.DerivedCategory.isGE_obj_of_isGE R 0
    (fun F ↦ G.isGE_rightDerivedFunctor_obj_singleFunctor F) L hbounded a
  have hhi : (R.obj L).IsLE (b + c) := _root_.DerivedCategory.isLE_obj_of_isLE R c
    (fun F ↦ (_root_.DerivedCategory.isLE_iff _ c).2
      (fun i hi ↦ hheart F i (.inr hi))) L hbounded b
  have hRL (i : ℤ) (hi : i < a ∨ b + c < i) :
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj (R.obj L)) := by
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff _ (a + 0)).1 hlo i (by omega)
    · exact (_root_.DerivedCategory.isLE_iff _ (b + c)).1 hhi i hi
  have := isIso_finiteConstantProjectionMap A f c.toNat hnat K hupper M
  intro i hi
  exact (hRL i hi).of_iso
    ((_root_.DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) i).mapIso
      (asIso ((finiteConstantProjectionMap A f K).app M)))

/-- A relative all-sheaf bound `c` enlarges the upper Tor endpoint by at most `c`.
Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.17,
residue-projection argument, with the relative bound and constructibility supplied
explicitly; Stacks Project, Tags 015A, 05TC and 08J5 for the derived heart argument.
(blueprint: lem-pur-etale-residue-direct-image-tor-window).

Proof:
1. Bounded constructibility supplies an upper cohomological bound for `K`. Test
   `hasTorAmplitudeIn` against the constant residue sheaf to put
   `L = K tensor^L kappa_X` in `[a,b]`. The residue module is finite over the
   Noetherian ring `A`, hence finitely presented; no injectivity of multiplication
   by the uniformizer is required (`def-sc-finitely-presented-module`).
2. Apply `lem-sf-projection-finite-constant` with this finitely presented residue
   module and the supplied bound. Noetherianity and boundedness above give
   `Rf_*K tensor^L kappa_Y` isomorphic to `Rf_*L` in the ordinary derived category.
   No flatness or perfectness of the residue module is assumed.
3. Module sheaves are Grothendieck abelian and have enough injectives and K-injective
   resolutions (`lem-weil-pbc-module-sheaves-grothendieck-abelian`,
   `lem-weil-pbc-module-sheaves-enough-injectives`,
   `prop-weil-pbc-kinjective-resolutions-exist`). Direct image is additive and left
   exact (`lem-weil-pbc-module-direct-image-left-exact`), so its right derivation
   is triangulated and commutes with shifts (`lem-pc-right-derived-functor-triangulated`).
   Identify nonnegative heart cohomology with the classical higher direct images
   by `lem-sp-derived-functor-single-identification` and
   `src-right-derived-functor-plus-compatibility`; negative cohomology vanishes by
   `lem-weil-pbc-derived-functor-negative-vanishing`. Thus heart objects map to `[0,c]`.
4. Apply the proved source-library `DerivedCategory.isGE_obj_of_isGE` and
   `DerivedCategory.isLE_obj_of_isLE` to `Rf_*` and the bounded object `L`. The heart
   bounds `[0,c]` give `Rf_*L` in `[a,b+c]` by finite cohomology-triangle induction,
   without an unbounded spectral sequence or a separate bounded-heart wrapper.
5. Transport that interval through the derived isomorphism from Step 2. The assumed
   bounded constructibility of `Rf_*K` permits `lem-exc-residue-tor-test`, giving Tor
   amplitude `[a,b+c]`. By `def-kun-tor-amplitude` this tests every degree-zero module
   sheaf on `Y`, including nonconstant ones. -/
theorem hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    [IsNoetherianRing (Padic.coefficientExtensionRing l E n)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : ℤ) (_hc : 0 ≤ c)
    (_hcd : ∀ (M : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) (q : ℕ),
      c < (q : ℤ) → IsZero
        (((lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
          f).rightDerived q).obj M))
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (_hK : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) X K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) X a b K)
    (_hF : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing l E n) Y
      ((lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        f).rightDerivedFunctor.obj K)) :
    DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a (b + c)
      ((lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        f).rightDerivedFunctor.obj K) := by
  let A := Padic.coefficientExtensionRing l E n
  let M := Padic.coefficientExtensionResidueModule l E n
  have hupper : ∃ t : ℤ, ∀ i : ℤ, t < i →
      IsZero ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj K) := by
    obtain ⟨s, t, _, h⟩ := _hK.2
    exact ⟨t, fun i hi ↦ h i (.inr hi)⟩
  have : Module.Finite A M := by
    dsimp [M, Padic.coefficientExtensionResidueModule]
    infer_instance
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  apply (residue_tor_amplitude_test l E n _hn Y a (b + c) _ _hF).2
  exact directImage_tensor_window A f c _hc _hcd a b _hab K hupper _hTor M

end AlgebraicGeometry.Etale
