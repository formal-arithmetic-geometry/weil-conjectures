/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-! # Unbounded compact-support site transport

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/prose-07-01.md,
conventions paragraph on transport by `ν^*`
(blueprint: lem-sfb-unbounded-compact-support-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open AlgebraicGeometry Scheme

set_option maxHeartbeats 1600000 in
-- The composite crosses both localized sheaf categories and their derived functors.
/-- The unbounded compact-support comparison is the counit mate for the proper factor,
followed by the degreewise canonical extension-by-zero comparison.
Source: prose-07-01 transport paragraph
(blueprint: lem-sfb-unbounded-compact-support-transport). -/
def unboundedCompactSupportComparison
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L) :=
  unboundedDirectImageComparisonMap A c.g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj L) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
      ((Functor.mapDerivedCategorySquareIso
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i)).hom.app L)

set_option maxHeartbeats 1600000 in
-- Elaborating the two routes involves the expanded derived tensor and pullback instances.
/-- Both canonical maps commute with unbounded compact-support comparison.
Source: prose-07-01 transport paragraph
(blueprint: lem-sfb-unbounded-compact-support-transport).

Proof: Write b_p for the specified unbounded direct-image counit mate and e_j for the
localized, degreewise open-extension comparison. Then C_c = Rp_*(e_j) after b_p. The first
factor is invertible by unbounded direct-image comparison and the second by the exact open
comparison. Naturality of these two maps gives the second conjunct.

For projection, apply ringed exchange/tensor coherence to the square formed by p on the
two sites and the two comparison morphisms. The exchange of this square is b_p: both are
transposes of the pullback comparison followed by the etale counit. The coherence identity
therefore says that b_p commutes with the proper projection mates. Paste this identity
with the open-extension tensor coherence for e_j. Use the composition coherence of the
pullback comparisons to identify the composite inverse image with f^{-1}, and naturality
of the proper projection map to move e_j through it. The resulting left route is C(PF_e),
then C_c at the tensor, then F_p(h); the right route is t_Y, then C_c tensor identity, then
PF_p. These are the third conjunct's two sides.

For exchange, first compare the proper exchange square with b_p. Transpose both routes
under the base-changed proper adjunction. Substitute the counit equation defining each b
and the unit-square-counit equation defining each exchange. Move the etale counit through
the pullback comparison by naturality. The remaining equality is precisely composition
coherence of pullback comparison with the Cartesian square identification. The adjunction
bijection is injective, so the proper square commutes, without inverting an exchange map.

The open base-change comparison commutes with e_j on bounded-below inputs by open exchange
transport. Apply this to a sheaf in degree zero and take H^0 to obtain the sheaf identity.
Every functor and every map of this open square is exact and degreewise, so the identity
holds on arbitrary complexes and descends to the unbounded derived category. Paste this
open square with the proper square just proved. Naturality of proper exchange at e_j and
of b_{p'} at the open base-change map changes the left route into C(E_e), then C_{c'}, then
F_{c'}(a_w); the right route becomes a_v, then v_p^{-1}(C_c), then E_p. This is the fourth
conjunct. All the constituent maps are natural, so both equations are natural in every
input. No step uses a bound, constructibility, Tor amplitude, flatness, or an inverse of
PF or E. For empty X or zero inputs the same composites are maps between zero objects.
-/
theorem unboundedCompactSupportTransport
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ : A) ^ r = 0)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f) [QuasiCompact c.i]
    {X' Y' : Scheme.{u}} {w : X' ⟶ X} {f' : X' ⟶ Y'} {v : Y' ⟶ Y}
    [Y'.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y' ↘ Spec (CommRingCat.of k))]
    [v.IsOver (Spec (CommRingCat.of k))]
    (sq : IsPullback w f' f v) :
    (∀ L : Etale.DerivedCategoryModule A X,
      IsIso (unboundedCompactSupportComparison A c L)) ∧
    (∀ (L L' : Etale.DerivedCategoryModule A X) (a : L ⟶ L'),
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a) ≫
        unboundedCompactSupportComparison A c L' =
      unboundedCompactSupportComparison A c L ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map a)) ∧
    (∀ (M : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y),
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K) ≫
        unboundedCompactSupportComparison A c
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
            ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (projectionComparisonTargetIso A f M K).inv =
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          (ModuleCat.{u + 1} A)
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).hom.app
            K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          (unboundedCompactSupportComparison A c M)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K) ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj K)) ∧
    (∀ (L : Etale.DerivedCategoryModule A X),
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y').mapDerivedCategory.map
          ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} A) sq c).app L) ≫
        unboundedCompactSupportComparison A (c.ofIsPullback sq)
          ((Etale.upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.obj L) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback sq)).map ((projectionComparisonPullbackIso A w).inv.app L) =
      (projectionComparisonPullbackIso A v).inv.app
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L) ≫
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
          (unboundedCompactSupportComparison A c L) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale
