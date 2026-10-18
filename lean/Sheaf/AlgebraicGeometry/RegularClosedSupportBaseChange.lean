/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact

/-!
# Regular base change for closed supported etale inverse image

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII, Corollary 4.2.3,
Proposition 4.2.1 and Lemma 4.3.1.1
(blueprint: lem-per-regular-closed-support-base-change).

The support functor and the actual exchange arrow are the published `closedSupportPlus`
and `closedSupportBaseChangePlus`. Finite prime coefficients are lifted only to the value
universe of the small etale site. No constructibility or excellence assumption is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (ell : ℕ) [Fact ell.Prime]

/-- Regular base change makes the fixed support mate invertible. Its naturality is part
of its natural-transformation type; the last equation fixes its supported counit.
Source: ILO XVII, Corollary 4.2.3 (blueprint: lem-per-regular-closed-support-base-change).
Proof:
1. Apply lem-per-regular-supported-base-change at n = 1. Z/ell is F_ell; the coefficient
   lift changes only the universe. The regularity, Noetherianity, invertibility and closed
   immersion hypotheses are exactly those of that theorem.
2. The localization-triangle comparison commutes with the support inclusions. By
   def-weil-pbc-adjunction-mate its transpose is the inverse closed direct-image exchange.
   Thus it is precisely closedSupportBaseChangePlus, with the displayed counit equation.
3. Shifting the localization triangle shifts both its support inclusion and exchange.
   Uniqueness of transposition gives the CommShift assertion. Naturality is already built
   into the mate. No excellence, finite type, compactification or constructibility is used. -/
theorem regular_closedSupport_baseChange
    {Z' Z P X : Scheme.{u}} {q : Z' ⟶ Z} {i' : Z' ⟶ P}
    {i : Z ⟶ X} {r : P ⟶ X} [IsNoetherian X] [IsNoetherian P]
    [IsClosedImmersion i] [IsClosedImmersion i'] [Flat r]
    (hreg : ∀ (x : X) (k : Type u) [Field k] [Algebra (X.residueField x) k]
      [Module.Finite (X.residueField x) k],
      IsRegularScheme (pullback (r.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)))))
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (hP : ∀ p : P, IsUnit (ell : P.presheaf.stalk p))
    (sq : IsPullback q i' i r) :
    IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))
      sq.toCommSq) ∧
    IsIso (closedSupportBaseChangePlus (ULift.{u + 1} (ZMod ell)) sq.toCommSq) ∧
    NatTrans.CommShift
      (closedSupportBaseChangePlus (ULift.{u + 1} (ZMod ell)) sq.toCommSq) ℤ ∧
    ∀ M : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))),
      (derivedBaseChangeMapPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))
          sq.toCommSq).app ((closedSupportPlus (ULift.{u + 1} (ZMod ell)) i).obj M) ≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i').rightDerivedFunctorPlus.map
          ((closedSupportBaseChangePlus (ULift.{u + 1} (ZMod ell)) sq.toCommSq).app M) ≫
        (closedSupportPlusAdjunction (ULift.{u + 1} (ZMod ell)) i').counit.app
          ((upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) r).mapDerivedCategoryPlus.obj M) =
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) r).mapDerivedCategoryPlus.map
        ((closedSupportPlusAdjunction (ULift.{u + 1} (ZMod ell)) i).counit.app M) := by
  sorry

/-- The canonical identification of successive closed supported restrictions, including
its pasted-counit normalization. It applies after localization, so also to successive
point costalks. Source: ILO XVII, Lemma 4.3.1.1; Stacks 0DV0
(blueprint: lem-per-regular-closed-support-base-change). -/
def closedSupportCompPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Z X : Scheme.{u}} (k : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion k] [IsClosedImmersion i] :
    closedSupportPlus A (k ≫ i) ≅ closedSupportPlus A i ⋙ closedSupportPlus A k :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) k)
  (closedSupportPlusAdjunction A (k ≫ i)).rightAdjointUniq
    (((closedSupportPlusAdjunction A k).comp (closedSupportPlusAdjunction A i)).ofNatIsoLeft
      (Functor.rightDerivedFunctorPlusCompIso'
        (lowerStar (ModuleCat.{u + 1} A) k) (lowerStar (ModuleCat.{u + 1} A) i)
        (lowerStarComp (ModuleCat.{u + 1} A) k i)))

/-- Tensor with a coefficient sheaf, using the existing sheaf tensor product.
Source: ILO XVII 4.2.3, Tate-twist compatibility
(blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensor {T : Scheme.{u}}
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :=
  MonoidalCategory.tensorRight L

/-- Additivity is inherited from the existing sheaf tensor functor.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
instance supportTensor_additive {T : Scheme.{u}}
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    (supportTensor ell L).Additive := inferInstanceAs (MonoidalCategory.tensorRight L).Additive

/-- Tensor over the coefficient field preserves finite limits.
Source: ILO XVII 4.2.3, the exact tensor used for twists
(blueprint: lem-per-regular-closed-support-base-change).
Proof: geometric stalks commute with tensor and detect exactness. Each stalk is a vector
space over F_ell, hence flat. Tensor therefore preserves kernels and finite products. -/
@[instance]
theorem supportTensor_preservesFiniteLimits {T : Scheme.{u}}
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    PreservesFiniteLimits (supportTensor ell L) := by
  sorry

/-- Tensor preserves finite colimits, as a left adjoint.
Source: ILO XVII 4.2.3, the exact tensor used for twists
(blueprint: lem-per-regular-closed-support-base-change).
Proof: sheaf tensor is left adjoint to sheaf internal Hom, hence preserves colimits. -/
@[instance]
theorem supportTensor_preservesFiniteColimits {T : Scheme.{u}}
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    PreservesFiniteColimits (supportTensor ell L) := by
  sorry

/-- Exact degreewise tensor on D+. Applied to finiteEtaleTateTwist this is the Tate twist.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorPlus {T : Scheme.{u}}
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :=
  (supportTensor ell L).mapDerivedCategoryPlus

/-- The canonical tensor/pullback comparison, induced by the monoidal inverse image.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorPullback {S T : Scheme.{u}} (f : S ⟶ T)
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    supportTensor ell L ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f ≅
      upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f ⋙
        supportTensor ell ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj L) :=
  (Functor.Monoidal.commTensorRight
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f) L).symm

/-- Derive the exact tensor/pullback comparison, with its representative normalization.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorPullbackPlus {S T : Scheme.{u}} (f : S ⟶ T)
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    supportTensorPlus ell L ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).mapDerivedCategoryPlus ⋙
        supportTensorPlus ell
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj L) :=
  (Functor.mapDerivedCategoryPlusCompIso (supportTensor ell L) _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (supportTensorPullback ell f L) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The ordinary projection map is the mate of monoidal inverse image.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorProjection {Z T : Scheme.{u}} (i : Z ⟶ T)
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i ⋙ supportTensor ell L ⟶
      supportTensor ell
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).obj L) ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i :=
  (mateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i)
    (TwoSquare.mk _ _ _ _ (supportTensorPullback ell i L).hom)).natTrans

/-- Closed projection is invertible on sheaves, including the empty support.
Source: ILO XVII 4.2.3, supported tensor compatibility; Stacks 04CA
(blueprint: lem-per-regular-closed-support-base-change).
Proof: at a geometric point on Z the projection is the identity tensor comparison;
outside Z both sides vanish. Conservative geometric stalks give invertibility. -/
@[instance]
theorem supportTensorProjection_isIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i]
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    IsIso (supportTensorProjection ell i L) := by
  sorry

/-- The derived projection, retaining the exact direct-image and tensor normalizations.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorProjectionPlus {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i]
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).rightDerivedFunctorPlus ⋙
        supportTensorPlus ell L ≅
      supportTensorPlus ell
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).obj L) ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).rightDerivedFunctorPlus :=
  Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _) _ ≪≫
    (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (asIso (supportTensorProjection ell i L)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _).symm

/-- The canonical supported tensor map: mate of the inverse closed projection.
Its transpose is tensor of the supported counit followed by the inverse projection.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorMatePlus {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i]
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    closedSupportPlus (ULift.{u + 1} (ZMod ell)) i ⋙ supportTensorPlus ell
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).obj L) ⟶
      supportTensorPlus ell L ⋙ closedSupportPlus (ULift.{u + 1} (ZMod ell)) i :=
  (mateEquiv (closedSupportPlusAdjunction (ULift.{u + 1} (ZMod ell)) i)
    (closedSupportPlusAdjunction (ULift.{u + 1} (ZMod ell)) i)
    (TwoSquare.mk _ _ _ _ (supportTensorProjectionPlus ell i L).inv)).natTrans

/-- Transport of the tensor endofunctor along a coefficient-sheaf isomorphism.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorTransportPlus {T : Scheme.{u}}
    {L L' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))}
    (e : L ≅ L') : supportTensorPlus ell L ≅ supportTensorPlus ell L' :=
  Functor.mapDerivedCategoryPlusNatIso ((MonoidalCategory.curriedTensor _).flip.mapIso e)

/-- Coefficient transport around a commutative square, through the canonical composition
isomorphisms of ordinary inverse image.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change). -/
def supportTensorSquareIso
    {Z' Z P X : Scheme.{u}} {q : Z' ⟶ Z} {i' : Z' ⟶ P}
    {i : Z ⟶ X} {r : P ⟶ X} (sq : CommSq q i' i r)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) q).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).obj L) ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i').obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) r).obj L) :=
  (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) q i).symm.app L ≪≫
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i' r
      (q ≫ i) sq.w).app L

/-- The coefficient ring is killed by ell, as required by the published finite Tate twist.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change).
Proof: reduce the cast in ULift to ZMod ell, whose characteristic is ell. -/
theorem supportPrimeCoefficient_annihilated :
    (ell : ULift.{u + 1} (ZMod ell)) = 0 := by
  sorry

/-- Supported restriction commutes with every finite roots-of-unity Tate twist, also
when the twisting sheaf is first pulled back to another scheme.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change).
Proof: ell invertible makes the roots-of-unity sheaf locally free of rank one. Its tensor
powers, including degree zero, are invertible. After an etale trivialization the displayed
mate is the identity comparison, by its counit normalization. Descent detects isomorphisms. -/
theorem supportTensorMatePlus_tate_isIso
    {Z S X : Scheme.{u}} (i : Z ⟶ S) (f : S ⟶ X) [IsClosedImmersion i]
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x)) (n : ℕ) :
    IsIso (supportTensorMatePlus ell i
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) f).obj
        (X.finiteEtaleTateTwist ell (ULift.{u + 1} (ZMod ell))
          (supportPrimeCoefficient_annihilated ell) n))) := by
  sorry

/-- The Tate-twist square for the fixed supported exchange, with every edge fixed by
monoidal pullback, closed projection, or supported adjunction. No arbitrary comparison is
chosen. The sheaf L can be the published finiteEtaleTateTwist; the previous theorem makes
both supported tensor edges invertible in that case.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change).
Proof: transpose through the closed adjunction. The tensor/projection adjunction identities,
the closed exchange and tensor naturality reduce both paths to tensor of the same closed
counit. Injectivity of transposition gives the equation. This also applies after restriction
and localization, and the degree-zero twist is the tensor unit. -/
theorem closedSupport_baseChange_tensor
    {Z' Z P X : Scheme.{u}} {q : Z' ⟶ Z} {i' : Z' ⟶ P}
    {i : Z ⟶ X} {r : P ⟶ X} [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : IsPullback q i' i r)
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) q).mapDerivedCategoryPlus.map
        ((supportTensorMatePlus ell i L).app M) ≫
      (closedSupportBaseChangePlus (ULift.{u + 1} (ZMod ell)) sq.toCommSq).app
        ((supportTensorPlus ell L).obj M) =
    (supportTensorPullbackPlus ell q
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).obj L)).hom.app
        ((closedSupportPlus (ULift.{u + 1} (ZMod ell)) i).obj M) ≫
      (supportTensorPlus ell
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) q).obj
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) i).obj L))).map
        ((closedSupportBaseChangePlus (ULift.{u + 1} (ZMod ell)) sq.toCommSq).app M) ≫
      (supportTensorTransportPlus ell (supportTensorSquareIso ell sq.toCommSq L)).hom.app
        ((closedSupportPlus (ULift.{u + 1} (ZMod ell)) i').obj
          ((upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) r).mapDerivedCategoryPlus.obj M)) ≫
      (supportTensorMatePlus ell i'
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) r).obj L)).app
        ((upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))) r).mapDerivedCategoryPlus.obj M) ≫
      (closedSupportPlus (ULift.{u + 1} (ZMod ell)) i').map
        ((supportTensorPullbackPlus ell r L).inv.app M) := by
  sorry

/-- Tensor-inverse coefficient lines give invertible supported tensor mates. This includes
negative Tate twists, interpreted as inverse tensor powers of the roots-of-unity line.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change).
Proof: apply the mate twice, with L and its tensor inverse. The projection and counit
normalizations identify the composite with the unit comparison. The same argument in the
other order gives a two-sided inverse. -/
theorem supportTensorMatePlus_isIso_of_inverse
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))))
    (e : L ⊗ L' ≅ 𝟙_ _) : IsIso (supportTensorMatePlus ell i L) := by
  sorry

/-- Every finite roots-of-unity Tate twist has a tensor inverse when ell is invertible.
This supplies the negative twists without choosing any noncanonical comparison.
Source: ILO XVII 4.2.3 (blueprint: lem-per-regular-closed-support-base-change).
Proof: etale locally choose a primitive ell-th root of unity. The twist is then a free
rank-one coefficient sheaf, whose evaluation pairing with its sheaf dual is invertible.
These evaluation isomorphisms descend and give the asserted inverse. -/
theorem supportTateTwist_tensorInverse (X : Scheme.{u})
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x)) (n : ℕ) :
    ∃ L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell))),
      Nonempty (X.finiteEtaleTateTwist ell (ULift.{u + 1} (ZMod ell))
        (supportPrimeCoefficient_annihilated ell) n ⊗ L' ≅ 𝟙_ _) := by
  sorry

/-- Horizontal pasting of the actual supported mates. In particular this is the pasting
law for regular base changes. Taking either base change to be an open immersion or the
canonical map from a local scheme gives the open-restriction and localization laws.
Source: ILO XVII 4.2.3 and Lemma 4.3.1.1
(blueprint: lem-per-regular-closed-support-base-change).
Proof: the ordinary closed exchange pastes by restriction of sections; its inverse
therefore pastes. Apply mateEquiv_vcomp, then the inverse-image composition isomorphisms.
Equivalently both displayed paths have transpose the twice-pulled-back supported counit.
The proof uses only Cartesian squares, hence includes identity, open and local base changes. -/
theorem closedSupport_baseChange_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z Z₁ Z₂ T T₁ T₂ : Scheme.{u}}
    {i : Z ⟶ T} {i₁ : Z₁ ⟶ T₁} {i₂ : Z₂ ⟶ T₂}
    {h₁ : Z₁ ⟶ Z} {h₂ : Z₂ ⟶ Z₁} {g₁ : T₁ ⟶ T} {g₂ : T₂ ⟶ T₁}
    [IsClosedImmersion i] [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (sq₁ : IsPullback h₁ i₁ i g₁) (sq₂ : IsPullback h₂ i₂ i₁ g₂)
    (M : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (closedSupportBaseChangePlus A (sq₂.toCommSq.horiz_comp sq₁.toCommSq)).app M ≫
        (closedSupportPlus A i₂).map
          ((upperStarCompDerivedPlus (ModuleCat.{u + 1} A) g₂ g₁).hom.app M) =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) h₂ h₁).hom.app
          ((closedSupportPlus A i).obj M) ≫
        (upperStar (ModuleCat.{u + 1} A) h₂).mapDerivedCategoryPlus.map
          ((closedSupportBaseChangePlus A sq₁.toCommSq).app M) ≫
        (closedSupportBaseChangePlus A sq₂.toCommSq).app
          ((upperStar (ModuleCat.{u + 1} A) g₁).mapDerivedCategoryPlus.obj M) := by
  sorry

/-- Vertical pasting with the canonical composition of closed right adjoints. Applying
this after localization and taking k to be the closed-point immersion gives precisely
the supported-composition identification for successive point costalks.
Source: ILO XVII 4.2.3, Lemma 4.3.1.1; Stacks 0DV0
(blueprint: lem-per-regular-closed-support-base-change).
Proof: closedSupportCompPlus identifies right adjoints by their pasted counits. Apply
mateEquiv_hcomp to the two closed adjunctions and their pulled-back adjunctions. The
closed direct-image composition comparison gives the displayed outer square, and
uniqueness of transposition identifies its mate with the two successive support mates.
Horizontal pasting then identifies this same equation before and after localization.
No excellence assumption enters the argument. -/
theorem closedSupport_baseChange_closed_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {W' W Z' Z P X : Scheme.{u}}
    {v : W' ⟶ W} {k' : W' ⟶ Z'} {k : W ⟶ Z} {q : Z' ⟶ Z}
    {i' : Z' ⟶ P} {i : Z ⟶ X} {r : P ⟶ X}
    [IsClosedImmersion k] [IsClosedImmersion k']
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sqk : IsPullback v k' k q) (sqi : IsPullback q i' i r)
    (M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (closedSupportBaseChangePlus A (sqk.toCommSq.vert_comp sqi.toCommSq)).app M ≫
        (closedSupportCompPlus A k' i').hom.app
          ((upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategoryPlus.obj M) =
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.map
          ((closedSupportCompPlus A k i).hom.app M) ≫
        (closedSupportBaseChangePlus A sqk.toCommSq).app ((closedSupportPlus A i).obj M) ≫
        (closedSupportPlus A k').map ((closedSupportBaseChangePlus A sqi.toCommSq).app M) := by
  sorry

end AlgebraicGeometry.Etale
