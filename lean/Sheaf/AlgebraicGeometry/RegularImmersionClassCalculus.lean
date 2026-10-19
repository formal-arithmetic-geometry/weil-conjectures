/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Supported Kummer classes of regular closed immersions

Source: ILO, Exposé XVI, §§2.1--2.3, especially Definition 2.3.1 and Theorem 2.3.2;
§3.2 and Propositions 3.3.1--3.3.2; Stacks, Tag 03Q6
(blueprint: lem-per-regular-immersion-class-calculus).

Classes are represented by Ext from the exact closed direct image of the coefficient sheaf.
The extra integer parameter is tensoring with a Tate line, so Yoneda composition expresses
exceptional transitivity without choosing another exceptional functor. All comparisons below
are the existing normalized root, tensor and direct-image comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The coefficient ring, lifted to the small-etale coefficient universe.
Source: ILO XVI 2.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
abbrev regularClassCoefficients (ℓ n : ℕ) := ULift.{u + 1} (ZMod (ℓ ^ n))

/-- The annihilation used by the existing finite Tate sheaf construction.
Source: ILO XVI 2.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
abbrev regularClassAnnihilation (ℓ n : ℕ) :
    ((ℓ ^ n : ℕ) : regularClassCoefficients.{u} ℓ n) = 0 :=
  congrArg (ULift.up : ZMod (ℓ ^ n) → regularClassCoefficients.{u} ℓ n)
    (ZMod.natCast_self (ℓ ^ n))

/-- The published signed finite Tate sheaf at this prime-power coefficient level.
Source: ILO XVI 2.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
abbrev regularClassTwist (ℓ n : ℕ) (X : Scheme.{u}) (a : ℤ) :=
  Scheme.finiteEtaleTateSheaf (regularClassCoefficients.{u} ℓ n) (ℓ ^ n) X
    (regularClassAnnihilation ℓ n) a

/-- The canonical pullback comparison already characterized on roots and their tensor powers.
The cited existence theorem determines these maps by its root-inclusion, pure-tensor,
constant, recursion and evaluation equations; this choice does not select arbitrary maps.
Source: Stacks 03PK, 03Q1; ILO XVI 2.3
(blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassTwistPullback (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)))
    (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) f).obj
      (regularClassTwist ℓ n Y a) ≅ regularClassTwist ℓ n X a :=
  (Scheme.finiteEtaleTwistPullbackData (regularClassCoefficients.{u} ℓ n) (ℓ ^ n)
    (pow_pos hℓ.pos n) (regularClassAnnihilation ℓ n)).c f hY hX a

/-- The existing normalized signed multiplication of Tate lines, fixed by unitors,
positive recursion, associativity and evaluation on dual lines.
Source: ILO XVI 1; Stacks 03PK (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassTwistProduct (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    (X : Scheme.{u}) (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (a b : ℤ) :
    regularClassTwist ℓ n X a ⊗ regularClassTwist ℓ n X b ≅
      regularClassTwist ℓ n X (a + b) :=
  (Scheme.finiteEtaleTwistPullbackData (regularClassCoefficients.{u} ℓ n) (ℓ ^ n)
    (pow_pos hℓ.pos n) (regularClassAnnihilation ℓ n)).p X hX a b

/-- Tensoring with a Tate line is exact, using its published normalized tensor inverse.
This instance merely supplies the exactness evidence required by Ext.mapExactFunctor.
Source: ILO XVI 1; Stacks 03PK (blueprint: lem-per-regular-immersion-class-calculus). -/
abbrev regularClassTwistTensorRightExact (ℓ : ℕ) (hℓ : Fact ℓ.Prime) (n : ℕ)
    (X : Scheme.{u}) (hX : Fact (IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))) (a : ℤ) :
    PreservesFiniteLimits (tensorRight (regularClassTwist ℓ n X a)) :=
  (ObjectProperty.flat_of_tensorIso
    (regularClassTwistProduct ℓ hℓ.out n X hX.out a (-a) ≪≫
      eqToIso (congrArg (regularClassTwist ℓ n X) (add_neg_cancel a)))).2.1

/-- A supported class and all its signed Tate tensors, in the ordinary etale categories.
Regularity is tested on the support, so empty and codimension-zero immersions are included.
Source: ILO XVI Definition 2.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
def RegularImmersionClassFamily (ℓ : ℕ) : Type (u + 1) :=
  ∀ (n : ℕ) (_hn : 1 ≤ n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (_hreg : IsStalkRegularClosedImmersion i c) (_hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (a : ℤ),
    Ext ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
      (regularClassTwist ℓ n Z a)) (regularClassTwist ℓ n X ((c : ℤ) + a)) (2 * c)

/-- The canonical map from a Tate line to its direct image, using the actual adjunction.
Source: ILO XVI 2.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassTwistUnit (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))
    (hZ : IsUnit ((ℓ ^ n : ℕ) : Γ(Z, ⊤))) (a : ℤ) :
    regularClassTwist ℓ n X a ⟶
      (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
        (regularClassTwist ℓ n Z a) :=
  (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).homEquiv _ _
      (regularClassTwistPullback ℓ hℓ n i hX hZ a).hom

/-- The projection on a supported constant tensored with a Tate line. This is assembled
from the actual adjunction unit and the actual lax monoidal direct-image tensorator.
Source: ILO XVI 2.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassProjection (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))
    (hZ : IsUnit ((ℓ ^ n : ℕ) : Γ(Z, ⊤))) (a : ℤ) :
    ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
      (regularClassTwist ℓ n Z 0)) ⊗ regularClassTwist ℓ n X a ⟶
      (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
        (regularClassTwist ℓ n Z a) :=
  tensorHom (𝟙 _) (regularClassTwistUnit ℓ hℓ n i hX hZ a) ≫
    Functor.LaxMonoidal.μ
      (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i) _ _ ≫
    (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).map
      (λ_ (regularClassTwist ℓ n Z a)).hom

/-- The canonical closed exchange, including its Tate pullback comparison.
Source: ILO XVI 2.2.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassExchange (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (v : X' ⟶ X) (w : Z' ⟶ Z) (sq : CommSq w i' i v)
    (hZ : IsUnit ((ℓ ^ n : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ n : ℕ) : Γ(Z', ⊤))) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) v).obj
      ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
        (regularClassTwist ℓ n Z a)) ⟶
      (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i').obj
        (regularClassTwist ℓ n Z' a) :=
  (baseChangeMap (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) sq).app _ ≫
    (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i').map
      (regularClassTwistPullback ℓ hℓ n w hZ hZ' a).hom

/-- Apply exact tensoring to the supported class. The exactness evidence is extracted from
its tensor inverse, rather than added as a hypothesis on the immersion or coefficients.
Source: ILO XVI 2.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassTensorMap (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (c : ℕ)
    (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (a : ℤ)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
        (regularClassTwist ℓ n Z 0)) (regularClassTwist ℓ n X c) (2 * c)) :
    Ext
      (((lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
        (regularClassTwist ℓ n Z 0)) ⊗ regularClassTwist ℓ n X a)
      (regularClassTwist ℓ n X c ⊗ regularClassTwist ℓ n X a) (2 * c) :=
  letI : PreservesFiniteLimits (tensorRight (regularClassTwist ℓ n X a)) :=
    regularClassTwistTensorRightExact ℓ ⟨hℓ⟩ n X ⟨hX⟩ a
  κ.mapExactFunctor (tensorRight (regularClassTwist ℓ n X a))

/-- Tensor normalization: every signed variant is the original supported class tensored
with the specified Tate line, through the canonical projection and multiplication.
Source: ILO XVI 2.3.1--2.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def RegularClassTensorNormalization (ℓ : ℕ) (hℓ : ℓ.Prime)
    (classes : RegularImmersionClassFamily.{u} ℓ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (hreg : IsStalkRegularClosedImmersion i c)
    (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (hZ : IsUnit ((ℓ ^ n : ℕ) : Γ(Z, ⊤))) (a : ℤ),
    (Ext.mk₀ (regularClassProjection ℓ hℓ n i hX hZ a)).comp
        (classes n hn i c hreg hX a) (zero_add (2 * c)) =
      (regularClassTensorMap ℓ hℓ n i c hX a (classes n hn i c hreg hX 0)).comp
        (Ext.mk₀ (regularClassTwistProduct ℓ hℓ n X hX c a).hom) (add_zero (2 * c))

/-- Cartier classes are exactly the relative supported Kummer boundaries. Their unit
composites are the positive Kummer Chern classes by ordinary_supported_kummer.
For codimension zero the class is the unique inclusion of the open-and-closed summand.
Source: ILO XVI 2.1, 2.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def RegularClassNormalization (ℓ : ℕ)
    (classes : RegularImmersionClassFamily.{u} ℓ) : Prop :=
  (∀ (n : ℕ) (hn : 1 ≤ n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hreg : IsStalkRegularClosedImmersion i 0)
    (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))),
    ∃ e : (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i).obj
        (regularClassTwist ℓ n Z 0) ⟶ regularClassTwist ℓ n X 0,
      e ≫ supportedConstantUnit (regularClassCoefficients.{u} ℓ n) i = 𝟙 _ ∧
      classes n hn i 0 hreg hX 0 = Ext.mk₀ e) ∧
  (∀ (n : ℕ) (hn : 1 ≤ n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hreg : IsStalkRegularClosedImmersion i 1) (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))),
    SupportedKummerBoundary (regularClassCoefficients.{u} ℓ n) (ℓ ^ n)
      (regularClassAnnihilation ℓ n) i hI hX (classes n hn i 1 hreg hX 0))

/-- Exceptional transitivity expressed in the equivalent supported Hom groups: exact
closed direct image followed by Yoneda composition. The canonical direct-image comparison
is precomposed, and addition of twists and degrees is displayed explicitly.
Iterating this clause along a regular-generator Cartier flag is precisely its Kummer formula;
normalization makes it independent of the generators and their order.
Source: ILO XVI Theorem 2.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def RegularClassComposition (ℓ : ℕ)
    (classes : RegularImmersionClassFamily.{u} ℓ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) {Z Y X : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (c d : ℕ) (hi : IsStalkRegularClosedImmersion i c)
    (hj : IsStalkRegularClosedImmersion j d)
    (hji : IsStalkRegularClosedImmersion (i ≫ j) (d + c))
    (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (hY : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤))) (a : ℤ),
    (Ext.mk₀ ((lowerStarComp
        (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) i j).inv.app
          (regularClassTwist ℓ n Z a))).comp
      (((classes n hn i c hi hY a).mapExactFunctor
          (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) j)).comp
        ((classes n hn j d hj hX ((c : ℤ) + a)).comp
          (Ext.mk₀ (eqToHom (congrArg (regularClassTwist ℓ n X)
            (by omega : (d : ℤ) + ((c : ℤ) + a) = ((d + c : ℕ) : ℤ) + a))))
          (add_zero (2 * d)))
        (by omega : 2 * c + 2 * d = 2 * (d + c)))
      (zero_add (2 * (d + c))) =
      classes n hn (i ≫ j) (d + c) hji hX a

/-- Flat pullback of pairs, with the canonical closed exchange and normalized Tate maps.
Open restriction and affine local or strict-local restriction are included because those
maps are flat; no compact-support adjoint for a localization morphism is postulated.
Source: ILO XVI 2.2.3.1, §3.2; Stacks 03Q6
(blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def RegularClassFlatBaseChange (ℓ : ℕ) (hℓ : ℓ.Prime)
    (classes : RegularImmersionClassFamily.{u} ℓ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) {Z Z' X X' : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian Z'] [IsNoetherian X] [IsNoetherian X']
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (v : X' ⟶ X) [Flat v] (w : Z' ⟶ Z) (sq : IsPullback w i' i v) (c : ℕ)
    (hi : IsStalkRegularClosedImmersion i c) (hi' : IsStalkRegularClosedImmersion i' c)
    (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤))) (hX' : IsUnit ((ℓ ^ n : ℕ) : Γ(X', ⊤)))
    (hZ : IsUnit ((ℓ ^ n : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ n : ℕ) : Γ(Z', ⊤))) (a : ℤ),
    IsIso (regularClassExchange ℓ hℓ n i i' v w sq.toCommSq hZ hZ' a) ∧
    (Ext.mk₀ (regularClassExchange ℓ hℓ n i i' v w sq.toCommSq hZ hZ' a)).comp
        (classes n hn i' c hi' hX' a) (zero_add (2 * c)) =
      ((classes n hn i c hi hX a).mapExactFunctor
          (upperStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)) v)).comp
        (Ext.mk₀ (regularClassTwistPullback ℓ hℓ n v hX hX' ((c : ℤ) + a)).hom)
        (add_zero (2 * c))

/-- The actual reduction of prime-power coefficient rings.
Source: ILO XVI 3.3.1 (blueprint: lem-per-regular-immersion-class-calculus). -/
def regularClassReduction (ℓ n N : ℕ) (h : n ≤ N) :
    regularClassCoefficients.{u} ℓ N →+* regularClassCoefficients.{u} ℓ n :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ n))).comp ULift.ringEquiv.toRingHom)

/-- The section of the constant coefficient sheaf represented by a scalar.
Source: ILO XVI 1 (blueprint: lem-per-regular-immersion-class-calculus). -/
def regularClassConstantGenerator (ℓ n : ℕ) (X : Scheme.{u}) (U : X.Etaleᵒᵖ)
    (r : regularClassCoefficients.{u} ℓ n) : (regularClassTwist ℓ n X 0).obj.obj U :=
  (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
    (ModuleCat.of (regularClassCoefficients.{u} ℓ n) (regularClassCoefficients.{u} ℓ n)))).app U r

/-- Multiplication of local Tate sections: first the tensor of sections, then sheafification,
then the published signed Tate multiplication. This fixes all dual comparisons as well.
Source: ILO XVI 1 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def regularClassTwistMultiply (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ)
    (X : Scheme.{u}) (hX : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))
    (a b : ℤ) (U : X.Etaleᵒᵖ) (x : (regularClassTwist ℓ n X a).obj.obj U)
    (y : (regularClassTwist ℓ n X b).obj.obj U) :
    (regularClassTwist ℓ n X (a + b)).obj.obj U :=
  (regularClassTwistProduct ℓ hℓ n X hX a b).hom.hom.app U
    ((Functor.LaxMonoidal.μ
      (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ n)))
      (regularClassTwist ℓ n X a) (regularClassTwist ℓ n X b)).app U
        (x ⊗ₜ[regularClassCoefficients.{u} ℓ n] y))

/-- Reduction comparisons are fixed by scalar reduction, the root power map, and signed
multiplication. Taking degrees `a` and `-a` in the last equation is exactly preservation of
the perfect evaluation pairing, so it specifies the dual comparisons for negative twists.
Source: ILO XVI 3.3.1--3.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def RegularClassReductionComparisons (ℓ : ℕ) (hℓ : ℓ.Prime) (n N : ℕ) (h : n ≤ N)
    (X : Scheme.{u}) (hXn : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))
    (hXN : IsUnit ((ℓ ^ N : ℕ) : Γ(X, ⊤)))
    (q : X.rootsOfUnitySheaf (ℓ ^ N) ⟶ X.rootsOfUnitySheaf (ℓ ^ n))
    (t : ∀ a : ℤ, regularClassTwist ℓ N X a ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology (regularClassReduction ℓ n N h)).obj
        (regularClassTwist ℓ n X a)) : Prop :=
  q ≫ kernel.ι ((ℓ ^ n) • 𝟙 X.gmSheaf) =
    (ℓ ^ (N - n)) • kernel.ι ((ℓ ^ N) • 𝟙 X.gmSheaf) ∧
  (∀ (U : X.Etaleᵒᵖ) (r : regularClassCoefficients.{u} ℓ N),
    (t 0).hom.app U (regularClassConstantGenerator ℓ N X U r) =
      regularClassConstantGenerator ℓ n X U (regularClassReduction ℓ n N h r)) ∧
  (∀ (U : X.Etaleᵒᵖ) (r : regularClassCoefficients.{u} ℓ N)
      (z : (X.rootsOfUnitySheaf (ℓ ^ N)).obj.obj U),
    (t 1).hom.app U
        (Scheme.finiteEtaleTateOneGenerator (regularClassCoefficients.{u} ℓ N) (ℓ ^ N) X
          (regularClassAnnihilation ℓ N) U r z) =
      Scheme.finiteEtaleTateOneGenerator (regularClassCoefficients.{u} ℓ n) (ℓ ^ n) X
        (regularClassAnnihilation ℓ n) U (regularClassReduction ℓ n N h r) (q.hom.app U z)) ∧
  (∀ (a b : ℤ) (U : X.Etaleᵒᵖ)
      (x : (regularClassTwist ℓ N X a).obj.obj U)
      (y : (regularClassTwist ℓ N X b).obj.obj U),
    (t (a + b)).hom.app U (regularClassTwistMultiply ℓ hℓ N X hXN a b U x y) =
      regularClassTwistMultiply ℓ hℓ n X hXn a b U
        ((t a).hom.app U x) ((t b).hom.app U y))

/-- The supported coefficient square uses restriction of scalars, not an assumed invertible
comparison between reduction and exceptional inverse image on arbitrary complexes.
The comparison maps are fully normalized on constants, roots, tensor powers and duals.
Source: ILO XVI 3.3.1--3.3.2 (blueprint: lem-per-regular-immersion-class-calculus). -/
@[irreducible]
def RegularClassCoefficientReduction (ℓ : ℕ) (hℓ : ℓ.Prime)
    (classes : RegularImmersionClassFamily.{u} ℓ) : Prop :=
  ∀ (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (h : n ≤ N),
    ∃ (q : ∀ (X : Scheme.{u}) [IsNoetherian X],
        X.rootsOfUnitySheaf (ℓ ^ N) ⟶ X.rootsOfUnitySheaf (ℓ ^ n))
      (t : ∀ (X : Scheme.{u}) [IsNoetherian X] (a : ℤ),
        regularClassTwist ℓ N X a ⟶
          (Sheaf.restrictScalars X.smallEtaleTopology (regularClassReduction ℓ n N h)).obj
            (regularClassTwist ℓ n X a)),
      (∀ (X : Scheme.{u}) [IsNoetherian X]
        (hXn : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))
        (hXN : IsUnit ((ℓ ^ N : ℕ) : Γ(X, ⊤))),
        RegularClassReductionComparisons ℓ hℓ n N h X hXn hXN (q X) (t X)) ∧
      (∀ {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
        (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
        (hi : IsStalkRegularClosedImmersion i c)
        (hXn : IsUnit ((ℓ ^ n : ℕ) : Γ(X, ⊤)))
        (hXN : IsUnit ((ℓ ^ N : ℕ) : Γ(X, ⊤))) (a : ℤ),
        (Ext.mk₀ ((lowerStar
            (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ N)) i).map (t Z a))).comp
          ((classes n hn i c hi hXn a).mapExactFunctor
            (Sheaf.restrictScalars X.smallEtaleTopology (regularClassReduction ℓ n N h)))
          (zero_add (2 * c)) =
        (classes N hN i c hi hXN a).comp (Ext.mk₀ (t X ((c : ℤ) + a)))
          (add_zero (2 * c)))

/-- The complete regular-immersion class calculus. The signed variants are constrained
by tensor normalization; they are not independent classes or extra mathematical data.
Source: ILO XVI 2.3.1--2.3.2, §3.2, 3.3.1--3.3.2
(blueprint: lem-per-regular-immersion-class-calculus). -/
def RegularImmersionClassLaws (ℓ : ℕ) (hℓ : ℓ.Prime)
    (classes : RegularImmersionClassFamily.{u} ℓ) : Prop :=
  RegularClassNormalization ℓ classes ∧
  RegularClassTensorNormalization ℓ hℓ classes ∧
  RegularClassComposition ℓ classes ∧
  RegularClassFlatBaseChange ℓ hℓ classes ∧
  RegularClassCoefficientReduction ℓ hℓ classes

/-- The canonical supported Kummer classes of regular closed immersions, simultaneously
at all positive prime-power levels and with all their signed Tate tensors.

Source: ILO XVI, Definition 2.3.1, Theorem 2.3.2, §3.2 and Propositions 3.3.1--3.3.2;
Stacks, Tag 03Q6 (blueprint: lem-per-regular-immersion-class-calculus).

Proof plan (the DAG proof, with its construction preceding the local formula):
1. For positive codimension use the conormal bundle from
   lem-per-regular-flag-blowup-geometry and its modified-blowup class from
   lem-per-modified-blowup-generalized-class. Its unique pullback is G(Q); thus the
   construction is global. Use lem-amb-closed-support-hom and the exceptional adjoint
   thm-amb-etale-exceptional-adjoint to transpose it. In degree zero use the clopen summand.
2. For a Cartier divisor the modified blowup is X and Q = -1. Hence the class is
   -e(I,1) = e(O(D),1), the SupportedKummerBoundary of lem-asd-ordinary-supported-kummer.
   Its unit composite is the positive Chern class.
3. Translate composition by supported Hom and lem-cat-right-adjoint-composition.
   Zero codimensions are the clopen restriction law.
4. For positive codimensions first treat an outer Cartier divisor. Blow up the inner
   support, using lem-per-regular-flag-blowup-geometry and the supported injection of
   lem-per-modified-blowup-generalized-class.
5. Split the pulled-back divisor class using the trivialized-line factorization. The
   pseudo-divisor identities in lem-per-noetherian-supported-product-calculus give
   the two terms G((-1)^(m+1)c_m(F)) and G((c_1(K)-ξ)S_F).
6. Whitney in lem-per-noetherian-etale-chern-identities gives
   Q_H = (c_1(K)-ξ)S_F + (-1)^(m+1)c_m(F). Injectivity proves Cartier composition.
7. Blow up the outer support for general composition. Its excess conormal kernels
   pull back to one another, and the excess formula introduces c_(n-1)(K dual).
8. Apply the Cartier case upstairs, then the projection and associativity identities
   of lem-per-noetherian-supported-product-calculus. The same supported injection descends
   the composition equation. This is the displayed Yoneda equation under transitivity.
9. Iterate along a regular-generator flag, using def-weil-pbc-regular-sequence. Every factor
   is the normalized Cartier Kummer class; every regular reordering gives that same class.
10. Flat base change preserves the regular sequence and its conormal. Apply the generalized
    class base-change formula and lem-asd-etale-finite-twist-pullback. Open restriction follows.
11. Apply lem-per-ind-etale-closed-support-base-change at local and strict-local schemes.
    The pair and its complement have the continuity identifications of
    lemma-weil-pbc-etale-cohomology-continuity; their shifted cones identify supported groups.
    Step 10 identifies the pulled-back fixed finite-stage class under these comparisons.
12. Reduction preserves the blowup polynomial and pseudo-divisor boundary by
    lem-per-noetherian-etale-chern-identities and lem-per-noetherian-supported-product-calculus.
    The supported injection identifies the reduced class with the class at the smaller level.
    lem-asd-etale-finite-twist-pullback fixes the root power map, tensors and dual comparisons.
    Tensoring determines all signed variants, including identity and equal-coefficient cases.
    STATEMENT-DISPUTED: full uniqueness in the displayed laws still needs an argument.
    ILO XVI 2.2.2.3 and 2.2.2.7 prove uniqueness with prescribed blowup image G(Q).
    To conclude the asserted uniqueness, show that any system satisfying these laws has
    that image; neither local equality of derived morphisms nor semi-purity for singular X
    supplies this implication. Construction uniqueness alone does not discharge this step.
-/
theorem regular_immersion_class_calculus (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃! classes : RegularImmersionClassFamily.{u} ℓ, RegularImmersionClassLaws ℓ hℓ classes := by
  sorry

end AlgebraicGeometry.Etale
