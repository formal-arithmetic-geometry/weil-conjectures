/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularSupportedClassOperations
public import WeilConjectures.AlgebraicGeometry.StalkRegularClosedImmersion
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement

/-! # Normalized regular-immersion class systems

Source: ILO, Expose XVI 2.1--2.3 and 3.2--3.3; Stacks Project, Tag 03Q6
(blueprint: def-per-regular-immersion-class-system).

Prime-power coefficients, normalized families, and their exact composition, flat
restriction and reduction laws.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

/-- The coefficient ring Z/ell^n, lifted to the universe of ordinary etale modules.
Source: ILO XVI 3.3 (blueprint: def-per-regular-immersion-class-system). -/
abbrev regularClassCoefficient (ell n : ℕ) := ULift.{u + 1} (ZMod (ell ^ n))

set_option linter.defProp false in
/-- The annihilator proof for these actual coefficients.
Source: ILO XVI 3.3 (blueprint: def-per-regular-immersion-class-system). -/
def regularClassAnnihilator (ell n : ℕ) :
    ((ell ^ n : ℕ) : regularClassCoefficient.{u} ell n) = 0 :=
  congrArg (ULift.up : ZMod (ell ^ n) → regularClassCoefficient.{u} ell n)
    (ZMod.natCast_self (ell ^ n))

set_option linter.defProp false in
/-- Invertibility of the coefficient exponent on the scheme.
Source: ILO XVI 3.3 (blueprint: def-per-regular-immersion-class-system). -/
def regularClassExponentUnit (ell n : ℕ) (T : Scheme.{u})
    (h : IsUnit (ell : Γ(T, ⊤))) : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)) :=
  cast (congrArg IsUnit (Nat.cast_pow ell n).symm) (h.pow n)

/-- Pure tensor of sections of the actual sheaf tensor product.
Source: ILO XVI 2.1 (blueprint: def-per-regular-immersion-class-system). -/
def regularClassPureTensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : T.Etaleᵒᵖ)
    (x : F.obj.obj W) (y : G.obj.obj W) : (F ⊗ G).obj.obj W :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} A)) F G).app W) (x ⊗ₜ[A] y)

/-- The actual reduction ring map, including equal levels.
Source: ILO XVI 3.3.1 (blueprint: def-per-regular-immersion-class-system). -/
def regularClassReduction (ell n N : ℕ) (h : n ≤ N) :
    regularClassCoefficient.{u} ell N →+* regularClassCoefficient.{u} ell n :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((ZMod.castHom (Nat.pow_dvd_pow ell h) (ZMod (ell ^ n))).comp
      ULift.ringEquiv.toRingHom)

/-- Coefficient reduction on all signed Tate sheaves, characterized on roots and tensors.
The degree-zero map sends a constant a to its residue. Degree one is the power map
u ↦ u^(ell^(N-n)); tensor compatibility includes evaluation in opposite degrees and
therefore specifies the dual comparisons for negative twists.
Source: ILO XVI 3.3.1--3.3.2 (blueprint: def-per-regular-immersion-class-system). -/
def RegularClassReductionData (ell n N : ℕ) (h : n ≤ N)
    (tN : Scheme.FiniteEtaleTwistPullbackData (regularClassCoefficient.{u} ell N)
      (ell ^ N) (regularClassAnnihilator ell N))
    (tn : Scheme.FiniteEtaleTwistPullbackData (regularClassCoefficient.{u} ell n)
      (ell ^ n) (regularClassAnnihilator ell n)) : Type (u + 1) :=
  { data : ∀ (T : Scheme.{u}),
      IsUnit (ell : Γ(T, ⊤)) →
      (T.rootsOfUnitySheaf (ell ^ N) ⟶ T.rootsOfUnitySheaf (ell ^ n)) ×
      (∀ a : ℤ, Scheme.finiteEtaleTateSheaf (regularClassCoefficient ell N) (ell ^ N) T
          (regularClassAnnihilator ell N) a ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology (regularClassReduction ell n N h)).obj
          (Scheme.finiteEtaleTateSheaf (regularClassCoefficient ell n) (ell ^ n) T
            (regularClassAnnihilator ell n) a)) //
    ∀ (T : Scheme.{u}) (hT : IsUnit (ell : Γ(T, ⊤))),
      (data T hT).1 ≫ kernel.ι ((ell ^ n) • 𝟙 T.gmSheaf) =
        (ell ^ (N - n)) • kernel.ι ((ell ^ N) • 𝟙 T.gmSheaf) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : regularClassCoefficient.{u} ell N),
        ((data T hT).2 0).hom.app W
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (regularClassCoefficient ell N) (regularClassCoefficient ell N)))).app
              W a) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of (regularClassCoefficient ell n) (regularClassCoefficient ell n)))).app W
            (regularClassReduction ell n N h a)) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : regularClassCoefficient.{u} ell N)
          (z : (T.rootsOfUnitySheaf (ell ^ N)).obj.obj W),
        ((data T hT).2 1).hom.app W
          (Scheme.finiteEtaleTateOneGenerator (regularClassCoefficient ell N) (ell ^ N) T
            (regularClassAnnihilator ell N) W a z) =
        Scheme.finiteEtaleTateOneGenerator (regularClassCoefficient ell n) (ell ^ n) T
          (regularClassAnnihilator ell n) W (regularClassReduction ell n N h a)
            ((data T hT).1.hom.app W z)) ∧
      (∀ (W : T.Etaleᵒᵖ) (a b : ℤ)
          (x : (Scheme.finiteEtaleTateSheaf (regularClassCoefficient ell N) (ell ^ N) T
            (regularClassAnnihilator ell N) a).obj.obj W)
          (y : (Scheme.finiteEtaleTateSheaf (regularClassCoefficient ell N) (ell ^ N) T
            (regularClassAnnihilator ell N) b).obj.obj W),
        ((data T hT).2 (a + b)).hom.app W
          ((tN.p T (regularClassExponentUnit ell N T hT) a b).hom.hom.app W
            (regularClassPureTensor _ T _ _ W x y)) =
        (tn.p T (regularClassExponentUnit ell n T hT) a b).hom.hom.app W
          (regularClassPureTensor _ T _ _ W
            (((data T hT).2 a).hom.app W x) (((data T hT).2 b).hom.app W y))) }

/-- A simultaneous family on every Noetherian pair and every positive coefficient level.
Source: ILO XVI 2.3.1 and 3.3 (blueprint: def-per-regular-immersion-class-system). -/
def RegularClassFamily (ell : ℕ) : Type (u + 1) :=
  ∀ (n : ℕ) (_hn : 0 < n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (_hi : IsStalkRegularClosedImmersion i c) (_hX : IsUnit (ell : Γ(X, ⊤))),
    RegularSupportedClass (regularClassCoefficient ell n) (ell ^ n)
      (regularClassAnnihilator ell n) i c

/-- The recorded normalized finite Tate comparisons at one coefficient level.
Source: ILO XVI 2.2.3.1 and 3.3 (blueprint: def-per-regular-immersion-class-system). -/
def regularClassTransport (ell : ℕ) (h : ell.Prime) (n : ℕ) :
    Scheme.FiniteEtaleTwistPullbackData (regularClassCoefficient.{u} ell n) (ell ^ n)
      (regularClassAnnihilator ell n) :=
  Scheme.finiteEtaleTwistPullbackData _ _ (pow_pos h.pos n) _

/-- The exact reduction square for the supported class, in the original coefficient
category after restriction of scalars. No flatness of the reduction ring is assumed.
Source: ILO XVI 3.3.1--3.3.2 (blueprint: def-per-regular-immersion-class-system). -/
def RegularClassCoefficientCompatibility (ell : ℕ) (h : ell.Prime)
    (g : RegularClassFamily.{u} ell) : Prop :=
  ∀ (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (hnN : n ≤ N),
    ∃ d : RegularClassReductionData ell n N hnN
        (regularClassTransport ell h N) (regularClassTransport ell h n),
    ∀ {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
      (hi : IsStalkRegularClosedImmersion i c) (hX : IsUnit (ell : Γ(X, ⊤)))
      (hZ : IsUnit (ell : Γ(Z, ⊤))),
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} (regularClassCoefficient ell N)) i).map
        ((d.val Z hZ).2 0))).comp
      ((g n hn i c hi hX).mapExactFunctor
        (Sheaf.restrictScalars X.smallEtaleTopology (regularClassReduction ell n N hnN)))
      (zero_add (2 * c)) =
    (g N hN i c hi hX).comp (Ext.mk₀ ((d.val X hX).2 c)) (add_zero (2 * c))

/-- The normalization in codimensions zero and one. In degree zero the unit equation
is restriction to the open-and-closed summand. In degree one the actual relative Kummer
boundary fixes the sign, including the +c_1 unit composite.
Source: ILO XVI 2.1 and 2.3.1 (blueprint: def-per-regular-immersion-class-system). -/
def RegularClassNormalization (ell : ℕ) (g : RegularClassFamily.{u} ell) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsUnit (ell : Γ(X, ⊤))),
    (∀ hi : IsStalkRegularClosedImmersion i 0,
      (g n hn i 0 hi hX).comp
        (Ext.mk₀ (supportedConstantUnit (regularClassCoefficient ell n) i)) (add_zero 0) =
      Ext.mk₀ (𝟙 _)) ∧
    (∀ (hi : IsStalkRegularClosedImmersion i 1) (hI : i.ker.IsInvertible),
      SupportedKummerBoundary (regularClassCoefficient ell n) (ell ^ n)
        (regularClassAnnihilator ell n) i hI (regularClassExponentUnit ell n X hX)
        (g n hn i 1 hi hX))

/-- Transitivity of the supported class on all regular closed flags.
Source: ILO XVI Theorem 2.3.2 (blueprint: def-per-regular-immersion-class-system). -/
def RegularClassTransitivity (ell : ℕ) (h : ell.Prime)
    (g : RegularClassFamily.{u} ell) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) {Z Y X : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (a b : ℕ) (hi : IsStalkRegularClosedImmersion i a)
    (hj : IsStalkRegularClosedImmersion j b)
    (hji : IsStalkRegularClosedImmersion (i ≫ j) (a + b))
    (hX : IsUnit (ell : Γ(X, ⊤))) (hY : IsUnit (ell : Γ(Y, ⊤))),
    RegularClassComposition (regularClassCoefficient ell n) (ell ^ n)
      (regularClassAnnihilator ell n) (regularClassTransport ell h n)
      i j (regularClassExponentUnit ell n X hX) (regularClassExponentUnit ell n Y hY) a b
      (g n hn i a hi hY) (g n hn j b hj hX) (g n hn (i ≫ j) (a + b) hji hX)

/-- Flat comparison of pairs, including open restrictions and the canonical localization
and strict-localization structural maps. These are comparisons of the supported class;
no exceptional base change is asserted for an arbitrary complex.
Source: ILO XVI 2.2.3.1 and 3.2 (blueprint: def-per-regular-immersion-class-system). -/
def RegularClassFlatCompatibility (ell : ℕ) (h : ell.Prime)
    (g : RegularClassFamily.{u} ell) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) {Z X Z' X' : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian X] [IsNoetherian Z'] [IsNoetherian X']
    (i : Z ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i] [IsClosedImmersion i']
    (v : X' ⟶ X) [Flat v] (w : Z' ⟶ Z) (sq : IsPullback w i' i v)
    (c : ℕ) (hi : IsStalkRegularClosedImmersion i c)
    (hi' : IsStalkRegularClosedImmersion i' c)
    (hX : IsUnit (ell : Γ(X, ⊤))) (hX' : IsUnit (ell : Γ(X', ⊤))),
    RegularClassPullback (regularClassCoefficient ell n) (ell ^ n)
      (regularClassAnnihilator ell n) (regularClassTransport ell h n)
      i i' v w sq (regularClassExponentUnit ell n X hX) (regularClassExponentUnit ell n X' hX') c
      (g n hn i c hi hX) (g n hn i' c hi' hX')

/-- The normalization, transitivity, flat restriction and coefficient laws of a
regular-immersion class family. Its Cartier-flag formula is the repeated transitivity
identity with each codimension-one factor fixed by SupportedKummerBoundary.
Source: ILO XVI 2.3.1--2.3.2 and 3.3
(blueprint: def-per-regular-immersion-class-system). -/
def IsRegularImmersionClassSystem (ell : ℕ) (h : ell.Prime)
    (g : RegularClassFamily.{u} ell) : Prop :=
  RegularClassNormalization ell g ∧ RegularClassTransitivity ell h g ∧
    RegularClassFlatCompatibility ell h g ∧ RegularClassCoefficientCompatibility ell h g

end AlgebraicGeometry.Etale
