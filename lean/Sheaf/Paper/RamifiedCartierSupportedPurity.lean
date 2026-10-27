/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.Paper.CartierDualKummerNormalization
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.CartierPairTensorAddition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Ramification multiplicity for supported Cartier purity

Source: ILO, Travaux de Gabber, Expose XVI, Sections 2.1 and 2.3, Theorem 3.1.1;
Stacks Project, Tag 03PL. The ordinary etale support objects are the right derived
kernels of the actual open units. The orientation uses the existing positive
supported Kummer boundary and the existing dual Tate evaluation.
(blueprint: lem-sfb-ramified-cartier-supported-purity).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open RamifiedRoot

/-- All clauses of the supported ramification square, written with degree-zero
closed duals mapping to the support object shifted by two. This is the shift by
two of the displayed equation with source i_* A(-1)[-2]. Local let-bindings only
apply the published support functor and its inclusion to the constant object.
The nonreduced inverse image V(g^e) is retained separately from V(g), and the
closed exchange is the existing mate for their composite commuting square.

Source: ILO XVI 2.1, 2.3, 3.1.1; Stacks 03PL, 0A45
(blueprint: lem-sfb-ramified-cartier-supported-purity). -/
def RamifiedCartierPurityAssertion (ℓ s : ℕ) (hN : 0 < ℓ ^ s)
    (X X' : Scheme.{u}) (f : Γ(X, ⊤)) (g : Γ(X', ⊤))
    (h : X' ⟶ X) (e : ℕ) : Prop :=
  let N := ℓ ^ s
  let A := ULift.{u + 1} (ZMod N)
  let hA : (N : A) = 0 := congrArg (ULift.up : ZMod N → A) (ZMod.natCast_self N)
  let C := ModuleCat.{u + 1} A
  let D := X.zeroLocusSubscheme {f}
  let D' := X'.zeroLocusSubscheme {g}
  let E := X'.zeroLocusSubscheme {g ^ e}
  let i : D ⟶ X := X.zeroLocusSubschemeι {f}
  let i' : D' ⟶ X' := X'.zeroLocusSubschemeι {g}
  let k : E ⟶ X' := X'.zeroLocusSubschemeι {g ^ e}
  let U := (X.basicOpen f).toScheme
  let U' := (X'.basicOpen g).toScheme
  let j : U ⟶ X := (X.basicOpen f).ι
  let j' : U' ⟶ X' := (X'.basicOpen g).ι
  let K : DerivedCategoryModule A X :=
    (sectionsWithSupport C j).rightDerivedFunctor.obj (ordinaryFiniteUnit A X)
  let K' : DerivedCategoryModule A X' :=
    (sectionsWithSupport C j').rightDerivedFunctor.obj (ordinaryFiniteUnit A X')
  let q : K ⟶ ordinaryFiniteUnit A X :=
    (Functor.rightDerivedFunctorNatTrans (sectionsWithSupportι C j)).app _ ≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        (𝟭 (Sheaf X.smallEtaleTopology C))).hom.app _ ≫
      (Functor.mapDerivedCategoryIdIso _).hom.app _
  let q' : K' ⟶ ordinaryFiniteUnit A X' :=
    (Functor.rightDerivedFunctorNatTrans (sectionsWithSupportι C j')).app _ ≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        (𝟭 (Sheaf X'.smallEtaleTopology C))).hom.app _ ≫
      (Functor.mapDerivedCategoryIdIso _).hom.app _
  let H := (upperStar C h).mapDerivedCategory
  let a : H.obj (ordinaryFiniteUnit A X) ≅ ordinaryFiniteUnit A X' :=
    ((upperStar C h).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((Scheme.upperStarConstantSheafIso C h).app (ModuleCat.of A A))
  let B := (lowerStar C j).rightDerivedFunctor.obj
    ((upperStar C j).mapDerivedCategory.obj (ordinaryFiniteUnit A X))
  let B' := (lowerStar C j').rightDerivedFunctor.obj
    ((upperStar C j').mapDerivedCategory.obj (ordinaryFiniteUnit A X'))
  ∃ (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤)))
    (hD : IsUnit (N : Γ(D, ⊤))) (hD' : IsUnit (N : Γ(D', ⊤)))
    (v : U' ⟶ U) (sqU : IsPullback v j' j h)
    (r : D' ⟶ E) (d : E ⟶ D) (_hr : r ≫ k = i')
    (_sqE : IsPullback d k i h) (sqD : CommSq (r ≫ d) i' i h),
    let β : H.obj B ⟶ B' :=
      (exactDerivedBaseChangeMap C sqU.toCommSq).app _ ≫
        (lowerStar C j').rightDerivedFunctor.map
          ((exactDerivedSquareUpperStarIso C sqU.toCommSq).inv.app _ ≫
            (upperStar C j').mapDerivedCategory.map a.hom)
    let ρ := closedExchange A N hN hA sqD hD hD'
    ∃ (δ : B ⟶ K⟦(1 : ℤ)⟧) (δ' : B' ⟶ K'⟦(1 : ℤ)⟧)
      (P : closedDual A N hA i ≅ K⟦(2 : ℤ)⟧)
      (P' : closedDual A N hA i' ≅ K'⟦(2 : ℤ)⟧)
      (θ : H.obj K ⟶ K'),
      Pretriangulated.Triangle.mk q
        ((mapDerivedUpperStarLowerStarAdjunction C j).unit.app _) δ ∈ distTriang _ ∧
      Pretriangulated.Triangle.mk q'
        ((mapDerivedUpperStarLowerStarAdjunction C j').unit.app _) δ' ∈ distTriang _ ∧
      KummerNormalized A N hN hA i hI hX hD K q P ∧
      KummerNormalized A N hN hA i' hI' hX' hD' K' q' P' ∧
      (∀ p : closedDual A N hA i ⟶ K⟦(2 : ℤ)⟧,
        p ≫ q⟦(2 : ℤ)⟧' = P.hom ≫ q⟦(2 : ℤ)⟧' → p = P.hom) ∧
      (∀ p : closedDual A N hA i' ⟶ K'⟦(2 : ℤ)⟧,
        p ≫ q'⟦(2 : ℤ)⟧' = P'.hom ≫ q'⟦(2 : ℤ)⟧' → p = P'.hom) ∧
      θ ≫ q' = H.map q ≫ a.hom ∧
      (∀ t : H.obj K ⟶ K', t ≫ q' = H.map q ≫ a.hom → t = θ) ∧
      H.map δ ≫ (H.commShiftIso (1 : ℤ)).hom.app _ ≫ θ⟦(1 : ℤ)⟧' = β ≫ δ' ∧
      H.map P.hom ≫ (H.commShiftIso (2 : ℤ)).hom.app _ ≫ θ⟦(2 : ℤ)⟧' =
        (e • ρ) ≫ P'.hom ∧
      (∀ z : ℤ, z ≠ 2 →
        IsZero ((DerivedCategory.homologyFunctor _ z).obj K) ∧
        IsZero ((DerivedCategory.homologyFunctor _ z).obj K')) ∧
      (DerivedCategory.homologyFunctor _ 0).map
          (H.map P.hom ≫ (H.commShiftIso (2 : ℤ)).hom.app _ ≫ θ⟦(2 : ℤ)⟧') =
        e • ((DerivedCategory.homologyFunctor _ 0).map ρ ≫
          (DerivedCategory.homologyFunctor _ 0).map P'.hom)

/-- Ramification multiplies the ordinary supported Cartier purity comparison by
the exponent, with the positive Kummer and actual adjunction-unit normalizations.
Empty divisors and e = 1 are included. The coefficient ring is precisely the
universe lift of Z/(ell^s), not an arbitrary annihilated coefficient algebra.

Source: ILO XVI 2.1, 2.3 and Theorem 3.1.1; Stacks 03PL
(blueprint: lem-sfb-ramified-cartier-supported-purity).

Proof:
1. Supported/open orthogonality and the actual support triangle make forgetting
support bijective on Hom from an object supported on the closed complement.
2. Tensor the positive supported Kummer boundary by the dual Tate line and shift.
The bijection gives its unique lift to the support fibre, on both schemes.
3. The regular-pair purity theorem in codimension one makes these lifts invertible;
the regular-immersion class calculus identifies the positive Kummer normalization.
The empty divisor gives the zero object directly.
4. The scheme-theoretic pullback is E = V(g^e), a Cartier divisor with the same
closed subtopos as D' = V(g). Apply ordinary Cartier Kummer pullback to E, then the
canonical closed reduction comparison. E is not assumed regular.
5. Cartier-pair tensor addition and induction on e give c_E = e c_D'. Tensor by
the dual line. No inverse of e is taken, including when ell^s divides e.
6. The actual open exchange mate commutes with the actual unit. Its induced
supported arrow satisfies the forget-support square; supported Hom bijectivity
makes it unique. Cancel the forget-support map to obtain the derived formula.
7. Closed pushforward is exact. Its dual Tate sheaf is in degree zero, so the
support fibre has cohomology only in degree two. Apply H^0 to the shifted formula
to get the degree-two transition, also for identity maps and empty schemes.
-/
theorem ramifiedCartierSupportedPurity (ℓ s : ℕ) (hℓ : ℓ.Prime) (hs : 1 ≤ s)
    (X X' : Scheme.{u}) [IsAffine X] [IsAffine X'] [IsNoetherian X] [IsNoetherian X']
    (hX : IsRegularScheme X) (hX' : IsRegularScheme X')
    (hℓX : IsUnit (ℓ : Γ(X, ⊤))) (hℓX' : IsUnit (ℓ : Γ(X', ⊤)))
    (f : Γ(X, ⊤)) (g : Γ(X', ⊤))
    (hf : f ∈ nonZeroDivisors _) (hg : g ∈ nonZeroDivisors _)
    (hD : IsRegularScheme (X.zeroLocusSubscheme {f}))
    (hD' : IsRegularScheme (X'.zeroLocusSubscheme {g}))
    (h : X' ⟶ X) (e : ℕ) (he : 1 ≤ e) (hfg : h.appTop.hom f = g ^ e) :
    RamifiedCartierPurityAssertion ℓ s (pow_pos hℓ.pos s) X X' f g h e := by
  sorry

end AlgebraicGeometry.Etale
