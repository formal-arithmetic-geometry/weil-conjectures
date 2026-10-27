/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Scalar compatibility of the normalized projective-line splitting

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts, retained Steps 5 and 6
(blueprint: lem-sp-p1-splitting-scalar).

## Main definitions and statement

* `p1ScalarSingleMap`: derive the specified ordinary coefficient map.
* `p1ScalarShiftedLine`: its shifted Tate-line identification.
* `p1ScalarSourceMap`: its ordered direct-sum identification.
* `p1ScalarPushforwardMap`: the proper counit transpose with its target identification.
* `p1SplittingScalar`: compatibility of the normalized splitting and trace.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Derive an ordinary scalar map on degree-zero sheaves using the scalar adjunction.
This is the canonical comparison with ordinary extension, followed by the given map;
its definition does not require the scalar ring map to be flat.
Source: Stacks 06YY, identity-topos coefficient specialization
(blueprint: lem-sp-p1-splitting-scalar). -/
def p1ScalarSingleMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (c : (ProEtale.etaleSheafExtendScalars φ T).obj F ⟶ G) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj G :=
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).homEquiv _ _).symm
    ((_root_.DerivedCategory.singleFunctor _ 0).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ c) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app G)

/-- Shift the specified coefficient identification of the Tate line by two.
Source: blueprint Charts, balanced twist identifications
(blueprint: lem-sp-p1-splitting-scalar). -/
def p1ScalarShiftedLine {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u})
    (d : (scalarExtension φ T).obj (ordinaryFiniteLine A N hA T) ≅
      ordinaryFiniteLine B N hB T) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  letI : (scalarExtension φ T).CommShift ℤ :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  ((scalarExtension φ T).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso d

/-- The direct-sum version of the balanced coefficient identifications, assembled
from the two projections. Source: blueprint Charts, retained Step 5
(blueprint: lem-sp-p1-splitting-scalar). -/
def p1ScalarSourceMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u})
    (d0 : (scalarExtension φ S).obj (ordinaryFiniteUnit A S) ≅ ordinaryFiniteUnit B S)
    (d1 : (scalarExtension φ S).obj (ordinaryFiniteLine A N hA S) ≅
      ordinaryFiniteLine B N hB S) :
    (scalarExtension φ S).obj
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      ((ordinaryFiniteLine B N hB S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit B S) :=
  biprod.lift
    ((scalarExtension φ S).map biprod.fst ≫ (p1ScalarShiftedLine φ N hA hB S d1).hom)
    ((scalarExtension φ S).map biprod.snd ≫ d0.hom)

/-- The specified proper counit-transpose coefficient map, followed by the balanced
identification of its shifted Tate-line input. Source: blueprint Charts, Steps 3--5
(blueprint: lem-sp-p1-splitting-scalar). -/
def p1ScalarPushforwardMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u})
    (dP : (scalarExtension φ (ProjectiveLine S)).obj
      (ordinaryFiniteLine A N hA (ProjectiveLine S)) ≅
        ordinaryFiniteLine B N hB (ProjectiveLine S)) :
    (scalarExtension φ S).obj ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ⟶
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (scalarMate φ (ProjectiveLine S ↘ S)).app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
      (p1ScalarShiftedLine φ N hA hB (ProjectiveLine S) dP).hom

/-- Scalar extension preserves the normalized projective-line splitting and trace,
with the balanced identifications explicitly characterized on constant and root
sections. The derived identifications are fixed by the adjunction comparison
`p1ScalarSingleMap`; hence the equations concern the specified derived arrows.
No flatness or finite projective dimension of B over A is assumed.
Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts, retained Steps 5 and 6
(blueprint: lem-sp-p1-splitting-scalar).

Proof: (1) The standing finite-type base is Noetherian by
lem-weil-pbc-finite-type-over-noetherian, and ell distinct from char(k) makes N
invertible. By lem-asd-finite-etale-twist-line the constant sheaf and Tate line
are flat. Their degree-zero complexes and shifts are K-flat by lem-pc-kflat-closure.
Thus lem-pur-derived-change-of-rings computes scalar extension by ordinary tensor.
The balanced map sends (z tensor a) tensor b to z tensor phi(a)b, with inverse
z tensor b maps to (z tensor 1) tensor b. Its adjoint has exactly the generator
normalizations below, and deriving it gives the specified single maps.
(2) Both Kummer Chern arrows are the images of the same Z/N arrow. Naturality of
the canonical composition comparison of lem-sfb-ringed-derived-monoidal-comparisons
identifies their scalar extensions, including their multiplication units. No
nonflat tensoring of the Kummer exact sequence is used.
(3) The proper coefficient map of lem-sp-et-proet-coefficient-compatibility is
the counit transpose. Apply lem-pur-adjunction-mate-transpose to identify scalar
extension of each adjunct with the B-adjunct of the extended upstairs arrow.
(4) Roots-induced twist pullback, lem-asd-etale-finite-twist-pullback, is compatible
with balancing on the same root generators. Step 3 therefore compares both the
twisted-unit and Kummer components of the splitting from
lem-asd-ordinary-finite-p1-adjunction.
(5) Equality on the two biproduct inclusions gives the first displayed equality.
(6) By def-amb-p1-trace the trace is the second projection after inverse splitting.
Postcompose the first equality with t_B, compare with scalar extension of t_A,
and cancel scalar extension of the invertible splitting. This gives the second
equality. Only K-flat computations, adjunction and biproduct identities were used. -/
theorem p1SplittingScalar
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hne : ell ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0) :
    ∃ (_hNoetherian : IsNoetherian S) (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))),
    ∃ (c0 : (ProEtale.etaleSheafExtendScalars φ S).obj (ordinaryFiniteConstant A S) ≅
        ordinaryFiniteConstant B S)
      (c1 : (ProEtale.etaleSheafExtendScalars φ S).obj
        (Scheme.finiteEtaleTateLine S (ell ^ n) A hA) ≅
          Scheme.finiteEtaleTateLine S (ell ^ n) B hB)
      (cP : (ProEtale.etaleSheafExtendScalars φ (ProjectiveLine S)).obj
        (Scheme.finiteEtaleTateLine (ProjectiveLine S) (ell ^ n) A hA) ≅
          Scheme.finiteEtaleTateLine (ProjectiveLine S) (ell ^ n) B hB)
      (d0 : (scalarExtension φ S).obj (ordinaryFiniteUnit A S) ≅ ordinaryFiniteUnit B S)
      (d1 : (scalarExtension φ S).obj (ordinaryFiniteLine A (ell ^ n) hA S) ≅
        ordinaryFiniteLine B (ell ^ n) hB S)
      (dP : (scalarExtension φ (ProjectiveLine S)).obj
        (ordinaryFiniteLine A (ell ^ n) hA (ProjectiveLine S)) ≅
          ordinaryFiniteLine B (ell ^ n) hB (ProjectiveLine S)),
      (∀ (W : S.Etaleᵒᵖ) (a : A),
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ S).homEquiv _ _ c0.hom).hom.app W
            ((toSheafify S.smallEtaleTopology
              ((Functor.const S.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a) =
          (toSheafify S.smallEtaleTopology
            ((Functor.const S.Etaleᵒᵖ).obj (ModuleCat.of B B))).app W (φ a)) ∧
      (∀ (W : S.Etaleᵒᵖ) (a : A) (z : (S.rootsOfUnitySheaf (ell ^ n)).obj.obj W),
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ S).homEquiv _ _ c1.hom).hom.app W
            (Scheme.finiteEtaleTateOneGenerator A (ell ^ n) S hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B (ell ^ n) S hB W (φ a) z) ∧
      (∀ (W : (ProjectiveLine S).Etaleᵒᵖ) (a : A)
          (z : ((ProjectiveLine S).rootsOfUnitySheaf (ell ^ n)).obj.obj W),
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ (ProjectiveLine S)).homEquiv
          _ _ cP.hom).hom.app W
            (Scheme.finiteEtaleTateOneGenerator A (ell ^ n) (ProjectiveLine S) hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B (ell ^ n) (ProjectiveLine S) hB W (φ a) z) ∧
      d0.hom = p1ScalarSingleMap φ S c0.hom ∧
      d1.hom = p1ScalarSingleMap φ S c1.hom ∧
      dP.hom = p1ScalarSingleMap φ (ProjectiveLine S) cP.hom ∧
      ((scalarExtension φ S).map
          (projectiveLineTraceDatum (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
            A hA S hS).decomposition.hom ≫
        p1ScalarPushforwardMap φ (ell ^ n) hA hB S dP =
          p1ScalarSourceMap φ (ell ^ n) hA hB S d0 d1 ≫
            (projectiveLineTraceDatum (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
              B hB S hS).decomposition.hom) ∧
      (p1ScalarPushforwardMap φ (ell ^ n) hA hB S dP ≫
          projectiveLineTrace (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n) B hB S hS =
        (scalarExtension φ S).map
            (projectiveLineTrace (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
              A hA S hS) ≫ d0.hom) := by
  sorry

end AlgebraicGeometry.Etale
