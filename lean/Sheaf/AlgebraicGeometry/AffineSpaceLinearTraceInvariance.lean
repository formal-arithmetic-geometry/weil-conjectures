/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Paper.ConstantSheafSectionsLocallyConstant
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange

/-!
# Linear changes of coordinates preserve the affine-space counit trace

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-linear-trace-invariance.md,
Proof paragraphs 1 and 2 (blueprint: lem-amb-linear-trace-invariance).

The coefficient complex is the existing coordinate-tower model of A(d)[2d]. Its
canonical inverse-image comparison is constructed by descent from the ordered tensor
of d shifted Tate lines on the base. The action uses compact-support exchange for the
actual Cartesian square (a_g, 1_S), followed by this coefficient comparison. It is then
transported along the existing bounded-below compact-support comparison to the tower.

## Main definitions and statement

- `affineTraceLinearMap`: the concrete polynomial map v ↦ gv in the tower model.
- `affineLinearCoefficientPullback`: the canonical comparison on A(d)[2d].
- `affineLinearTraceAction`: exchange followed by the coefficient comparison.
- `affineSpaceLinearTraceInvariance`: the specified action preserves the specified counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The linear coordinate map in the existing tower model: pull the matrix entries
back from S, take the usual finite sums, and use the canonical affine-space coordinate
isomorphism. Source: blueprint linear-trace lemma, statement and proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineTraceLinearMap (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    affineTraceTower S d ⟶ affineTraceTower S d :=
  AffineSpace.homOfVector (affineTraceProjection S d)
    (fun i : ULift.{u} (Fin d) ↦ ∑ j : Fin d,
      (affineTraceProjection S d).appTop.hom (g i.down j) * affineTraceCoordinate S d j) ≫
    (affineTraceAffineSpaceIso S d).inv

namespace Etale

/-- The identity inverse-image comparison, using the existing exact-derived comparison.
Source: blueprint linear-trace lemma, identity normalization in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearPullbackId (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    ordinaryFinitePullback A (𝟙 S) ≅ 𝟭 (DerivedCategoryModule A S) :=
  leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S) ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) S) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The ordered tensor product of d shifted finite Tate lines on the base, representing
A_S(d)[2d]. The zero stage is the constant coefficient complex. No orientation is chosen.
Source: blueprint linear-trace lemma, K_T in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearBaseCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : ℕ → DerivedCategoryModule A S
  | 0 => ordinaryFiniteUnit A S
  | d + 1 => (derivedTensorRight (ModuleCat.{u + 1} A) S
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj
        (affineLinearBaseCoefficient A N hA S d)

/-- One coordinate right functor, canonically expressed as inverse image of a tensor
with the shifted line on its base. This uses tensor inverse image, composition, and
normalized finite Tate inverse image, in that order.
Source: blueprint linear-trace lemma, coefficient identification in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearLineDescent (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (K : DerivedCategoryModule A S) :
    (affineTraceLineRight A N hA S).obj K ≅
      (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} S ↘ S)).obj
        ((derivedTensorRight (ModuleCat.{u + 1} A) S
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj K) :=
  ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart S)
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≪≫
    ordinaryFiniteTensorRightMapIso A (AffineSpace PUnit.{u + 1} S)
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine.affineChart S)
        (ProjectiveLine S ↘ S) (AffineSpace PUnit.{u + 1} S ↘ S)
        (ProjectiveLine.affineChart_over S).symm).symm.app K)
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine.affineChart S)
        (affineTraceProjectiveInvertible N S hS) ≪≫
        (ordinaryFiniteShiftedLinePullback A N hA t
          (AffineSpace PUnit.{u + 1} S ↘ S) hS).symm) ≪≫
    (ordinaryFiniteTensorPullback A (AffineSpace PUnit.{u + 1} S ↘ S) K
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm

/-- One induction step in the canonical coefficient descent, with the preceding
comparison explicit. Source: blueprint linear-trace lemma, proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearCoefficientDescentStep (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (e : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (affineLinearBaseCoefficient A N hA S d)) :
    (affineTraceLineRight A N hA (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (ordinaryFinitePullback A
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d) ≫
          affineTraceProjection S d)).obj
        ((derivedTensorRight (ModuleCat.{u + 1} A) S
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).obj
            (affineLinearBaseCoefficient A N hA S d)) :=
  affineLinearLineDescent A N hA t (affineTraceTower S d)
    (affineTraceInvertible N S hS d)
    ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≪≫
  (ordinaryFinitePullback A
    (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).mapIso
    (ordinaryFiniteTensorRightMapIso A (affineTraceTower S d) e
      (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).symm ≪≫
    (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
      (affineLinearBaseCoefficient A N hA S d)
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).symm) ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
    (affineTraceProjection S d)).symm.app (affineLinearBaseCoefficient A N hA S (d + 1))

/-- Descend the existing tower coefficient to the ordered shifted Tate tensor on S.
Every component is a canonical tensor, inverse-image, or normalized Tate comparison.
Source: blueprint linear-trace lemma, coefficient identification in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearCoefficientDescent (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (affineLinearBaseCoefficient A N hA S d) :=
  Nat.rec (motive := fun e ↦
    (affineTraceRight A N hA S e).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S e)).obj
        (affineLinearBaseCoefficient A N hA S e))
    ((affineLinearPullbackId A S).app (ordinaryFiniteUnit A S)).symm
    (fun e r ↦ affineLinearCoefficientDescentStep A N hA t S hS e r) d

/-- The canonical Tate comparison for an S-endomorphism of affine space, obtained by
pulling the descended base coefficient through a ≫ p = p. In particular this is the
usual roots-of-unity/tensor/shift comparison, with no scalar automorphism inserted.
Source: blueprint linear-trace lemma, theta_a in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearCoefficientPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (ha : a ≫ affineTraceProjection S d = affineTraceProjection S d) :
    (ordinaryFinitePullback A a).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) :=
  (ordinaryFinitePullback A a).mapIso (affineLinearCoefficientDescent A N hA t S hS d) ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a (affineTraceProjection S d)
      (affineTraceProjection S d) ha.symm).symm.app
        (affineLinearBaseCoefficient A N hA S d) ≪≫
    (affineLinearCoefficientDescent A N hA t S hS d).symm

/-- The specified bounded-below tower comparison, read in the ordinary unbounded
category using the two existing restriction-compatibility isomorphisms.
Source: blueprint linear-trace lemma, identification with F_S in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearCompactComparison (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineTraceLeft A S d).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :=
  let K : _root_.DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  ((affineTracePlusCompatibility A S d).app K).symm ≪≫
    _root_.DerivedCategory.Plus.ι.mapIso
      ((affineTraceCompactSupportComparison A S d).app K) ≪≫
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection S d)).app K

/-- The pullback action: identify the tower with Rp_d!, insert inverse image along the
identity on S, apply exchange for the actual square, apply the canonical Tate comparison,
and return through the same tower comparison.
Source: blueprint linear-trace lemma, definition of rho_g in proof paragraph 1
(blueprint: lem-amb-linear-trace-invariance). -/
def affineLinearTraceAction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (a : affineTraceTower S d ⟶ affineTraceTower S d)
    (sq : IsPullback a (affineTraceProjection S d) (affineTraceProjection S d) (𝟙 S)) :
    (affineTraceLeft A S d).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      (affineTraceLeft A S d).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) :=
  (affineLinearCompactComparison N hN A hA S hS d).hom ≫
    (affineLinearPullbackId A S).inv.app _ ≫
    (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).map
      (affineLinearCoefficientPullback A N hA t S hS d a
        (sq.w.trans (Category.comp_id _))).hom ≫
    (affineLinearCompactComparison N hN A hA S hS d).inv

/-- Every invertible linear coordinate change preserves the actual coordinate-tower
counit trace. The existential square is the Cartesian-square certificate for the concrete
polynomial map v ↦ gv; it is not an extra hypothesis on g or a choice of action.
Source: blueprint linear-trace lemma, statement and both proof paragraphs
(blueprint: lem-amb-linear-trace-invariance).

Proof, following the node's seven steps:
1. Construct G = D(det) in affine matrix space. Its coordinate ring on Spec R is
   R[x_ij,z]/(z det(x)-1), finite type over R, hence G is Noetherian. The universal
   invertible matrix gives a; the inverse is z adj(x). The given g and the identity
   define sections s_g and e. The coordinate formulas give the Cartesian square below.
2. Compactify the affine-space projections by the standard open in projective space;
   these maps are separated and finite type, with quasi-compact open and proper factors.
   Apply thm-cbc-finite-torsion to the universal automorphism square and base changes.
   Use lem-asd-etale-finite-twist-pullback for theta_a. Exchange pasting gives
   C_u u* rho_a = rho_(a_T) C_u; at the identity both factors are identities.
3. Conjugate rho_a by the specified trace isomorphism of lem-amb-affine-space-top-trace.
   Degree-zero full faithfulness identifies the resulting endomorphism of A_G with an
   ordinary module-sheaf map. Its value b on 1 determines it by linearity. The constant
   sheaf section lemmas identify b with a Zariski-locally-constant function beta on G.
   The trace base-change equation identifies its pullback with the corresponding scalar.
4. Each residue-field fibre of G is nonempty and connected: its ring is a polynomial
   domain localized at the nonzero determinant, whose value at the identity is 1.
   Its zero prime lies in every nonempty basic open. This includes dimension zero.
5. On each such fibre beta equals 1 at the identity by Step 2. A locally constant map
   on a connected space is constant (lem-weil-pbc-connected-locally-constant-map).
6. Every point of G lifts to its residue-field fibre. Thus beta is everywhere 1, hence
   b = 1 by the constant-sheaf section identification. Degree-zero faithfulness gives
   t_G rho_a = t_G as an actual derived equality. The empty base causes no exception.
7. Pull back along s_g and use exchange pasting and trace base change. Cancel C_(s_g)
   to obtain t_S rho_g = t_S. In dimension zero this is the identity-adjunction equation.
-/
theorem affineSpaceLinearTraceInvariance (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    ∃ sq : IsPullback (affineTraceLinearMap S d g) (affineTraceProjection S d)
        (affineTraceProjection S d) (𝟙 S),
      affineLinearTraceAction N hN A hA t S hS d (affineTraceLinearMap S d g) sq ≫
        affineTraceCounit A N hA t D S hS d = affineTraceCounit A N hA t D S hS d := by
  sorry

end Etale
end AlgebraicGeometry
