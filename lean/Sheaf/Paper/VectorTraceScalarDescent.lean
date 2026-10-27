/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.Paper.FiniteTateScalarSourceNormalization
public import Sheaf.Paper.EtaleCompactScalarCoherence
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
import Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints
import Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.Paper.OpenScalarSiteCoherence
import Sheaf.Paper.EtaleOpenScalarExchange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.P1KummerDerivedScalar
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Scalar descent of the specified vector-bundle trace

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, old Steps 9--10
(blueprint: lem-pur-vector-trace-scalar-descent).

The helper maps express the normalized Tate balancing in the existing ordered-tensor
presentation used by vector integration and the affine coordinate tower. All compact
support maps are the published proper/open maps for the chosen compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
namespace VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The unique ordinary balancing family, selected from the existing normalization
 theorem. Its pure-root/scalar generator equations determine every map uniquely.
Source: blueprint paragraph 2, normalized coefficient identifications
(blueprint: lem-pur-vector-trace-scalar-descent). -/
@[irreducible]
def balancing (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ r : ℕ, (purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateTwist T N A hA r) ≅
      Scheme.finiteEtaleTateTwist T N B hB r :=
  Classical.choose ((finite_tate_scalar_source_normalization φ N hN hA hB T
    (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)).2.exists)

/-- The degree-one balancing from the uniquely generator-normalized Tate theorem,
shifted using its actual scalar/single comparison. This is l_{T,1}.
Source: blueprint paragraph 2, normalized coefficient identifications
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def line (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  finiteTateScalarLineMap φ N hA hB T 1 (balancing φ N hN hA hB T hT 1)

/-- Multiplication on the constant coefficient complex, with the published single/unit
identifications. Source: blueprint paragraph 2, u_T
(blueprint: lem-pur-vector-trace-scalar-descent). -/
abbrev unit (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtension φ T).obj (ordinaryFiniteUnit A T) ⟶ ordinaryFiniteUnit B T :=
  purityScalarUnitMap φ T

/-- The tensor powers of shifted balanced lines, starting with multiplication at rank
zero. This is l in the ordered shifted-Tate presentation already used by integration;
no orientation or new Tate object is chosen.
Source: blueprint paragraph 2, l_{T,d}
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def base (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ d : ℕ, (scalarExtension φ T).obj (affineLinearBaseCoefficient A N hA T d) ⟶
      affineLinearBaseCoefficient B N hB T d
  | 0 => unit φ T
  | d + 1 =>
    (ExceptionalCoefficients.tensorIso φ T).hom.app
      (affineLinearBaseCoefficient A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫
    ((ordinaryFiniteTensor B T).map (base φ N hN hA hB T hT d)).app
      ((scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ≫
    ((ordinaryFiniteTensor B T).obj (affineLinearBaseCoefficient B N hB T d)).map
      (line φ N hN hA hB T hT)

/-- The normalized scalar map on the pullback of an ordered Tate coefficient. The
inverse scalar/pullback comparison has source Q_X f^* and target f'^* Q_Y.
Source: blueprint paragraph 2, pullback compatibility of l
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def pullBase (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X T : Scheme.{u}} (f : X ⟶ T) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    (scalarExtension φ X).obj
        ((ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA T d)) ⟶
      (ordinaryFinitePullback B f).obj (affineLinearBaseCoefficient B N hB T d) :=
  (scalarPullbackIso φ f).inv.app (affineLinearBaseCoefficient A N hA T d) ≫
    (ordinaryFinitePullback B f).map (base φ N hN hA hB T hT d)

/-- The actual proper scalar mate followed by the degree-one normalized balancing.
Source: blueprint paragraph 2, tilde q_p
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def projective (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ⟶
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (scalarMate φ (ProjectiveLine S ↘ S)).app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
      (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))

/-- The comparison d_S is assembled from its two projections l_{S,1} and u_S.
Source: blueprint paragraph 2, projective-line decomposition
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def sum (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      ((ordinaryFiniteLine B N hB S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit B S) :=
  biprod.lift ((scalarExtension φ S).map biprod.fst ≫ line φ N hN hA hB S hS)
    ((scalarExtension φ S).map biprod.snd ≫ unit φ S)

/-- Normalized balancing on the coordinate tower's actual right-adjoint input,
transported by the existing coefficient-descent isomorphisms.
Source: blueprint paragraph 2, affine-space composition
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def affineCoefficient (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      (affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S) :=
  (scalarExtension φ (affineTraceTower S d)).map
      (affineLinearCoefficientDescent A N hA (projectiveLineTraceTransport N hN A hA)
        S hS d).hom ≫
    pullBase φ N hN hA hB (affineTraceProjection S d) hS d ≫
    (affineLinearCoefficientDescent B N hB (projectiveLineTraceTransport N hN B hB)
      S hS d).inv

/-- The actual coordinate-tower counit, on the specified compact-support source.
Source: blueprint paragraph 2, t_{p_d}
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def affineTrace (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      ordinaryFiniteUnit A S :=
  (affineLinearCompactComparison N hN A hA S hS d).inv ≫
    affineTraceCounit A N hA (projectiveLineTraceTransport N hN A hA)
      (projectiveLineTraceDatum N hN A hA) S hS d

/-- The specified compactification scalar map followed by the tower's Tate balancing.
Source: blueprint paragraph 2, affine tilde q
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def affine (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ S).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).obj
        ((affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S)) :=
  (compactScalarChosenMap φ (affineTraceProjection S d)).app
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).map
      (affineCoefficient φ N hN hA hB S hS d)

/-- The specified compact-support comparison for the bundle followed by its actual
pullback/Tate balancing. Geometry instances are furnished by the recorded construction.
Source: blueprint paragraph 2, tilde q_pi
(blueprint: lem-pur-vector-trace-scalar-descent). -/
def vector (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (scalarExtension φ S).obj (vectorIntegrationSource A N hA S d F) ⟶
      vectorIntegrationSource B N hB S d F :=
  letI := (vectorIntegration_geometry S d F).1
  letI := (vectorIntegration_geometry S d F).2.1
  (compactScalarChosenMap φ (VectorBundleZeroSection.π S d F)).app
      (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (VectorBundleZeroSection.π S d F)).map
      (pullBase φ N hN hA hB (VectorBundleZeroSection.π S d F) hS d)

/-- Scalar extension preserves the specified Kummer component, projective decomposition,
its second-projection trace, all coordinate-tower traces, and global vector integration.
Source: main-20261015, cor-pur-vector-bundle-purity.proof.md, paragraph 2, old Steps 9--10
(blueprint: lem-pur-vector-trace-scalar-descent).

Proof:
1. Fix the normalized scalar unit and Tate balancing. On K-flat flat degree-zero Tate
lines the scalar/single comparison is ordinary balancing; shifted tensor powers compute
all ranks. Pullback preserves the generator formula (z tensor a) tensor b maps to
z tensor phi(a)b. Use lem-asd-etale-finite-twist-pullback,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback and degree-zero full faithfulness.
2. Transpose the proper scalar mate using lem-asd-proper-finite-coefficient-extension.
Naturality of the scalar/pullback comparison and lem-sp-p1-kummer-derived-scalar identify
the two adjuncts of h with the same normalized Kummer arrow. Adjunction injectivity gives
the first equality. The triangle identity and pullback compatibility give the first
summand's equation, hence the decomposition equality by additivity.
3. Invert the two normalized decompositions and project to their second summands.
The biproduct projection identities give the projective-line trace equality.
4. The inverse open scalar comparison is the left mate of the inverse pullback comparison
(lem-pur-etale-open-scalar-composition). Apply lem-pur-adjunction-mate-transpose to the
open counit. Naturality of the proper comparison and Step 3 give the affine-line equation.
5. Tensor that equation with every shifted Tate input. The ordered projection square of
lem-pur-etale-compact-scalar-coherence and the open tensor/counit identity of
lem-pur-etale-open-derived-tensor give the affine-line counit equation on these inputs.
6. Induct through the ordered coordinate tower, starting with the identity at rank zero.
Use the actual composition scalar square, the preceding counit equation and naturality.
Every intermediate input and its scalar extension is a shifted flat Tate line, hence D+;
all bases remain Noetherian. Proper-refinement coherence identifies the resulting map
with the specified compactification comparison.
7. On a common Zariski frame cover use def-amb-vector-integration: the local maps are
exactly these affine traces. The actual open-restriction square and Cartesian exchange
for the inverse frame identify the scalar maps. Refinement removes compactification
choices. Thus the global equation holds on every frame open.
8. Local traces are invertible. Degree-zero concentration and cover detection make the
global trace invertible. Precompose the desired equality with the inverse of Q(t_A)
followed by u. Both maps are now endomorphisms of the constant degree-zero object.
Degree-zero full faithfulness and lem-pur-sheaf-hom-cover-gluing detect their equality;
cancel the inverse. This is descent only for these degree-zero sheaf maps.
9. Rank zero uses the identity adjunction and multiplication. On the empty base all
objects are zero. N=1 gives zero coefficient rings. No flatness of B over A, cohomology
base-change assertion, or general smooth-purity theorem enters this argument. -/
theorem vectorTraceScalarDescent (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (r : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank r] :
    ((scalarExtension φ S).map (ordinaryFiniteP1ChernPushforward A N hA S
        (projectiveLineTraceDatum N hN A hA S hS).chern) ≫
      projective φ N hN hA hB S hS =
      unit φ S ≫ ordinaryFiniteP1ChernPushforward B N hB S
        (projectiveLineTraceDatum N hN B hB S hS).chern) ∧
    ((scalarExtension φ S).map (projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
      projective φ N hN hA hB S hS =
      sum φ N hN hA hB S hS ≫ (projectiveLineTraceDatum N hN B hB S hS).decomposition.hom) ∧
    (projective φ N hN hA hB S hS ≫ projectiveLineTrace N hN B hB S hS =
      (scalarExtension φ S).map (projectiveLineTrace N hN A hA S hS) ≫ unit φ S) ∧
    (∀ d : ℕ, affine φ N hN hA hB S hS d ≫ affineTrace N hN B hB S hS d =
      (scalarExtension φ S).map (affineTrace N hN A hA S hS d) ≫ unit φ S) ∧
    (vector φ N hN hA hB S hS r F ≫ vectorBundleIntegration N hN B hB S hS r F =
      (scalarExtension φ S).map (vectorBundleIntegration N hN A hA S hS r F) ≫ unit φ S) := by
  sorry

end VectorTraceScalar
end AlgebraicGeometry.Etale
