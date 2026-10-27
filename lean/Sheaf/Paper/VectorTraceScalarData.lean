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

/-! # Canonical scalar maps for vector-bundle traces

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, old Steps 9--10
(blueprint: def-pur-vector-trace-scalar-coefficient-data).

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
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
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
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
def line (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  finiteTateScalarLineMap φ N hA hB T 1 (balancing φ N hN hA hB T hT 1)

/-- Multiplication on the constant coefficient complex, with the published single/unit
identifications. Source: blueprint paragraph 2, u_T
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
abbrev unit (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtension φ T).obj (ordinaryFiniteUnit A T) ⟶ ordinaryFiniteUnit B T :=
  purityScalarUnitMap φ T

/-- The tensor powers of shifted balanced lines, starting with multiplication at rank
zero. This is l in the ordered shifted-Tate presentation already used by integration;
no orientation or new Tate object is chosen.
Source: blueprint paragraph 2, l_{T,d}
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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
(blueprint: def-pur-vector-trace-scalar-map-data). -/
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

end VectorTraceScalar
end AlgebraicGeometry.Etale
