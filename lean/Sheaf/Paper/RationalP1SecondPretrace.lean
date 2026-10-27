/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.RationalP1SecondPullComparison
public import Sheaf.Paper.RationalP1AmbientTail

/-! # The second projective-line calculation before applying a trace

Source: the second identity of the rational projective-line triangle calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The specified shifted Tate comparison on the first projection.
Source: rational projective-line triangle calculation, Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def firstLineComparisonForTrace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
        (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧ := by
  letI : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  letI : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  exact shiftedLineComparison l c (firstProjection Y)

/-- The forward scalar exchange on the shifted line, with its fixed root comparison.
Source: rational projective-line triangle calculation, Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTraceExchange
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ⟶
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
        0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) := by
  refine ?_ ≫ (moduleObjectDerivedPushforward (coefficient l c).X
    (secondProjection Y)).map (firstLineComparisonForTrace l c k p hpl Y).hom
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact (condensedAmbientExchange (coefficient l c).X (square Y)).app
    (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
      0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})

/-- Cache the actual canonical monoidal structure through the fixed functor names.
Source: extraction of q*K in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTracePullMonoidal :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).Monoidal := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle moduleObjectDerivedPullback
  exact monoidal_leftDerivedUpperStar Λ (ProjectiveLine Y ↘ Y)

/-- Cache the native derived Koszul braiding through the fixed tensor interface.
Source: extraction of q*K in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTraceBraided : BraidedCategory (DerivedCategory (Modules Λ (ProjectiveLine Y))) := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  letI : SymmetricCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1}) :=
    { sheafSymmetricCategory (ProjectiveLine Y) with
      toBraidedCategory := sheafBraidedCategory Ab.{u + 1} (ProjectiveLine Y) }
  exact DerivedCategory.braidedCategory' (Modules Λ (ProjectiveLine Y))

/-- The inverse unitator of the canonical monoidal derived pullback.
Source: the coefficient-unit comparison in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTraceUnitIso :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      (𝟙_ (DerivedCategory (Modules Λ Y))) ≅
      𝟙_ (DerivedCategory (Modules Λ (ProjectiveLine Y))) := by
  letI := secondTracePullMonoidal Λ Y
  exact (Functor.Monoidal.εIso
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y))).symm

/-- The tensorator of the canonical monoidal derived pullback, in the fixed interface.
Source: extraction of q*K in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTraceTensorIso (K V : DerivedCategory (Modules Λ Y)) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K ⊗
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V ≅
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj (K ⊗ V) := by
  letI := secondTracePullMonoidal Λ Y
  exact Functor.Monoidal.μIso
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) K V

/-- The native Koszul symmetry in the fixed tensor interface.
Source: extraction of q*K in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTraceSwap (A B : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    A ⊗ B ≅ B ⊗ A := by
  letI := secondTraceBraided Λ Y
  exact β_ A B

/-- Extract a further pulled factor from a twisted pulled object, before evaluation.
This is the tensorator, associators and native symmetry, conjugated by tensorShiftIso.
Source: extraction of q*K in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def secondTraceStrength (L : Modules Λ (ProjectiveLine Y))
    (K V : DerivedCategory (Modules Λ Y)) :
    (twist Λ (ProjectiveLine Y) L).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V ≅
    (twist Λ (ProjectiveLine Y) L).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj (K ⊗ V)) :=
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
    ⟦(2 : ℤ)⟧
  tensorIso (tensorShiftIso Λ (ProjectiveLine Y) L (F.obj K)).symm (Iso.refl _) ≪≫
    (α_ (F.obj K) T (F.obj V)) ≪≫
    tensorIso (Iso.refl _) (secondTraceSwap Λ Y T (F.obj V)) ≪≫
    (α_ (F.obj K) (F.obj V) T).symm ≪≫
    tensorIso (secondTraceTensorIso Λ Y K V) (Iso.refl T) ≪≫
    tensorShiftIso Λ (ProjectiveLine Y) L (F.obj (K ⊗ V))

/-- The projection part of the counit, before any scalar trace is applied.
Source: cancellation of the projection and its inverse in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
@[irreducible]
def counitProjectionPart (L : Modules Λ (ProjectiveLine Y))
    (K : DerivedCategory (Modules Λ Y))
    (hq : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
        ⟦(2 : ℤ)⟧))) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      ((twist Λ (ProjectiveLine Y) L).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)) ⟶
    K ⊗ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
        ⟦(2 : ℤ)⟧) :=
  haveI := hq
  (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (tensorShiftIso Λ (ProjectiveLine Y) L _).inv ≫
    inv (projectionMap Λ (ProjectiveLine Y ↘ Y) K _)

/-- The literal trace-free equation, checked before substituting a coefficient ring.
Its sole field is an equality of the specified maps, with no additional data.
Source: extraction of q*K in the Second identity
(blueprint: lem-sfb-rational-p1-second-pretrace). -/
structure SecondPretraceEquation (L : ∀ X : Scheme.{u}, Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M N X : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (V : DerivedCategory (Modules Λ Y))
    (f : (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ⟶ N)
    (x : X ⟶ (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V)
    (S : M ⊗ (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V ⟶ N)
    (J : M ⊗ X ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) : Prop where
  equation
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) :
    J ≫ unitTail Λ Y L e M hb hp ≫ f = (M ◁ x) ≫ S

/-- Exchange/projection reordering before applying any scalar trace.
The only inverses are the specified exchange and projection arrows. In particular,
this statement has no completed reference, diagonal class, counit, or trace map.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, extraction of q*K
(blueprint: lem-sfb-rational-p1-second-pretrace).

Proof: Write A=q*K and T=Lambda_P(1)[2]. Exchange/tensor coherence for the
self-square at inside T and outside K gives exchange_(A tensor T) after pullback
of projection_q(K,T) as projection_p2(A,p1*T) after identity tensor exchange_T,
with the native tensor and pullback composition comparisons. Invert this square
using hq, hb and hx. The two-factor projection law separates the final T factor
from the inverse twisted projection in unitTail. Both p1*T and p2*T are identified
with T_W by the root-normalized comparisons. Their degree-zero rank-one line has
identity self-symmetry, checked on a common root frame; the degree-two shifts
contribute (-1)^4=1. Thus the two-factor law has no remaining line transposition.
The p1/p2 comparison on A is ambientPullbackComparison and on the line it is the
specified root comparison, so the comparison on M is secondPullComparison. Cancel
the projection_q and its inverse in counitProjectionPart, and the tensorShiftIso
and its inverse. The remaining comparison is precisely secondTraceStrength and
identity tensor the inverse scalar exchange. No property of a trace is used. -/
theorem second_pretrace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
        0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hx : IsIso (secondTraceExchange l c k p hpl Y)) :
    SecondPretraceEquation (coefficient l c).X Y (line l c)
      (secondLineComparison l c k p hpl Y)
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          (K ⊗ (moduleObjectDerivedPushforward (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj
              (((DerivedCategory.singleFunctor (Modules (coefficient l c).X
                (ProjectiveLine Y)) 0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
          (counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y)) K hq)))
      (@inv _ _ _ _ (secondTraceExchange l c k p hpl Y) hx)
      (secondTraceStrength (coefficient l c).X Y (line l c (ProjectiveLine Y)) K
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
            0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))).hom
      (secondForwardProjection l c k p hpl Y K) := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
