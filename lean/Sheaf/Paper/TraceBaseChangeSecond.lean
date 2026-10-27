/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.ProEtaleProjectionExchangeMaps
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedProjectionTensorComposition
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons


/-!
# Trace and base change before the second triangle

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-int-restriction,
`sk-thm-int-restriction-line.proof.md`, (1), second triangle
(blueprint: lem-sfb-trace-base-change-second).

The tensor comparison is the existing representative-normalized comparison on internal
module objects. Projection and base change are its actual adjunction mates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u uA vA wA uB u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {W : Scheme.{u}} (p₁ p₂ : W ⟶ X) (sq : CommSq p₁ p₂ f f)

/-- G(K)=f^*K tensor f^*T. Source: blueprint (1), second triangle
(blueprint: lem-sfb-trace-base-change-second). -/
def traceG (T : TraceDerived Λ Y) :
    TraceDerived Λ Y ⥤ TraceDerived Λ X :=
  (tracePull Λ f) ⋙
    (derivedTensor Λ X).flip.obj ((tracePull Λ f).obj T)

/-- The displayed counit, using the inverse of the specified projection map.
Source: blueprint e_K formula (blueprint: lem-sfb-trace-base-change-second). -/
noncomputable def traceCounit (T K : TraceDerived Λ Y)
    (t : (tracePush Λ f).obj
      ((tracePull Λ f).obj T) ⟶ 𝟙_ (TraceDerived Λ Y))
    (hp : IsIso (traceProjection Λ f K ((tracePull Λ f).obj T))) :
  (tracePush Λ f).obj ((traceG Λ f T).obj K) ⟶ K :=
  letI := hp
  inv (traceProjection Λ f K ((tracePull Λ f).obj T)) ≫
    (K ◁ t) ≫ (ρ_ K).hom

/-- The canonical identification p1^*GK=p2^*GK from the tensor and composition comparisons.
Source: blueprint right side of the second triangle
(blueprint: lem-sfb-trace-base-change-second). -/
noncomputable def traceSquareG (T K : TraceDerived Λ Y) :
    (tracePull Λ p₁).obj ((traceG Λ f T).obj K) ≅
      (tracePull Λ p₂).obj ((traceG Λ f T).obj K) :=
  ((traceTensorComparison Λ p₁).app
      ((tracePull Λ f).obj K)).app
        ((tracePull Λ f).obj T) ≪≫
    tensorIso ((traceSquarePullback Λ f p₁ p₂ sq).symm.app K)
      ((traceSquarePullback Λ f p₁ p₂ sq).symm.app T) ≪≫
    (((traceTensorComparison Λ p₂).app
      ((tracePull Λ f).obj K)).app
        ((tracePull Λ f).obj T)).symm

/-- B_N, with T_W=p1^*f^*T; the comparison changes it to p2^*f^*T before projection.
Every inverse in this definition inverts the map actually displayed, using its IsIso proof.
Source: blueprint B_N formula (blueprint: lem-sfb-trace-base-change-second). -/
noncomputable def traceB (T : TraceDerived Λ Y) (N : TraceDerived Λ X)
    (hb : IsIso ((traceBaseChange Λ f p₁ p₂ sq).app N))
    (hp : IsIso (traceProjection Λ p₂ ((tracePull Λ f).obj T)
      ((tracePull Λ p₁).obj N))) :
    (tracePush Λ p₂).obj
        ((tracePull Λ p₁).obj N ⊗
          (tracePull Λ p₁).obj ((tracePull Λ f).obj T)) ⟶
      (traceG Λ f T).obj ((tracePush Λ f).obj N) :=
  letI := hb
  letI := hp
  (tracePush Λ p₂).map
      ((traceBraiding Λ W ((tracePull Λ p₁).obj N)
          ((tracePull Λ p₁).obj ((tracePull Λ f).obj T))).hom ≫
        ((traceSquarePullback Λ f p₁ p₂ sq).inv.app T ▷
          (tracePull Λ p₁).obj N)) ≫
    inv (traceProjection Λ p₂ ((tracePull Λ f).obj T)
      ((tracePull Λ p₁).obj N)) ≫
    (traceBraiding Λ X ((tracePull Λ f).obj T)
      ((tracePush Λ p₂).obj ((tracePull Λ p₁).obj N))).hom ≫
    (inv ((traceBaseChange Λ f p₁ p₂ sq).app N) ▷
      (tracePull Λ f).obj T)

/-- Exactly the restricted invertibility and preservation assumptions of the node.
No map is required to be invertible on objects outside Loc(Dbc).
Source: blueprint hypotheses before G (blueprint: lem-sfb-trace-base-change-second). -/
structure TraceSecondHypotheses (T : TraceDerived Λ Y) : Prop where
  /-- Pullback along f preserves the given closure. -/
  pull_f : ∀ K, TraceLoc Λ Y K →
    TraceLoc Λ X ((tracePull Λ f).obj K)
  /-- Direct image along f preserves the given closure. -/
  push_f : ∀ N, TraceLoc Λ X N →
    TraceLoc Λ Y ((tracePush Λ f).obj N)
  /-- Both projections' inverse images preserve the closure. -/
  pull_projections : ∀ N, TraceLoc Λ X N →
    TraceLoc Λ W ((tracePull Λ p₁).obj N) ∧
      TraceLoc Λ W ((tracePull Λ p₂).obj N)
  /-- Both projections' direct images preserve the closure. -/
  push_projections : ∀ N, TraceLoc Λ W N →
    TraceLoc Λ X ((tracePush Λ p₁).obj N) ∧
      TraceLoc Λ X ((tracePush Λ p₂).obj N)
  /-- The displayed twisted pullback preserves the closure. -/
  twisted_pull : ∀ K, TraceLoc Λ Y K →
    TraceLoc Λ X ((traceG Λ f T).obj K)
  /-- The source functor of B preserves the closure. -/
  twisted_projection_pull : ∀ N, TraceLoc Λ X N →
    TraceLoc Λ W ((tracePull Λ p₁).obj N ⊗
      (tracePull Λ p₁).obj ((tracePull Λ f).obj T))
  /-- Both canonical base-change maps are invertible on the closure. -/
  base_change : ∀ N, TraceLoc Λ X N →
    IsIso ((traceBaseChange Λ f p₁ p₂ sq).app N) ∧
      IsIso ((traceBaseChange Λ f p₂ p₁ sq.flip).app N)
  /-- The projection used in e is invertible for K in the closure. -/
  projection_f : ∀ K, TraceLoc Λ Y K →
    IsIso (traceProjection Λ f K ((tracePull Λ f).obj T))
  /-- The projection used in B is invertible for N in the closure. -/
  projection_B : ∀ N, TraceLoc Λ X N →
    IsIso (traceProjection Λ p₂ ((tracePull Λ f).obj T)
      ((tracePull Λ p₁).obj N))
  /-- The projection used on the right is invertible for K in the closure. -/
  projection_rhs : ∀ K, TraceLoc Λ Y K →
    IsIso (traceProjection Λ p₂ ((traceG Λ f T).obj K)
      ((tracePull Λ p₁).obj ((tracePull Λ f).obj T)))

/-- The integral coefficient ring fixed by ell and E. Source: blueprint (1)
(blueprint: lem-sfb-trace-base-change-second). -/
abbrev traceIntegralCoefficients (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  Profinite.padicIntegersRingObj.{u} ℓ E.1

/-- T_X=f^*T_Y. Source: blueprint (1)
(blueprint: lem-sfb-trace-base-change-second). -/
def traceIntegralTX (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (tracePull (traceIntegralCoefficients ℓ E) f).obj (traceTate ℓ E Y)

/-- T_W=p1^*T_X, with p2^*T_X identified by traceSquarePullback.
Source: blueprint (1) (blueprint: lem-sfb-trace-base-change-second). -/
def traceIntegralTW (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (p₁ : W ⟶ X) :=
  (tracePull (traceIntegralCoefficients ℓ E) p₁).obj
    (traceIntegralTX ℓ E f)

/-- Trace/base-change rearrangement before the second triangle.
Source: blueprint main-20261015, sk-thm-int-restriction-line.proof.md, (1), second triangle
(blueprint: lem-sfb-trace-base-change-second).

Proof (the six steps of the DAG):
1. Work in the ambient unbounded module-derived categories. Cartesian coefficients and
   lem-sfb-ringed-derived-monoidal-comparisons identify successive pullbacks, tensor,
   unit and composition comparisons. Put r=p2, a=f^*K, T=T_X, V=r^*T and S=Rr_*V.
   All inverses are justified on Loc(Dbc) by the restricted assumptions.
2. V is the even shifted rank-one Tate line R_W(1)[2]. On a trivializing cover its
   degree -2 one-term complex is flat, hence K-flat by
   lem-weil-pbc-independent-bounded-flat-kflat. The signed symmetry has sign
   (-1)^((-2)(-2))=1; on a generator the ordinary flip is identity. This equality is
   an equality of chain maps, which descends to the derived category. Use
   sk-def-sp-tate-twist and lem-sf-ringed-derived-closed-symmetric-monoidal.
3. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to (p2,f,p1) and (T,K).
   Its exchange is the actual mate b2 by def-weil-pbc-adjunction-mate. With
   lambda=pi_(r,a,V), tensor symmetries give
   b_GK f^*(pi_f)=lambda(1 tensor b_T). Invert this identity to obtain
   f^*(pi_f^-1)b_GK^-1=(1 tensor b_T^-1)lambda^-1.
4. Put H=Rr_*(U tensor V tensor V), where U=r^*a, and let q be the right-factor
   projection. Expand B_GK=(b_GK^-1 tensor 1)q^-1 and G(e_K). Substitute step 3,
   and then t2 b_T=f^*t, to obtain (1 tensor t2 tensor 1)D, where
   D=(lambda^-1 tensor 1)q^-1. The first trace equation is retained but unused here.
5. Put psi=pi_(r,a tensor T,V). The two-factor law of
   lem-sfb-ringed-projection-tensor-composition gives
   q(lambda tensor 1)=Rr_*(1 tensor sigma_(V,V))psi(1 tensor sigma_(S,T)).
   Step 2 removes the transposition, so psi^-1=(1 tensor sigma_(S,T))D.
6. Naturality of symmetry with t2 and the unitors changes
   (1 tensor t2 tensor 1)D to (1_(a tensor T) tensor t2)psi^-1. This is the required
   right side. traceSquareG is exactly its p1^*GK=p2^*GK identification from step 1.
   Preservation of the specified localizing categories restricts the identity there. -/
theorem traceBaseChangeSecond
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y W : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (p₁ p₂ : W ⟶ X) [p₁.IsOver (Spec (.of k))] [p₂.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare p₁ p₂ f f)
    (h : TraceSecondHypotheses (traceIntegralCoefficients ℓ E) f p₁ p₂ sq.toCommSq
      (traceTate ℓ E Y))
    (t : (tracePush (traceIntegralCoefficients ℓ E) f).obj
      (traceIntegralTX ℓ E f) ⟶ 𝟙_ (TraceDerived (traceIntegralCoefficients ℓ E) Y))
    (t₁ : (tracePush (traceIntegralCoefficients ℓ E) p₁).obj
      (traceIntegralTW ℓ E f p₁) ⟶ 𝟙_ (TraceDerived (traceIntegralCoefficients ℓ E) X))
    (t₂ : (tracePush (traceIntegralCoefficients ℓ E) p₂).obj
      (traceIntegralTW ℓ E f p₁) ⟶ 𝟙_ (TraceDerived (traceIntegralCoefficients ℓ E) X))
    (ht₁ : (traceBaseChange (traceIntegralCoefficients ℓ E) f p₂ p₁ sq.toCommSq.flip).app
        (traceIntegralTX ℓ E f) ≫
      (tracePush (traceIntegralCoefficients ℓ E) p₁).map
        ((traceSquarePullback (traceIntegralCoefficients ℓ E) f p₁ p₂ sq.toCommSq).hom.app
          (traceTate ℓ E Y)) ≫ t₁ =
      (tracePull (traceIntegralCoefficients ℓ E) f).map t ≫
        (condensedDerivedUnitIso (traceIntegralCoefficients ℓ E) f).hom)
    (ht₂ : (traceBaseChange (traceIntegralCoefficients ℓ E) f p₁ p₂ sq.toCommSq).app
        (traceIntegralTX ℓ E f) ≫ t₂ =
      (tracePull (traceIntegralCoefficients ℓ E) f).map t ≫
        (condensedDerivedUnitIso (traceIntegralCoefficients ℓ E) f).hom)
    (K : TraceDerived (traceIntegralCoefficients ℓ E) Y)
    (hK : TraceLoc (traceIntegralCoefficients ℓ E) Y K) :
    traceB (traceIntegralCoefficients ℓ E) f p₁ p₂ sq.toCommSq (traceTate ℓ E Y)
        ((traceG (traceIntegralCoefficients ℓ E) f (traceTate ℓ E Y)).obj K)
        (h.base_change _ (h.twisted_pull K hK)).1
        (h.projection_B _ (h.twisted_pull K hK)) ≫
      (traceG (traceIntegralCoefficients ℓ E) f (traceTate ℓ E Y)).map
        (traceCounit (traceIntegralCoefficients ℓ E) f (traceTate ℓ E Y) K t
          (h.projection_f K hK)) =
      (tracePush (traceIntegralCoefficients ℓ E) p₂).map
          ((traceSquareG (traceIntegralCoefficients ℓ E) f p₁ p₂ sq.toCommSq
            (traceTate ℓ E Y) K).hom ▷ traceIntegralTW ℓ E f p₁) ≫
        @inv _ _ _ _
          (traceProjection (traceIntegralCoefficients ℓ E) p₂
            ((traceG (traceIntegralCoefficients ℓ E) f (traceTate ℓ E Y)).obj K)
            (traceIntegralTW ℓ E f p₁)) (h.projection_rhs K hK) ≫
        ((traceG (traceIntegralCoefficients ℓ E) f (traceTate ℓ E Y)).obj K ◁ t₂) ≫
        (ρ_ ((traceG (traceIntegralCoefficients ℓ E) f (traceTate ℓ E Y)).obj K)).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
