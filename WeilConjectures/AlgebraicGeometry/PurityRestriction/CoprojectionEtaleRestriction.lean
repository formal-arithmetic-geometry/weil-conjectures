/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointTensor
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! # Étale restriction of the canonical invertible-factor co-projection

Source: current blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/sk-thm-regular.proof.md,
Steps 2 and 4(i)--(ii), and part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-trace/
sec-base-change-and-composition/sk-prop-sp-purity-bc/sk-lem-coprojection/
sk-lem-coprojection.proof.md, the displayed Hom calculation
(blueprint: lem-pur-coprojection-etale-restriction).

We use ordinary étale coordinates for the finite-coefficient constructible categories.
The final maps are their images under the actual derived site-comparison pullback, so
are morphisms in D(V_proet,A). All comparisons below are constructions, not parameters.
The finite-coefficient coefficient-model equivalence and counit-preserving adjunction
transfer identify these coordinates with the condensed-coefficient statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale.PurityRestriction

variable (A : Type (w + 1)) [CommRing A] [Finite A]

/-- The canonical counit-preserving étale identification, using the chosen
compactification and the recorded graph/sum comparison, followed by the canonical
exact-to-left-derived pullback comparison.
Source: sk-thm-regular, Step 4(i); lem-pur-etale-sum-right-adjoint-tensor
(blueprint: lem-pur-coprojection-etale-restriction). -/
def rho {T W : Scheme.{w}} (e : T ⟶ W) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedUpperShriek A e ≅ (upperStar (ModuleCat.{w + 1} A) e).leftDerivedFunctor :=
  etaleTensorRho A e (HasCompactification.compactification e)
    (rightDerivedUpperShriek A e) (rightDerivedUpperShriekAdjunction A e) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{w + 1} A) e).symm

section Square
variable {X Z U V : Scheme.{w}}
variable (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (j : V ⟶ U)
variable [AlgebraicGeometry.Etale u] [AlgebraicGeometry.Etale v]
variable [IsSeparated u] [IsSeparated v]
variable [HasCompactification i] [HasCompactification u]
variable [HasCompactification v] [HasCompactification j]
variable [HasCompactification (j ≫ u)] [HasCompactification (v ≫ i)]
variable [QuasiCompact j] [QuasiCompact v] [QuasiCompact u]
variable [QuasiCompact (j ≫ u)] [QuasiCompact (v ≫ i)]

/-- The displayed B, as a natural isomorphism. Its middle comparison is the canonical
compactification comparison for the equality of the two composite scheme maps.
Source: sk-thm-regular, Step 4(i), the chain Rj! u* = R(uj)! = R(iv)! = v* Ri!
(blueprint: lem-pur-coprojection-etale-restriction). -/
def B (sq : IsPullback j v u i) :
    (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor ⋙ rightDerivedUpperShriek A j ≅
      rightDerivedUpperShriek A i ⋙
        (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor :=
  Functor.isoWhiskerRight (rho A u).symm (rightDerivedUpperShriek A j) ≪≫
    (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A j u).symm ≪≫
    rightDerivedUpperShriekCongr A sq.w ≪≫
    WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition A v i ≪≫
    Functor.isoWhiskerLeft (rightDerivedUpperShriek A i) (rho A v)

/-- The canonical pullback-composition comparison of the square, with the same
composite map on both sides. No choice of a square isomorphism is involved.
Source: sk-thm-regular, Step 4(ii), pullback of the invertible factor
(blueprint: lem-pur-coprojection-etale-restriction). -/
def chi (sq : IsPullback j v u i) :
    (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{w + 1} A) j).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor :=
  (leftDerivedUpperStarComp (ModuleCat.{w + 1} A) j u).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{w + 1} A) v i (j ≫ u) sq.w

variable (sq : IsPullback j v u i)
variable (K L M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} A)))
variable (e : ((derivedTensor (ModuleCat.{w + 1} A) X).obj M).obj L ≅ constantComplex A X)
variable (e' : ((derivedTensor (ModuleCat.{w + 1} A) X).obj L).obj M ≅ constantComplex A X)

/-- Left side of the restriction square. The co-projection is the existing right-adjoint
comparison induced by projection at M and the two specified evaluations: its construction
is the test-object Hom chain, not a choice from Nonempty.
Source: sk-lem-coprojection, displayed Hom calculation; sk-thm-regular, Steps 2 and 4(ii)
(blueprint: lem-pur-coprojection-etale-restriction). -/
def leftArrow :
    (rightDerivedUpperShriek A j).obj
        ((upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor.obj
          (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L)) ⟶
      ((derivedTensor (ModuleCat.{w + 1} A) V).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((rightDerivedUpperShriek A i).obj K))).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L)) :=
  (B A i u v j sq).hom.app (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L) ≫
    (upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.map
      ((derivedTensorRightCompRightDerivedUpperShriekIso A i L M e e').hom.app K) ≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) v
      ((rightDerivedUpperShriek A i).obj K)
      ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L)).hom

/-- Right side of the restriction square. The evaluations for the j co-projection are
obtained by the actual pullback tensor and unit comparisons applied to e and e'.
Source: sk-thm-regular, Steps 2 and 4(ii), with the Hom chain of sk-lem-coprojection
(blueprint: lem-pur-coprojection-etale-restriction). -/
def rightArrow :
    (rightDerivedUpperShriek A j).obj
        ((upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor.obj
          (((derivedTensor (ModuleCat.{w + 1} A) X).obj K).obj L)) ⟶
      ((derivedTensor (ModuleCat.{w + 1} A) V).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((rightDerivedUpperShriek A i).obj K))).obj
        ((upperStar (ModuleCat.{w + 1} A) v).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{w + 1} A) i).leftDerivedFunctor.obj L)) :=
  let Su := (upperStar (ModuleCat.{w + 1} A) u).leftDerivedFunctor
  let eu := (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u M L).symm ≪≫
    Su.mapIso e ≪≫ leftDerivedUpperStarUnitIso (ModuleCat.{w + 1} A) u
  let eu' := (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u L M).symm ≪≫
    Su.mapIso e' ≪≫ leftDerivedUpperStarUnitIso (ModuleCat.{w + 1} A) u
  (rightDerivedUpperShriek A j).map
      (leftDerivedUpperStarTensorIso (ModuleCat.{w + 1} A) u K L).hom ≫
    (derivedTensorRightCompRightDerivedUpperShriekIso A j
      (Su.obj L) (Su.obj M) eu eu').hom.app (Su.obj K) ≫
    tensorHom ((B A i u v j sq).hom.app K) ((chi A i u v j sq).hom.app L)

end Square

/-- The co-projection restriction equation and its naturality, in finite-coefficient
ordinary étale coordinates followed by the actual site-comparison pullback.
Source: current blueprint sk-thm-regular, Steps 2 and 4(i)--(ii), and the full Hom
calculation in sk-lem-coprojection (blueprint: lem-pur-coprojection-etale-restriction).

Proof:
1. Base change makes v étale and j closed. Finite type over k and separatedness supply
   Noetherian qcqs schemes and Nagata compactifications of the arrows and composites.
2. Work in the ordinary étale realization. Conjugate the specified lower-shriek
   compositor to obtain c. Conjugate the graph/sum comparison to obtain rho, uniquely
   fixed by its evaluation-counit equation (etaleSumRightAdjointTensor).
3. The iterated-square-mates identity and the horizontal support-mate identity identify
   the inverse exchange mate with B, in the displayed order of its five factors.
4. Expand each co-projection using its tensorRightCompIsoOfTensorIso construction:
   adjunction; cancellation with M; projection at M; adjunction; cancellation back
   with L. Projection-formula/base-change coherence identifies the middle Hom arrows.
   The outer Hom arrows agree by the counit equations and mate pasting. Transpose back.
5. Strong monoidal pullback carries both evaluations to eu and eu'. Pullback composition
   identifies the two restrictions through chi. This gives leftArrow = rightArrow.
   All Hom arrows are natural in K and in evaluation-preserving invertible isomorphisms;
   applying the same calculation to these arrows gives the second clause below.
6. Apply derived comparisonUpperStar. Finite-Tor site equivalence, the finite discrete
   coefficient equivalence, and counit-preserving Brown-adjunction transfer identify
   this with the asserted equality in D(V_proet,A), including the same naturality.
   Unit, shifted, inverse-twist, identity-pullback and empty-scheme cases are covered
   by these constructions without an orientation or a choice of comparison maps.
-/
theorem coprojectionEtaleRestriction
    {k : Type w} [Field k] {p ell : ℕ}
    (hp : 0 < p) (hchar : ringChar k = p) (hpPrime : Nat.Prime p)
    (hellPrime : Nat.Prime ell) (hneq : ell ≠ p) (hk : Finite k ∨ IsAlgClosed k)
    (hA : ∃ N : ℕ, 1 ≤ N ∧ ∀ a : A, (ell ^ N) • a = 0)
    (X Z U V : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (i : Z ⟶ X) (u : U ⟶ X) (v : V ⟶ Z) (j : V ⟶ U)
    [IsClosedImmersion i.left] [AlgebraicGeometry.Etale u.left]
    (sq : IsPullback j.left v.left u.left i.left) :
    letI : AlgebraicGeometry.Etale v.left :=
      MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) sq inferInstance
    letI : IsClosedImmersion j.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip inferInstance
    letI : HasCompactification i.left := HasCompactification.of_over i
    letI : HasCompactification u.left := HasCompactification.of_over u
    letI : HasCompactification v.left := HasCompactification.of_over v
    letI : HasCompactification j.left := HasCompactification.of_over j
    letI : HasCompactification (j.left ≫ u.left) := HasCompactification.of_over (j ≫ u)
    letI : HasCompactification (v.left ≫ i.left) := HasCompactification.of_over (v ≫ i)
    letI : QuasiCompact u.left := by
      have : QuasiCompact (u.left ≫ X.hom) := by rw [u.w]; infer_instance
      exact QuasiCompact.of_comp u.left X.hom
    letI : QuasiCompact v.left := by
      have : QuasiCompact (v.left ≫ Z.hom) := by rw [v.w]; infer_instance
      exact QuasiCompact.of_comp v.left Z.hom
    letI : IsSeparated u.left := by
      have : IsSeparated (u.left ≫ X.hom) := by rw [u.w]; infer_instance
      exact IsSeparated.of_comp u.left X.hom
    letI : IsSeparated v.left := by
      have : IsSeparated (v.left ≫ Z.hom) := by rw [v.w]; infer_instance
      exact IsSeparated.of_comp v.left Z.hom
    let ν := (ProEtale.comparisonUpperStar (ModuleCat.{w + 1} A) V.left).mapDerivedCategory
    ∀ (K L M : _root_.DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{w + 1} A))),
    DerivedCategory.boundedConstructibleFiniteTor A X.left K →
    DerivedCategory.boundedConstructibleFiniteTor A X.left L →
    DerivedCategory.boundedConstructibleFiniteTor A X.left M →
    ∀ (e : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj M).obj L ≅
      constantComplex A X.left)
      (e' : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj L).obj M ≅
      constantComplex A X.left),
    ν.map (leftArrow A i.left u.left v.left j.left sq K L M e e') =
      ν.map (rightArrow A i.left u.left v.left j.left sq K L M e e') ∧
    ∀ (K' L' M' : _root_.DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{w + 1} A))),
    DerivedCategory.boundedConstructibleFiniteTor A X.left K' →
    DerivedCategory.boundedConstructibleFiniteTor A X.left L' →
    DerivedCategory.boundedConstructibleFiniteTor A X.left M' →
    ∀ (f : K ⟶ K') (l : L ≅ L') (m : M ≅ M')
      (d : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj M').obj L' ≅
        constantComplex A X.left)
      (d' : ((derivedTensor (ModuleCat.{w + 1} A) X.left).obj L').obj M' ≅
        constantComplex A X.left),
      tensorHom m.hom l.hom ≫ d.hom = e.hom →
      tensorHom l.hom m.hom ≫ d'.hom = e'.hom →
      let Gi := rightDerivedUpperShriek A i.left
      let Gj := rightDerivedUpperShriek A j.left
      let Su := (upperStar (ModuleCat.{w + 1} A) u.left).leftDerivedFunctor
      let Si := (upperStar (ModuleCat.{w + 1} A) i.left).leftDerivedFunctor
      let Sv := (upperStar (ModuleCat.{w + 1} A) v.left).leftDerivedFunctor
      ν.map (Gj.map (Su.map (tensorHom f l.hom)) ≫
        leftArrow A i.left u.left v.left j.left sq K' L' M' d d') =
      ν.map (leftArrow A i.left u.left v.left j.left sq K L M e e' ≫
        tensorHom (Sv.map (Gi.map f)) (Sv.map (Si.map l.hom))) := by
  sorry

end AlgebraicGeometry.Etale.PurityRestriction
