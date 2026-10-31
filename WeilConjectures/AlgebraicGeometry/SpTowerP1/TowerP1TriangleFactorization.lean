/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TriangleWords
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1FirstTraceReordering
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1SecondTraceReordering
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1DiagonalTransport
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1DiagonalProjectionFactor

/-! # Projective-line tower triangle composites as diagonal scalar contractions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities (blueprint: lem-sp-tower-p1-triangle-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

private theorem eta_factor (p : Presentation l E S hS) (d : Maps l E p)
    (M : C l E p.classes.base (ProjectiveLine S)) :
    eta l E d M = unitInsertion l E d M ≫ unitTail l E d M := by
  simp only [eta, unitInsertion, unitTail, Functor.map_comp, Category.assoc]

private theorem cancel_projection_word
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y : B} {Z W : A} (i : X ≅ Y) (f : Y ⟶ R.obj Z) [IsIso f]
    (j : Z ≅ W) :
    (i.hom ≫ f ≫ R.map j.hom) ≫ (R.map j.inv ≫ inv f ≫ i.inv) = 𝟙 X := by
  simp only [Category.assoc, ← R.map_comp_assoc, Iso.hom_inv_id, R.map_id,
    Category.id_comp, IsIso.hom_inv_id_assoc]

private theorem outside_projection_cancel (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :
    outsideProjection l E p a M.obj ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ≫
      outsideLineProjectionInverse l E h a M = 𝟙 _ := by
  let := h.projection_projections a M
  exact cancel_projection_word
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a)))
    ((p.tensorP.symmetry l E).braiding _ _)
    (projection l E (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) M.obj)
    ((p.tensorW.symmetry l E).braiding _ _)

private theorem expanded_eq_scalar (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d) (a : Bool)
    (M : C l E p.classes.base (ProjectiveLine S)) :
    expandedContraction l E h a M =
      scalarContraction l E p M.obj (diagonalScalar l E h a) := by
  rw [expandedContraction, towerP1DiagonalProjectionFactor l E p d h a M]
  rw [Category.assoc, ← Category.assoc
    (outsideProjection l E p a M.obj ((line l E p.classes.chernW)⟦(2 : ℤ)⟧))]
  rw [outside_projection_cancel l E p d h a M, Category.id_comp]
  simp only [diagonalTensorFactor, scalarContraction, diagonalScalar, Category.assoc]
  rw [← Functor.map_comp_assoc]
  apply congrArg (fun f ↦ (p.tensorP.rightUnit l E M.obj).inv ≫ f ≫
    (p.tensorP.rightUnit l E M.obj).hom)
  apply congrArg (SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).map
  simp only [prod_comp, Category.id_comp, Category.assoc]

attribute [local irreducible] unitInsertion unitTail contractionTail Presentation.pushSwap
  rightPullComparison diagonalInsertion expandedContraction

private theorem first_expanded (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d)
    (M : C l E p.classes.base (ProjectiveLine S)) :
    (p.F l E).map (eta l E d M) ≫ epsilon l E d ((left l E d).obj M) =
      (p.F l E).map (expandedContraction l E h false M) := by
  have ht := towerP1FirstTraceReordering l E p d h M
  have hz := (towerP1DiagonalTransport l E p d h).1 M
  calc
    _ = (p.F l E).map (unitInsertion l E d M) ≫
        ((p.F l E).map (unitTail l E d M) ≫
          epsilon l E d ((left l E d).obj M)) := by
      rw [eta_factor l E p d M, Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun f ↦ (p.F l E).map (unitInsertion l E d M) ≫ f) ht
    _ = (p.F l E).map (diagonalInsertion l E h false M) ≫
        (p.F l E).map (contractionTail l E h false M) := by
      rw [← Category.assoc, hz]
    _ = _ := by
      simp only [expandedContraction, contractionTail, Functor.map_comp]

private theorem second_expanded (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d)
    (K : C l E p.classes.base S) :
    eta l E d ((rightRestricted l E d).obj K) ≫ (p.G l E).map (epsilon l E d K) =
      expandedContraction l E h true ((rightRestricted l E d).obj K) := by
  have ht := towerP1SecondTraceReordering l E p d h K
  have hz := (towerP1DiagonalTransport l E p d h).2 K
  calc
    _ = unitInsertion l E d ((rightRestricted l E d).obj K) ≫
        (unitTail l E d ((rightRestricted l E d).obj K) ≫
          (p.G l E).map (epsilon l E d K)) := by
      rw [eta_factor l E p d ((rightRestricted l E d).obj K), Category.assoc]
    _ = _ := congrArg
      (fun f ↦ unitInsertion l E d ((rightRestricted l E d).obj K) ≫ f) ht
    _ = diagonalInsertion l E h true ((rightRestricted l E d).obj K) ≫
        contractionTail l E h true ((rightRestricted l E d).obj K) := by
      rw [← Category.assoc, hz]
    _ = _ := by
      simp only [expandedContraction, contractionTail]

/-- Both actual tower-derived triangle words factor through the two diagonal scalars.
The expanded words and their source factors specify the projection/exchange reordering;
the second expanded word uses p2 on GK, via p1*GK = p2*GK from qp1 = qp2.
No equality c_i=1 and no adjunction F ⊣ G is a hypothesis or conclusion.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities (blueprint: lem-sp-tower-p1-triangle-factorization).

Proof plan, the nine steps of the node:
1. Use the actual system tensor, pullback/direct-image adjunctions and square mates. Set
T=A_P(1)[2], T_W=A_W(1)[2]. The base-changed splitting traces satisfy t1 v_T=q*t_q and
 t2 u_T=q*t_q because pullback preserves the unit, Chern class, inverse splitting and projection.
2. Set C_M=(u_M^{-1} tensor 1) times inverse twist projection. Form the two forward words J1,J2
from RM tensor RT to RU(aM tensor T_W), exactly as in the node; no inverse of P_q^r(M,RT) is used.
3. Transpose both words under (qp1)* ⊣ R(qp1)*. Projection becomes counit tensor identity;
exchange becomes the pulled counit. Their common transpose is a(epsilon_M) tensor b(epsilon_T).
Mate pasting and tensor bifunctoriality give J1=J2 as actual derived maps.
4. Let D_M be inverse p1 projection followed by contraction with t1. Cancel the forward
projection in D_M J1, substitute trace base change, and use projection unit normalization.
Since J2=R(C_M^{-1}) P_q(RM,T), cancel it to get D_M=epsilon_RM R(C_M).
5. Insert the diagonal z_M. Section specialization of projection-composition coherence gives
its projected factor 1_M tensor U(delta) alpha1. Naturality of tensor gives the first scalar
identity and the displayed expanded first composite, with its alpha1 source retained.
6. The unshifted rank-one line has identity self-symmetry under multiplication: on a simultaneous
root frame, multiplication rs equals sr. The signed tensor symmetry moves [2] across degree j
with sign (-1)^(2j)=1 and swaps two shifted lines with sign (-1)^4=1, also at ell=2.
7. For N=GK, apply the actual exchange/tensor square at inside T and outside K. Invert its
canonical projection and exchange maps on the domains supplied by the comparison theorem.
8. Tensor associativity extracts the last T. The identity swap of the two pulled T factors
and the inverted square cancel C_N against G(epsilon_K); trace base change leaves 1_N tensor t2.
9. Section specialization for p2 identifies the projected z_N with 1_N tensor V(delta) alpha2.
Thus the second triangle is the second expanded contraction, and then 1_GK tensor c2.
Dependencies: lem-coef-semilinear-derived-sections, lem-sp-tower-p1-etale-origin-comparisons,
lem-sp-tower-p1-kernel-scalar-normalization (only trace base change), def-weil-pbc-adjunction-mate,
lem-weil-pbc-mate-pasting, lem-sfb-ringed-projection-tensor-composition,
lem-weil-pbc-adjunct-counit-identity, sk-def-sp-tate-twist, def-sp-tower-class-twisting,
def-pc-tensor-complex-sheaves, lem-weil-pbc-ringed-exchange-tensor-coherence,
lem-weil-pbc-ringed-projection-mate-exact.
-/
theorem towerP1TriangleFactorization (p : Presentation l E S hS) (d : Maps l E p)
    (h : EtaleOriginComparisonsWithLine l E p d) :
    (∀ M : C l E p.classes.base (ProjectiveLine S),
      (p.F l E).map (eta l E d M) ≫ epsilon l E d ((left l E d).obj M) =
        (p.F l E).map (scalarContraction l E p M.obj (diagonalScalar l E h false))) ∧
    (∀ K : C l E p.classes.base S,
      eta l E d ((rightRestricted l E d).obj K) ≫ (p.G l E).map (epsilon l E d K) =
        scalarContraction l E p ((p.G l E).obj K.obj) (diagonalScalar l E h true)) ∧
    (∀ M : C l E p.classes.base (ProjectiveLine S),
      (p.F l E).map (eta l E d M) ≫ epsilon l E d ((left l E d).obj M) =
        (p.F l E).map (expandedContraction l E h false M)) ∧
    (∀ K : C l E p.classes.base S,
      eta l E d ((rightRestricted l E d).obj K) ≫ (p.G l E).map (epsilon l E d K) =
        expandedContraction l E h true ((rightRestricted l E d).obj K)) ∧
    (∀ M : C l E p.classes.base (ProjectiveLine S),
      diagonalInsertion l E h false M =
        diagonalTensorFactor l E p false M.obj ≫
          outsideProjection l E p false M.obj ((line l E p.classes.chernW)⟦(2 : ℤ)⟧)) ∧
    (∀ K : C l E p.classes.base S,
      diagonalInsertion l E h true ((rightRestricted l E d).obj K) =
        diagonalTensorFactor l E p true ((p.G l E).obj K.obj) ≫
          outsideProjection l E p true ((p.G l E).obj K.obj)
            ((line l E p.classes.chernW)⟦(2 : ℤ)⟧)) := by
  refine ⟨?_, ?_, first_expanded l E p d h, second_expanded l E p d h, ?_, ?_⟩
  · intro M
    rw [first_expanded l E p d h M, expanded_eq_scalar l E p d h false M]
  · intro K
    rw [second_expanded l E p d h K,
      expanded_eq_scalar l E p d h true ((rightRestricted l E d).obj K)]
    rfl
  · intro M
    exact towerP1DiagonalProjectionFactor l E p d h false M
  · intro K
    exact towerP1DiagonalProjectionFactor l E p d h true ((rightRestricted l E d).obj K)

end AlgebraicGeometry.ProEtale.SpTowerP1
