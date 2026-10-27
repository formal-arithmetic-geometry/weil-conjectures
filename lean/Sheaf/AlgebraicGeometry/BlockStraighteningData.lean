/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
public import Sheaf.RingTheory.FormalInitialDiagram
public import Sheaf.RingTheory.FiniteCoefficientExpression
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion


/-!
# One block of derivative straightening and exact projection transport

Source: Bierstone--Milman, Invent. Math. 128 (1997), Theorem 9.6, (9.7)--(9.8),
Remarks 9.9--9.11, pp.279--280; the stored-projection refinement in the DAG
(blueprint: def-trf-block-straightening-data).

The helpers specify this block's input and output; they do not choose an implicit
solution, a Taylor homomorphism, a coordinate change, or a projection. Degree blocks
are indexed by their degrees, so indices before the present block have degree < d.
The full variable numbering is w, then y, then T. In particular it uses an actual
linear order, rather than the incomparable summands of the default Sum relation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

/-- Number the current chart variables in the required order w,y,T.
Source: BM (9.7) (blueprint: def-trf-block-straightening-data). -/
def blockVariableEquiv (m r t : ℕ) :
    ((Fin m ⊕ Fin r) ⊕ Fin t) ≃ Fin ((m + r) + t) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin t))).trans finSumFinEquiv

/-- The inclusion of the old formal variables in the ordered full variable list.
Source: BM (9.7) (blueprint: def-trf-block-straightening-data). -/
def blockOldVariable (m r t : ℕ) (j : Fin t) : Fin ((m + r) + t) :=
  blockVariableEquiv m r t (Sum.inr j)

/-- The inclusion of the newly essential variables in the ordered full variable list.
Source: BM (9.7) (blueprint: def-trf-block-straightening-data). -/
def blockNewVariable (m r t : ℕ) (j : Fin r) : Fin ((m + r) + t) :=
  blockVariableEquiv m r t (Sum.inl (Sum.inr j))

/-- All transverse variables, new before old, as members of the full ordered list.
Source: BM (9.7) (blueprint: def-trf-block-straightening-data). -/
def blockTransverseVariable (m r t : ℕ) : Fin (r + t) → Fin ((m + r) + t) :=
  Sum.elim (blockNewVariable m r t) (blockOldVariable m r t) ∘ finSumFinEquiv.symm

/-- Adapt the existing coefficient flattening to the split regular chart (w,y).
First rename its coefficient variables by Fin m + Fin r = Fin (m+r), then use
flattenFormalCoefficients and rename the resulting (w,y),T variables in that order.
This differs from blockFlatten, whose coefficient variables already have type Fin m.
Source: BM Remark 9.9 (blueprint: def-trf-block-straightening-data). -/
def blockFlattenChart {m r t : ℕ} {R : Type u} [CommRing R]
    (F : MvPowerSeries (Fin t) (MvPowerSeries (Fin m ⊕ Fin r) R)) :
    MvPowerSeries (Fin ((m + r) + t)) R :=
  MvPowerSeries.rename finSumFinEquiv
    (MvPowerSeries.flattenFormalCoefficients
      (MvPowerSeries.map (MvPowerSeries.renameEquiv R finSumFinEquiv).toRingHom F))

/-- The old-variable part of a full exponent, without any support assumption.
Source: BM (9.8) (blueprint: def-trf-block-straightening-data). -/
def blockOldExponent {m r t : ℕ} (β : Fin ((m + r) + t) →₀ ℕ) : Fin t →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j ↦ β (blockOldVariable m r t j))

/-- Restrict a full exponent to the newly essential regular variables y.
This is an exponent-valued restriction, unlike the predicate blockNewExponent
for membership in the finite set of newly forbidden coefficient tests.
Source: BM (9.8) (blueprint: def-trf-block-straightening-data). -/
def blockNewVariableExponent {m r t : ℕ} (β : Fin ((m + r) + t) →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j ↦ β (blockNewVariable m r t j))

/-- The mixed derivative: regular coordinate derivations in y and formal ones in T.
Source: BM (9.8)(b) (blueprint: def-trf-block-straightening-data). -/
def blockDerivative {k : Type u} [Field k] {B : Scheme.{u}} {m r t : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (β : Fin ((m + r) + t) →₀ ℕ)
    (F : MvPowerSeries (Fin t) Γ(B, ⊤)) : MvPowerSeries (Fin t) Γ(B, ⊤) :=
  fun γ ↦ implicitIteratedDerivative (D.deriv ⊤) (blockNewVariableExponent β)
    (MvPowerSeries.coeff γ (iteratedPartial (blockOldExponent β) F))

/-- Evaluate the mixed derivative at T=0, an actual global regular function.
Source: BM (9.8)(b) (blueprint: def-trf-block-straightening-data). -/
def blockEquations {k : Type u} [Field k] {B : Scheme.{u}} {m r t s : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (pick : Fin (r + t) → Fin s) (β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ) :
    Fin r → Γ(B, ⊤) :=
  fun j ↦ MvPowerSeries.constantCoeff
    (blockDerivative D (β (finSumFinEquiv (Sum.inl j)))
      (f (pick (finSumFinEquiv (Sum.inl j)))))

/-- A prefix test extracts its fixed exponent and retains exactly the complementary
old variables. Its value is a full series, not its value at the origin.
Source: BM (9.8)(d) (blueprint: def-trf-block-straightening-data). -/
def blockTestAt {m r t s : ℕ} (α : Fin s → Fin ((m + r) + t) →₀ ℕ)
    (q Q : ℕ) (E : MvPowerSeries.FormalCoefficientTest t) : Prop :=
  (∃ i : Fin s, (α i).degree = q) ∧ E.fixed.degree ≤ Q ∧
    inDiagram α q (Finsupp.mapDomain (blockOldVariable m r t) E.fixed) ∧
    ∀ j : Fin t, (j ∈ Set.range E.inclusion ↔ ¬ essential α q (blockOldVariable m r t j))

/-- Index all old tests, allowing repeated enumerations of complementary variables.
Source: BM (9.8)(d) (blueprint: def-trf-block-straightening-data). -/
def BlockEarlierTest {m r t s : ℕ} (α : Fin s → Fin ((m + r) + t) →₀ ℕ)
    (d Q : ℕ) : Type :=
  {p : ℕ × MvPowerSeries.FormalCoefficientTest t // p.1 < d ∧ blockTestAt α p.1 Q p.2}

/-- The old test itself, for the existing common-kernel and projection interfaces.
Source: BM (9.8)(d) (blueprint: def-trf-block-straightening-data). -/
def blockEarlierTests {m r t s : ℕ} (α : Fin s → Fin ((m + r) + t) →₀ ℕ)
    (d Q : ℕ) (E : BlockEarlierTest α d Q) : MvPowerSeries.FormalCoefficientTest t :=
  E.val.2

/-- A monomial passes the old tests when none extracts its old-variable exponent.
The condition is independent of the complementary coefficient monomial.
Source: stored-projection refinement, step 7
(blueprint: def-trf-block-straightening-data). -/
def blockMonomialPasses {m r t s : ℕ} (α : Fin s → Fin ((m + r) + t) →₀ ℕ)
    (d Q : ℕ) (η : Fin ((m + r) + t) →₀ ℕ) : Prop :=
  ∀ E : BlockEarlierTest α d Q, ∀ γ : Fin (blockEarlierTests α d Q E).kept →₀ ℕ,
    blockOldExponent η ≠ (blockEarlierTests α d Q E).fixed +
      γ.mapDomain (blockEarlierTests α d Q E).inclusion

/-- The completed operator's first-exponent property at the specified center.
Source: stored-projection refinement, step 7
(blueprint: def-trf-block-straightening-data). -/
def blockPreservesFirst {m r t s : ℕ} {R L : Type u} [CommRing R] [Field L]
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (P : MvPowerSeries.FiniteCoefficientExpression R t 1 t 1)
    (τ : R →+* MvPowerSeries (Fin m ⊕ Fin r) L) : Prop :=
  ∀ (H : MvPowerSeries (Fin t) (MvPowerSeries (Fin m ⊕ Fin r) L))
      (η : Fin ((m + r) + t) →₀ ℕ),
    MonomialDiagram.IsFirstExponent (blockFlattenChart H) η → blockMonomialPasses α d Q η →
      MonomialDiagram.IsFirstExponent (blockFlattenChart ((P.map τ).scalarEval H)) η

/-- Earlier derivative equations and their invertible transverse Jacobians, for
all degree prefixes already constructed. Membership means vanishing as a full
series in the complementary variables. These are the earlier smooth coefficient
stages after their specified identifications with T=0, as in Remark 9.9.
Source: BM (9.8)(b), Remark 9.10
(blueprint: def-trf-block-straightening-data). -/
def blockOldStages {m r t s : ℕ} {L : Type u} [Field L]
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d : ℕ)
    (pick : Fin (r + t) → Fin s) (β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ)
    (F : Fin s → MvPowerSeries (Fin ((m + r) + t)) L) : Prop := by
  classical
  exact ∀ q : ℕ, q < d → (∃ i : Fin s, (α i).degree = q) →
    (∀ j : Fin t, essential α q (blockOldVariable m r t j) →
      iteratedPartial (β (finSumFinEquiv (Sum.inr j)))
        (F (pick (finSumFinEquiv (Sum.inr j)))) ∈
      Ideal.span {g | ∃ l : Fin t, essential α q (blockOldVariable m r t l) ∧
        g = MvPowerSeries.X (blockOldVariable m r t l)}) ∧
    IsUnit (Matrix.det
      (fun j l : {j : Fin t // essential α q (blockOldVariable m r t j)} ↦
        MvPowerSeries.constantCoeff (MvPowerSeries.pderiv L (blockOldVariable m r t l.val)
          (iteratedPartial (β (finSumFinEquiv (Sum.inr j.val)))
            (F (pick (finSumFinEquiv (Sum.inr j.val))))))))

/-- Input to a single block. The Taylor maps and coordinate derivations are the
existing characterized maps, not additional algebraic assumptions. The old smooth
closed stages enter through their inherited Taylor ideals and derivative equations.
Source: BM (9.7)--(9.8), Remarks 9.9--9.10
(blueprint: def-trf-block-straightening-data). -/
structure BlockStraighteningInput {k : Type u} [Field k] [CharZero k]
    (B : Scheme.{u}) {m r t s : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) (a : B)
    (D : ImplicitCoordinateDerivations B c)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (pick : Fin (r + t) → Fin s) (β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ) where
  etale : Etale (implicitCoordinateMorphism c)
  smooth : Smooth (implicitStructureMorphism c)
  finite_type : LocallyOfFiniteType (implicitStructureMorphism c) ∧
    QuasiCompact (implicitStructureMorphism c)
  taylor : ∀ b : B, Γ(B, ⊤) →+* MvPowerSeries (Fin m ⊕ Fin r) (B.residueField b)
  taylor_spec : ∀ b : B, isTaylorMap c (B.Γevaluation b).hom (taylor b)
  ideal : ∀ b : B, Ideal (MvPowerSeries (Fin t)
    (MvPowerSeries (Fin m ⊕ Fin r) (B.residueField b)))
  membership : ∀ (b : B) (i : Fin s), MvPowerSeries.map (taylor b) (f i) ∈ ideal b
  generation : ∀ b : B, ideal b =
    Ideal.span (Set.range fun i : Fin s ↦ MvPowerSeries.map (taylor b) (f i))
  first : ∀ i : Fin s,
    MonomialDiagram.IsFirstExponent (blockFlattenChart (MvPowerSeries.map (taylor a) (f i))) (α i)
  monotone : MonomialDiagram.IsMonotone (MonomialDiagram.generated α)
  vertices : MonomialDiagram.IsOrderedVertexFamily (MonomialDiagram.generated α) α
  current_block : ∃ i : Fin s, (α i).degree = d
  old_variables : ∀ j : Fin ((m + r) + t),
    (∃ i : Fin s, (α i).degree < d ∧ 0 < α i j) ↔
      j ∈ Set.range (blockOldVariable m r t)
  current_variables : ∀ j : Fin ((m + r) + t), essential α d j ↔
    j ∈ Set.range (blockTransverseVariable m r t)
  bound : ∀ i : Fin s, (α i).degree - 1 ≤ Q
  vertex_derivative : ∀ j : Fin (r + t),
    α (pick j) = β j + Finsupp.single (blockTransverseVariable m r t j) 1
  first_block : ∀ (j : Fin (r + t)) (i : Fin s),
    0 < α i (blockTransverseVariable m r t j) → (α (pick j)).degree ≤ (α i).degree
  beta_supported : ∀ (j : Fin (r + t)) (l : Fin ((m + r) + t)),
    β j l ≠ 0 → essential α (α (pick j)).degree l
  old_stages : ∀ b : B, blockOldStages α d pick β
    (fun i ↦ blockFlattenChart (MvPowerSeries.map (taylor b) (f i)))
  old_tests : ∀ (q : ℕ), q < d → ∀ i : Fin s, q < (α i).degree →
    ∀ E : MvPowerSeries.FormalCoefficientTest t, blockTestAt α q Q E → E.eval (f i) = 0

/-- The global coefficient after straightening, before Taylor expansion on C.
The inverse factorial is taken in the characteristic-zero ground field, then
restricted along the actual coefficient-scheme inclusion.
Source: BM Remark 9.11
(blueprint: def-trf-block-straightening-data). -/
def blockRegularCoefficient {k : Type u} [Field k] {B C : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    (D : ImplicitCoordinateDerivations B c) (j : C ⟶ B)
    (δ : Fin r →₀ ℕ) (g : Γ(B, ⊤)) : Γ(C, ⊤) :=
  j.appTop (c (MvPolynomial.C (((δ.prod fun _ n ↦ n.factorial : ℕ) : k)⁻¹)) *
    implicitIteratedDerivative (D.deriv ⊤) δ g)

/-- The completed coefficient homomorphism after the canonical graph substitution.
Source: BM Remark 9.9 (blueprint: def-trf-block-straightening-data). -/
def blockPointCoefficientMap {k : Type u} [Field k] [CharZero k]
    {B C : Scheme.{u}} {m r : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    {h : Fin r → Γ(B, ⊤)} {D : ImplicitCoordinateDerivations B c}
    {j : C ⟶ B} {b : C} (p : ImplicitTaylorPoint.{u, u} c h D j b) :
    Γ(B, ⊤) →+* MvPowerSeries (Fin m ⊕ Fin r) (C.residueField b) :=
  p.straight.toRingHom.comp (p.taylor.comp (B.presheaf.germ ⊤ (j b) (by trivial)).hom)

/-- A regular stored projection has exactly the properties assumed in the node.
Its ideal correction is for arbitrary inputs, and its first-exponent property is
on the completed ring at a. No truncation replaces any correction column.
Source: stored-projection refinement, steps 6--7
(blueprint: def-trf-block-straightening-data). -/
def blockProjectionHypotheses {m r t s : ℕ} {R L : Type u} [CommRing R] [Field L]
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) R)
    (τ : R →+* MvPowerSeries (Fin m ⊕ Fin r) L)
    (P : MvPowerSeries.FiniteCoefficientExpression R t 1 t 1) : Prop :=
  P.IsKernelProjection (blockEarlierTests α d Q) ∧
    (∀ H : MvPowerSeries (Fin t) R, P.scalarEval H - H ∈
      Ideal.span {g | ∃ i : Fin s, (α i).degree < d ∧ g = f i}) ∧
    (∀ i : Fin s, d ≤ (α i).degree → P.scalarEval (f i) = f i) ∧
    blockPreservesFirst α d Q P τ

/-- The conclusions for a stored projection on the common coefficient scheme C.
Both the regular Y-family and every unrestricted centered formal input occur.
The zero-test identity follows from the projection clause; the explicit coefficient
clause records that the old tests vanish in every Y degree, not only at Y=0.
Source: stored-projection refinement, steps 6--7
(blueprint: def-trf-block-straightening-data). -/
def blockProjectionConclusions {k : Type u} [Field k] [CharZero k]
    {B C : Scheme.{u}} {m r t s : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    {h : Fin r → Γ(B, ⊤)} {D : ImplicitCoordinateDerivations B c}
    (j : C ⟶ B) (center : C)
    (points : ∀ b : C, ImplicitTaylorPoint.{u, u} c h D j b)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (ρ : Γ(B, ⊤) →+* MvPowerSeries (Fin r) Γ(C, ⊤))
    (P : MvPowerSeries.FiniteCoefficientExpression Γ(B, ⊤) t 1 t 1) : Prop :=
  (P.map ρ).IsKernelProjection (blockEarlierTests α d Q) ∧
    (∀ H : MvPowerSeries (Fin t) (MvPowerSeries (Fin r) Γ(C, ⊤)),
      (P.map ρ).scalarEval H - H ∈ Ideal.span
        {g | ∃ i : Fin s, (α i).degree < d ∧ g = MvPowerSeries.map ρ (f i)}) ∧
    (∀ i : Fin s, d ≤ (α i).degree →
      (P.map ρ).scalarEval (MvPowerSeries.map ρ (f i)) = MvPowerSeries.map ρ (f i)) ∧
    (∀ (H : MvPowerSeries (Fin t) (MvPowerSeries (Fin r) Γ(C, ⊤)))
        (E : BlockEarlierTest α d Q) (γ : Fin (blockEarlierTests α d Q E).kept →₀ ℕ)
        (δ : Fin r →₀ ℕ),
      MvPowerSeries.coeff δ (MvPowerSeries.coeff γ
        ((blockEarlierTests α d Q E).eval ((P.map ρ).scalarEval H))) = 0) ∧
    (∀ b : C,
      (∀ i : Fin s, d ≤ (α i).degree →
        (P.map (blockPointCoefficientMap (points b))).scalarEval
          (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i)) =
            MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i)) ∧
      (P.map (blockPointCoefficientMap (points b))).IsKernelProjection
        (blockEarlierTests α d Q) ∧
      ∀ H : MvPowerSeries (Fin t) (MvPowerSeries (Fin m ⊕ Fin r) (C.residueField b)),
        (P.map (blockPointCoefficientMap (points b))).scalarEval H - H ∈ Ideal.span
          {g | ∃ i : Fin s, (α i).degree < d ∧
            g = MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i)}) ∧
    blockPreservesFirst α d Q P (blockPointCoefficientMap (points center)) ∧
    (IsEmpty (BlockEarlierTest α d Q) →
      (P.scalarEval = id ∧ (P.map ρ).scalarEval = id))

/-- The geometric data before any stored projection is transported.
The square says that C is precisely
V(h) after shrinking B, and `closed` refers to that open ambient scheme. The
pointwise implicit calculus gives the graph ideal (Y); `joint_derivatives` includes
all old and new derivative equations in (Y,T), with the full invertible Jacobian.
Source: BM (9.8)(a)--(c), Remarks 9.9--9.11
(blueprint: def-trf-block-straightening-data). -/
structure BlockStraighteningGeometry {k : Type u} [Field k] [CharZero k]
    {B : Scheme.{u}} {m r t s : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)} {a : B}
    {D : ImplicitCoordinateDerivations B c}
    {α : Fin s → Fin ((m + r) + t) →₀ ℕ} {d Q : ℕ}
    {f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤)}
    {pick : Fin (r + t) → Fin s} {β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ}
    (A : BlockStraighteningInput B c a D α d Q f pick β) where
  open_in_zero : (implicitZeroScheme D (blockEquations D f pick β)).Opens
  ambient : B.Opens
  toAmbient : open_in_zero.toScheme ⟶ ambient.toScheme
  square : IsPullback open_in_zero.ι toAmbient
    (implicitZeroInclusion D (blockEquations D f pick β)) ambient.ι
  closed : IsClosedImmersion toAmbient
  affine : IsAffine open_in_zero.toScheme
  center : open_in_zero.toScheme
  center_eq : (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) center = a
  etale : Etale (implicitCoordinateMorphism
    ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)).appTop.hom.comp
      (c.comp (MvPolynomial.rename Sum.inl).toRingHom)))
  smooth : Smooth ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) ≫
    implicitStructureMorphism c)
  points : ∀ b : open_in_zero.toScheme, ImplicitTaylorPoint.{u, u} c
    (blockEquations D f pick β) D
    (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) b
  rho : Γ(B, ⊤) →+* MvPowerSeries (Fin r) Γ(open_in_zero.toScheme, ⊤)
  rho_coeff : ∀ (g : Γ(B, ⊤)) (δ : Fin r →₀ ℕ), MvPowerSeries.coeff δ (rho g) =
    blockRegularCoefficient D
      (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) δ g
  coefficient_specialization : ∀ (b : open_in_zero.toScheme) (g : Γ(B, ⊤))
      (δ : Fin r →₀ ℕ),
    implicitTransverseCoeff δ (blockPointCoefficientMap (points b) g) =
      (points b).taylorN (open_in_zero.toScheme.presheaf.germ ⊤ b (by trivial)
        (MvPowerSeries.coeff δ (rho g)))
  old_tests : ∀ (q : ℕ), q < d → ∀ i : Fin s, q < (α i).degree →
    ∀ E : MvPowerSeries.FormalCoefficientTest t, blockTestAt α q Q E →
      E.eval (MvPowerSeries.map rho (f i)) = 0 ∧
        ∀ b : open_in_zero.toScheme,
          E.eval (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i)) = 0
  coefficients : ∀ (b : open_in_zero.toScheme) (i : Fin s) (γ : Fin t →₀ ℕ)
      (δ : Fin r →₀ ℕ),
    implicitTransverseCoeff δ
      (MvPowerSeries.coeff γ (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i))) =
      (points b).taylorN (open_in_zero.toScheme.presheaf.germ ⊤ b (by trivial)
        (MvPowerSeries.coeff δ (rho (MvPowerSeries.coeff γ (f i)))))
  first : ∀ i : Fin s, MonomialDiagram.IsFirstExponent
    (blockFlattenChart (MvPowerSeries.map (blockPointCoefficientMap (points center)) (f i))) (α i)
  ideals : ∀ b : open_in_zero.toScheme,
    Ideal.map (MvPowerSeries.map (points b).straight.toRingHom)
      (Ideal.map (MvPowerSeries.map (MvPowerSeries.map
        ((open_in_zero.ι ≫ implicitZeroInclusion D
          (blockEquations D f pick β)).residueFieldMap b).hom))
        (A.ideal ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) b))) =
    Ideal.span (Set.range fun i : Fin s ↦
      MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i))
  membership : ∀ (b : open_in_zero.toScheme) (i : Fin s),
    MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i) ∈
      Ideal.map (MvPowerSeries.map (points b).straight.toRingHom)
        (Ideal.map (MvPowerSeries.map (MvPowerSeries.map
          ((open_in_zero.ι ≫ implicitZeroInclusion D
            (blockEquations D f pick β)).residueFieldMap b).hom))
          (A.ideal ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) b)))
  residue_center : Function.Surjective
    ((open_in_zero.ι ≫ implicitZeroInclusion D
      (blockEquations D f pick β)).residueFieldMap center).hom
  joint_derivatives : ∀ b : open_in_zero.toScheme,
    (∀ j : Fin (r + t), iteratedPartial (β j)
      (blockFlattenChart (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f (pick j)))) ∈
        Ideal.span (Set.range fun l : Fin (r + t) ↦
          (MvPowerSeries.X (blockTransverseVariable m r t l) :
            MvPowerSeries (Fin ((m + r) + t)) (open_in_zero.toScheme.residueField b)))) ∧
    IsUnit (Matrix.det (fun j l : Fin (r + t) ↦ MvPowerSeries.constantCoeff
      (MvPowerSeries.pderiv (open_in_zero.toScheme.residueField b)
        (blockTransverseVariable m r t l) (iteratedPartial (β j)
          (blockFlattenChart
            (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f (pick j))))))))

/-- Output on one common open neighborhood. The square says that C is precisely
V(h) after shrinking B, and `closed` refers to that open ambient scheme. The
pointwise implicit calculus gives the graph ideal (Y); `joint_derivatives` includes
all old and new derivative equations in (Y,T), with the full invertible Jacobian.
Source: BM (9.8)(a)--(c), Remarks 9.9--9.11
(blueprint: def-trf-block-straightening-data). -/
structure BlockStraighteningOutput {k : Type u} [Field k] [CharZero k]
    {B : Scheme.{u}} {m r t s : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)} {a : B}
    {D : ImplicitCoordinateDerivations B c}
    {α : Fin s → Fin ((m + r) + t) →₀ ℕ} {d Q : ℕ}
    {f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤)}
    {pick : Fin (r + t) → Fin s} {β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ}
    (A : BlockStraighteningInput B c a D α d Q f pick β) where
  open_in_zero : (implicitZeroScheme D (blockEquations D f pick β)).Opens
  ambient : B.Opens
  toAmbient : open_in_zero.toScheme ⟶ ambient.toScheme
  square : IsPullback open_in_zero.ι toAmbient
    (implicitZeroInclusion D (blockEquations D f pick β)) ambient.ι
  closed : IsClosedImmersion toAmbient
  affine : IsAffine open_in_zero.toScheme
  center : open_in_zero.toScheme
  center_eq : (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) center = a
  etale : Etale (implicitCoordinateMorphism
    ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)).appTop.hom.comp
      (c.comp (MvPolynomial.rename Sum.inl).toRingHom)))
  smooth : Smooth ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) ≫
    implicitStructureMorphism c)
  points : ∀ b : open_in_zero.toScheme, ImplicitTaylorPoint.{u, u} c
    (blockEquations D f pick β) D
    (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) b
  rho : Γ(B, ⊤) →+* MvPowerSeries (Fin r) Γ(open_in_zero.toScheme, ⊤)
  rho_coeff : ∀ (g : Γ(B, ⊤)) (δ : Fin r →₀ ℕ), MvPowerSeries.coeff δ (rho g) =
    blockRegularCoefficient D
      (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) δ g
  coefficient_specialization : ∀ (b : open_in_zero.toScheme) (g : Γ(B, ⊤))
      (δ : Fin r →₀ ℕ),
    implicitTransverseCoeff δ (blockPointCoefficientMap (points b) g) =
      (points b).taylorN (open_in_zero.toScheme.presheaf.germ ⊤ b (by trivial)
        (MvPowerSeries.coeff δ (rho g)))
  old_tests : ∀ (q : ℕ), q < d → ∀ i : Fin s, q < (α i).degree →
    ∀ E : MvPowerSeries.FormalCoefficientTest t, blockTestAt α q Q E →
      E.eval (MvPowerSeries.map rho (f i)) = 0 ∧
        ∀ b : open_in_zero.toScheme,
          E.eval (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i)) = 0
  coefficients : ∀ (b : open_in_zero.toScheme) (i : Fin s) (γ : Fin t →₀ ℕ)
      (δ : Fin r →₀ ℕ),
    implicitTransverseCoeff δ
      (MvPowerSeries.coeff γ (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i))) =
      (points b).taylorN (open_in_zero.toScheme.presheaf.germ ⊤ b (by trivial)
        (MvPowerSeries.coeff δ (rho (MvPowerSeries.coeff γ (f i)))))
  first : ∀ i : Fin s, MonomialDiagram.IsFirstExponent
    (blockFlattenChart (MvPowerSeries.map (blockPointCoefficientMap (points center)) (f i))) (α i)
  ideals : ∀ b : open_in_zero.toScheme,
    Ideal.map (MvPowerSeries.map (points b).straight.toRingHom)
      (Ideal.map (MvPowerSeries.map (MvPowerSeries.map
        ((open_in_zero.ι ≫ implicitZeroInclusion D
          (blockEquations D f pick β)).residueFieldMap b).hom))
        (A.ideal ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) b))) =
    Ideal.span (Set.range fun i : Fin s ↦
      MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i))
  membership : ∀ (b : open_in_zero.toScheme) (i : Fin s),
    MvPowerSeries.map (blockPointCoefficientMap (points b)) (f i) ∈
      Ideal.map (MvPowerSeries.map (points b).straight.toRingHom)
        (Ideal.map (MvPowerSeries.map (MvPowerSeries.map
          ((open_in_zero.ι ≫ implicitZeroInclusion D
            (blockEquations D f pick β)).residueFieldMap b).hom))
          (A.ideal ((open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β)) b)))
  joint_derivatives : ∀ b : open_in_zero.toScheme,
    (∀ j : Fin (r + t), iteratedPartial (β j)
      (blockFlattenChart (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f (pick j)))) ∈
        Ideal.span (Set.range fun l : Fin (r + t) ↦
          (MvPowerSeries.X (blockTransverseVariable m r t l) :
            MvPowerSeries (Fin ((m + r) + t)) (open_in_zero.toScheme.residueField b)))) ∧
    IsUnit (Matrix.det (fun j l : Fin (r + t) ↦ MvPowerSeries.constantCoeff
      (MvPowerSeries.pderiv (open_in_zero.toScheme.residueField b)
        (blockTransverseVariable m r t l) (iteratedPartial (β j)
          (blockFlattenChart
            (MvPowerSeries.map (blockPointCoefficientMap (points b)) (f (pick j))))))))
  projection : ∀ P : MvPowerSeries.FiniteCoefficientExpression Γ(B, ⊤) t 1 t 1,
    blockProjectionHypotheses α d Q f (A.taylor a) P →
      blockProjectionConclusions
        (open_in_zero.ι ≫ implicitZeroInclusion D (blockEquations D f pick β))
        center points α d Q f rho P


end AlgebraicGeometry.HilbertCoefficient
