module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Jointly continuous homogeneous cochain coordinates

Source: Stacks Project, Tag 0DVG, etale-cohomology.tex, continuous group cohomology;
the homogeneous coordinate calculation is the agent-written expansion of that complex.
(blueprint: lem-sfb-topological-homogeneous-cochain-coordinates).

The evaluation maps below identify the abstract vector spaces with exactly the specified
jointly continuous functions, with their pointwise linear operations. No function-space
topology, iterated-continuous-map model, or exponential law is used. The complexes are
integer indexed and zero in negative degrees. Their derived isomorphism is represented
by the specified actual cochain isomorphism.
-/

@[expose] public section

universe u v w t r v' w'

open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

/-- The homogeneous and inhomogeneous complexes together with the prescribed coordinate
isomorphism, described by injective linear evaluation maps whose images are exactly the
functions in the statement. This is a specification of these complexes up to their
unique evaluation-preserving isomorphisms, not a choice of unspecified cochain spaces.
The image conditions give precisely continuous equivariant homogeneous functions and
continuous inhomogeneous functions, and thus their pointwise vector space structures.

Source: Stacks Project, Tag 0DVG, displayed inhomogeneous differential, and the
agent-written homogeneous conversion, steps 1--12 of the DAG proof.
(blueprint: lem-sfb-topological-homogeneous-cochain-coordinates). -/
structure JointContinuousCochainCoordinates
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V)
    (B C : CochainComplex (ModuleCat.{t} E) ℤ)
    [HasDerivedCategory.{r} (ModuleCat.{t} E)] where
  /-- Evaluation on homogeneous tuples. -/
  bEval : ∀ n : ℕ, B.X (n : ℤ) →ₗ[E] ((Fin (n + 1) → J) → V)
  /-- Evaluation loses no homogeneous cochain. -/
  bInjective : ∀ n : ℕ, Function.Injective (bEval n)
  /-- Its image is exactly the continuous equivariant functions. -/
  bRange : ∀ (n : ℕ) (F : (Fin (n + 1) → J) → V),
    (∃ b, bEval n b = F) ↔
      Continuous F ∧ ∀ (a : J) (x : Fin (n + 1) → J),
        F (fun i ↦ a * x i) = ρ a (F x)
  /-- Evaluation on inhomogeneous tuples, including the empty tuple in degree zero. -/
  cEval : ∀ n : ℕ, C.X (n : ℤ) →ₗ[E] ((Fin n → J) → V)
  /-- Evaluation loses no inhomogeneous cochain. -/
  cInjective : ∀ n : ℕ, Function.Injective (cEval n)
  /-- Its image is exactly the jointly continuous functions. -/
  cRange : ∀ (n : ℕ) (f : (Fin n → J) → V),
    (∃ c, cEval n c = f) ↔ Continuous f
  /-- Extension of the homogeneous complex by zero. -/
  bNegative : ∀ i : ℤ, i < 0 → IsZero (B.X i)
  /-- Extension of the inhomogeneous complex by zero. -/
  cNegative : ∀ i : ℤ, i < 0 → IsZero (C.X i)
  /-- The homogeneous differential is the alternating sum of all omissions. -/
  delta : ∀ (n : ℕ) (b : B.X (n : ℤ)) (x : Fin (n + 2) → J),
    bEval (n + 1) ((B.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom b) x =
      ∑ i : Fin (n + 2), (-1 : E) ^ i.val • bEval n b (x ∘ i.succAbove)
  /-- Internal contractions multiply adjacent arguments; the final contraction drops
  the last argument. For n = 0 this is exactly g acting on v minus v. -/
  differential : ∀ (n : ℕ) (c : C.X (n : ℤ)) (g : Fin (n + 1) → J),
    cEval (n + 1) ((C.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom c) g =
      ρ (g 0) (cEval n c (fun i ↦ g i.succ)) +
        ∑ i : Fin (n + 1),
          (-1 : E) ^ (i.val + 1) • cEval n c (Fin.contractNth i (· * ·) g)
  /-- The actual linear cochain isomorphism. -/
  iso : B ≅ C
  /-- Evaluation at (1,g₁,g₁g₂,...). In degree zero it evaluates F at 1. -/
  phi : ∀ (n : ℕ) (b : B.X (n : ℤ)) (g : Fin n → J),
    cEval n ((iso.hom.f (n : ℤ)).hom b) g = bEval n b (Fin.partialProd g)
  /-- The inverse uses successive ratios, and acts by x₀. In degree zero this
  sends v to the function x₀ acting on v. -/
  psi : ∀ (n : ℕ) (c : C.X (n : ℤ)) (x : Fin (n + 1) → J),
    bEval n ((iso.inv.f (n : ℤ)).hom c) x =
      ρ (x 0) (cEval n c (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))
  /-- The isomorphism in the abstract derived category of E-vector spaces. -/
  derived : (DerivedCategory.Q.obj B) ≅ (DerivedCategory.Q.obj C)
  /-- Its forward arrow is represented by the actual coordinate cochain map. -/
  derived_hom : derived.hom = DerivedCategory.Q.map iso.hom
  /-- Its inverse is represented by the inverse coordinate cochain map. -/
  derived_inv : derived.inv = DerivedCategory.Q.map iso.inv

/-- Jointly continuous homogeneous and inhomogeneous cochains admit the specified
actual cochain isomorphism and the isomorphism it represents in D(E-Vect).
The extra ambient universe t allows both source and target of any coefficient or group
map to be represented in one category, without equating their carrier universes.

Source: Stacks Project, Tag 0DVG, displayed differential; agent-written homogeneous
coordinate calculation, all twelve steps of the node proof.
(blueprint: lem-sfb-topological-homogeneous-cochain-coordinates).

Proof: (1) Take the vector subspaces of all functions consisting of continuous
homogeneous equivariant maps and continuous inhomogeneous maps. Pointwise operations
preserve these conditions. Lift the spaces to the chosen ambient universe if needed.
(2) Alternating omission preserves continuity and equivariance and squares to zero:
the deletions i < j occur in opposite orders with signs (-1)^(i+j-1) and (-1)^(i+j).
(3) Cumulative products are continuous, so precomposition defines Phi.
(4) Successive ratios and the jointly continuous action define continuous Psi;
(ax) inverse times (ay) = x inverse times y proves equivariance.
(5) Ratios of consecutive cumulative products recover the arguments, giving Phi Psi = id.
(6) Products of successive ratios telescope to x0 inverse times xi; equivariance gives
Psi Phi = id. Both maps are E-linear. These computations include the empty tuple.
(7) The first omitted cumulative product is the action term in the differential.
(8) Internal omissions multiply consecutive arguments and the last omission drops the
last argument, with exactly the displayed signs; hence Phi delta = d Phi, including n=0.
(9) Consequently d = Phi delta Psi squares to zero and Psi d = delta Psi. Extend by zero
in negative degrees, obtaining an actual cochain isomorphism.
(10) Equivariant linear coefficient maps commute with evaluation and the action.
(11) Group homomorphisms preserve 1, products and ratios, proving restriction naturality.
The next theorem records (10)--(11) on complexes and on both localized arrows.
(12) Apply the localization functor Q to the cochain isomorphism and its inverse;
functoriality preserves the two inverse identities. -/
theorem exists_jointContinuousCochainCoordinates
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V) (hρ : Continuous (fun p : J × V ↦ ρ p.1 p.2))
    [HasDerivedCategory.{r} (ModuleCat.{max v w t} E)] :
    ∃ B C : CochainComplex (ModuleCat.{max v w t} E) ℤ,
      Nonempty (JointContinuousCochainCoordinates E J V ρ B C) := by
  sorry

/-- Both coordinate maps commute with continuous equivariant coefficient maps and
restriction along continuous group homomorphisms, on complexes and in D(E-Vect).
Taking h = id gives coefficient naturality; taking u = id with the restricted action
gives restriction naturality. The evaluation formulas uniquely specify the induced maps.

Source: Stacks Project, Tag 0DVG; agent-written homogeneous coordinate conversion,
steps 10--12 of the node proof.
(blueprint: lem-sfb-topological-homogeneous-cochain-coordinates).

Proof: Precompose cochains coordinatewise with h and postcompose with u. Continuity,
linearity and equivariance preserve the two specified images. The omission differential
commutes with these operations, as does the inhomogeneous differential since h preserves
products and u intertwines the actions. Evaluation injectivity gives the resulting
cochain maps, with the unique zero maps in negative degrees. The Phi formula commutes
with h because h preserves 1 and cumulative products. The Psi formula commutes because
h preserves successive ratios and u intertwines the actions. Thus both naturality
squares commute in every degree. Apply Q to those equalities and use functoriality and
the prescribed representatives of the derived isomorphisms to obtain both derived squares. -/
theorem jointContinuousCochainCoordinates_naturality
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V)
    (H : Type v') [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (W : Type w') [AddCommGroup W] [Module E W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul E W]
    (σ : H →* W ≃ₗ[E] W)
    [HasDerivedCategory.{r} (ModuleCat.{t} E)]
    (B C B' C' : CochainComplex (ModuleCat.{t} E) ℤ)
    (D : JointContinuousCochainCoordinates E J V ρ B C)
    (D' : JointContinuousCochainCoordinates E H W σ B' C')
    (h : H →* J) (hh : Continuous h) (u : V →ₗ[E] W) (hu : Continuous u)
    (heq : ∀ (a : H) (v : V), u (ρ (h a) v) = σ a (u v)) :
    ∃ (bMap : B ⟶ B') (cMap : C ⟶ C'),
      (∀ (n : ℕ) (b : B.X (n : ℤ)) (x : Fin (n + 1) → H),
        D'.bEval n ((bMap.f (n : ℤ)).hom b) x = u (D.bEval n b (h ∘ x))) ∧
      (∀ (n : ℕ) (c : C.X (n : ℤ)) (g : Fin n → H),
        D'.cEval n ((cMap.f (n : ℤ)).hom c) g = u (D.cEval n c (h ∘ g))) ∧
      D.iso.hom ≫ cMap = bMap ≫ D'.iso.hom ∧
      D.iso.inv ≫ bMap = cMap ≫ D'.iso.inv ∧
      D.derived.hom ≫ DerivedCategory.Q.map cMap =
        DerivedCategory.Q.map bMap ≫ D'.derived.hom ∧
      D.derived.inv ≫ DerivedCategory.Q.map bMap =
        DerivedCategory.Q.map cMap ≫ D'.derived.inv := by
  sorry

end ContinuousCohomology
