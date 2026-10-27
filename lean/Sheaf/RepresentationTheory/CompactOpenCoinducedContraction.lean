module

public import Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Module.ULift

/-!
# Compact-open coinduced contraction

Source: the agent-written scalar analytic input below paragraph (3) of
`literature/blueprint/latest/blueprint/sec-six-functors-basics/`'s direct-image proof;
Stacks Tag 0DVG supplies the continuous cochain differential only.
(blueprint: lem-sfb-compact-open-coinduced-contraction).

Evaluation specifies every complex and every operator. Only the proof of existence is
postponed. The coefficient complex is the ordinary single complex, with a universe lift.
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

/-- The coefficient vector space in degree zero, lifted only to the ambient universe.
Source: the augmented contraction in the scalar analytic input below direct-image
paragraph (3) (blueprint: lem-sfb-compact-open-coinduced-contraction). -/
noncomputable def compactOpenCoefficientSingle
    (k : Type u) [Field k] (V : Type w) [AddCommGroup V] [Module k V] :
    CochainComplex (ModuleCat.{max w t} k) ℤ :=
  (HomologicalComplex.single (ModuleCat.{max w t} k) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of k (ULift.{t} V))

/-- Evaluation of the degree-zero coefficient complex in the original vector space.
Source: evaluation at zero in the augmented scalar contraction below direct-image
paragraph (3) (blueprint: lem-sfb-compact-open-coinduced-contraction). -/
noncomputable def compactOpenSingleEval
    (k : Type u) [Field k] (V : Type w) [AddCommGroup V] [Module k V]
    (x : (compactOpenCoefficientSingle.{u, w, t} k V).X 0) : V :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of k (ULift.{t} V))).hom.hom x).down

/-- Specification of the explicit compact-open contraction. The homogeneous and
inhomogeneous terms reuse the existing coordinate interface on `Multiplicative J`;
its multiplication is precisely addition in J. The injective evaluation map on D has
image exactly the continuous functions, so no unspecified cochain spaces are chosen.
All arrows and homotopies are arrows of abstract vector spaces.

Source: agent-written scalar analytic input below direct-image paragraph (3), with
Stacks Tag 0DVG for the cochain differential.
(blueprint: lem-sfb-compact-open-coinduced-contraction). -/
structure CompactOpenCoinducedContraction
    (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
    (J : Type v) [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
    [CompactSpace J] [T2Space J]
    (V : Type w) [AddCommGroup V] [Module k V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul k V] [T2Space V]
    (B C D : CochainComplex (ModuleCat.{max v w t} k) ℤ)
    [HasDerivedCategory.{r} (ModuleCat.{max v w t} k)] where
  /-- Right translation on the actual compact-open function space. -/
  action : Multiplicative J →* C(J, V) ≃ₗ[k] C(J, V)
  action_apply : ∀ (a : Multiplicative J) (f : C(J, V)) (y : J),
    action a f y = f (y + a.toAdd)
  action_continuous : Continuous (fun p : Multiplicative J × C(J, V) ↦ action p.1 p.2)
  coordinates : JointContinuousCochainCoordinates k (Multiplicative J) C(J, V) action B C
  /-- The unaugmented deletion complex is exactly continuous functions on powers of J. -/
  eval : ∀ n : ℕ, D.X (n : ℤ) →ₗ[k] ((Fin (n + 1) → J) → V)
  injective : ∀ n : ℕ, Function.Injective (eval n)
  range : ∀ (n : ℕ) (f : (Fin (n + 1) → J) → V),
    (∃ d, eval n d = f) ↔ Continuous f
  negative : ∀ j : ℤ, j < 0 → IsZero (D.X j)
  delta : ∀ (n : ℕ) (d : D.X (n : ℤ)) (x : Fin (n + 2) → J),
    eval (n + 1) ((D.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom d) x =
      ∑ a : Fin (n + 2), (-1 : k) ^ a.val • eval n d (x ∘ a.succAbove)
  theta : B ≅ D
  theta_apply : ∀ (n : ℕ) (b : B.X (n : ℤ)) (x : Fin (n + 1) → J),
    eval n ((theta.hom.f (n : ℤ)).hom b) x =
      coordinates.bEval n b (fun a ↦ Multiplicative.ofAdd (x a)) 0
  theta_inv_apply : ∀ (n : ℕ) (d : D.X (n : ℤ))
      (x : Fin (n + 1) → Multiplicative J) (y : J),
    coordinates.bEval n ((theta.inv.f (n : ℤ)).hom d) x y =
      eval n d (fun a ↦ (x a).toAdd + y)
  /-- Insertion of zero, with actual continuous-cochain values. -/
  h : ∀ n : ℕ, D.X ((n + 1 : ℕ) : ℤ) ⟶ D.X (n : ℤ)
  h_apply : ∀ (n : ℕ) (d : D.X ((n + 1 : ℕ) : ℤ)) (x : Fin (n + 1) → J),
    eval n ((h n).hom d) x = eval (n + 1) d (Fin.cons 0 x)
  i : compactOpenCoefficientSingle.{u, w, max v t} k V ⟶ D
  p : D ⟶ compactOpenCoefficientSingle.{u, w, max v t} k V
  i_apply : ∀ (a : (compactOpenCoefficientSingle.{u, w, max v t} k V).X 0)
      (x : Fin 1 → J),
    eval 0 ((i.f 0).hom a) x = compactOpenSingleEval.{u, w, max v t} k V a
  p_apply : ∀ d : D.X 0,
    compactOpenSingleEval.{u, w, max v t} k V ((p.f 0).hom d) = eval 0 d (fun _ ↦ 0)
  pi : i ≫ p = 𝟙 _
  /-- The homotopy identity is oriented as id = dh + hd + ip. -/
  contraction : Homotopy (𝟙 D) (p ≫ i)
  contraction_h : ∀ n : ℕ, contraction.hom ((n + 1 : ℕ) : ℤ) (n : ℤ) = h n
  contraction_h0 : contraction.hom 0 (-1) = 0
  /-- Transport by T = Theta Phi inverse specifies both equivalence arrows. -/
  equiv : HomotopyEquiv C (compactOpenCoefficientSingle.{u, w, max v t} k V)
  equiv_hom : equiv.hom = coordinates.iso.inv ≫ theta.hom ≫ p
  equiv_inv : equiv.inv = i ≫ theta.inv ≫ coordinates.iso.hom
  equiv_h : ∀ n : ℕ,
    equiv.homotopyHomInvId.hom ((n + 1 : ℕ) : ℤ) (n : ℤ) =
      -((coordinates.iso.inv.f ((n + 1 : ℕ) : ℤ)) ≫
        theta.hom.f ((n + 1 : ℕ) : ℤ) ≫ h n ≫
        theta.inv.f (n : ℤ) ≫ coordinates.iso.hom.f (n : ℤ))
  /-- The isomorphism represented by the specified homotopy equivalence. -/
  derived : DerivedCategory.Q.obj C ≅
    DerivedCategory.Q.obj (compactOpenCoefficientSingle.{u, w, max v t} k V)
  derived_hom : derived.hom = DerivedCategory.Q.map equiv.hom
  derived_inv : derived.inv = DerivedCategory.Q.map equiv.inv
  /-- Every positive closed cochain has a continuous primitive. -/
  primitive : ∀ (n : ℕ) (c : C.X ((n + 1 : ℕ) : ℤ)),
    (C.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom c = 0 →
      ∃ b : C.X (n : ℤ), (C.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom b = c

/-- The explicit compact-open coinduced contraction, including its derived isomorphism
and continuous primitives, without any completeness or discreteness hypothesis on V.

Source: agent-written scalar analytic input below paragraph (3) of the current blueprint
open-direct-image proof; Stacks Tag 0DVG gives only the differential.
(blueprint: lem-sfb-compact-open-coinduced-contraction).

Proof: (1) Compact Hausdorff J is locally compact by
lem-coef-hausdorff-compact-neighborhood-basis. Compact-open currying and evaluation
(lem-coef-compact-open-currying) give continuous vector operations and jointly continuous
right translation on R. Point evaluations show R is Hausdorff.
(2) Evaluate homogeneous cochains at zero; transpose phi(x+y) for the inverse. Addition
is continuous and commutativity proves equivariance; both operations are linear.
(3) Equivariance proves the inverse identities. Evaluation commutes with finite alternating
sums; paired omissions cancel, proving delta squared zero. Extend by zero below zero.
(4) Insert zero to obtain h with continuous values. Constant inclusion i and evaluation p
are cochain maps, and pi is the identity.
(5) Expand delta h and h delta. In positive degrees all terms with an inserted zero
cancel in pairs, leaving phi. In degree zero the result is phi(x)-phi(0). This proves
id = delta h + h delta + ip, including characteristic two and the negative degrees.
(6) Use lem-sfb-topological-homogeneous-cochain-coordinates to transport by
T = Theta Phi inverse. This gives the specified equivalence and explicit continuous
primitives T inverse h T of positive closed cochains. Mathlib's homotopy from IP to id
has components minus these primitives.
(7) The deletion complex has only H0 = V: its zero cocycles are constants and positive
cocycles are boundaries by (5). Thus pT is a quasi-isomorphism and Q inverts it, by
def-weil-abstract-derived-category. Its inverse is represented by T inverse i. All
operations are finite sums, composition, evaluation, and insertion. -/
theorem exists_compactOpenCoinducedContraction
    (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
    (J : Type v) [AddCommGroup J] [TopologicalSpace J] [IsTopologicalAddGroup J]
    [CompactSpace J] [T2Space J]
    (V : Type w) [AddCommGroup V] [Module k V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul k V] [T2Space V]
    [HasDerivedCategory.{r} (ModuleCat.{max v w t} k)] :
    ∃ B C D : CochainComplex (ModuleCat.{max v w t} k) ℤ,
      Nonempty (CompactOpenCoinducedContraction.{u, v, w, t, r} k J V B C D) := by
  sorry

end ContinuousCohomology
