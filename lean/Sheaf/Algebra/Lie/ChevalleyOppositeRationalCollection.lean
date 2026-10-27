/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Sheaf.Algebra.Lie.KostantIntegralPBW
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Local rational collection of opposite Chevalley root products

Source: Milne, Algebraic Groups (2017), Section 23h, (152)--(153), Theorem 23.72
and Notes, printed pp.510--511; the agent-expanded local collection argument
(blueprint: lem-sfb-chevalley-opposite-rational-collection).

The morphisms are written contravariantly in affine coordinates: the coordinates of
A and B are elements of the localization, and h is an algebra map from F[P].
The matrix identity is over that coordinate algebra, hence is an identity of
morphisms, including evaluation in nonreduced algebras. Tensor symmetry identifies
our F-algebra tensor lattice with the lattice tensor F in the source.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w t z

open scoped TensorProduct

namespace LieAlgebra.ChevalleyCollection

/-- Restrict an integral divided power to the given admissible lattice.
Source: Milne, Section 23h, before (152)--(153), p.510
(blueprint: lem-sfb-chevalley-opposite-rational-collection). -/
def latticeDividedPower {W : Type w} [AddCommGroup W] [Module ℚ W]
    (Λ : Submodule ℤ W) (E : Module.End ℚ W) (m : ℕ)
    (h : ∀ w : W, w ∈ Λ → ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ) :
    Module.End ℤ Λ :=
  (((Nat.factorial m : ℚ)⁻¹ • E ^ m).restrictScalars ℤ).restrict h

/-- The finite root exponential on a base-changed lattice, truncated at a nilpotence bound.
Source: Milne, Section 23h, (153), p.510
(blueprint: lem-sfb-chevalley-opposite-rational-collection). -/
def rootExponential {Λ : Type w} [AddCommGroup Λ]
    (D : ℕ → Module.End ℤ Λ) (n : ℕ) {C : Type t} [CommRing C] (a : C) :
    Module.End C (C ⊗[ℤ] Λ) :=
  ∑ m ∈ Finset.range n, a ^ m • (D m).baseChange C

/-- The lattice intersection with an actual rational weight space.
Source: Milne, Section 23h, (152), p.510
(blueprint: lem-sfb-chevalley-opposite-rational-collection). -/
def latticeWeightSpace {V : Type u} [AddCommGroup V] [Module ℚ V]
    {g : Type v} [LieRing g] [LieAlgebra ℚ g]
    {W : Type w} [AddCommGroup W] [Module ℚ W]
    [LieRingModule g W] [LieModule ℚ g W]
    (H : LieSubalgebra ℚ g) (θ : H ≃ₗ[ℚ] Module.Dual ℚ V)
    (Λ : Submodule ℤ W) (μ : V) : Submodule ℤ Λ :=
  ((LieModule.weightSpace W (fun h : H ↦ θ h μ)).toSubmodule.restrictScalars ℤ).comap
    Λ.subtype

open Classical in
/-- The canonical projection onto a summand of an internal lattice decomposition.
Source: Milne, (152), p.510
(blueprint: lem-sfb-chevalley-opposite-rational-collection). -/
def weightProjection {ι : Type u} [DecidableEq ι] {Λ : Type w} [AddCommGroup Λ]
    (E : ι → Submodule ℤ Λ) (hE : DirectSum.IsInternal E) (i : ι) :
    Module.End ℤ Λ :=
  (E i).subtype ∘ₗ DirectSum.component ℤ ι (fun j ↦ E j) i ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap E) hE).symm.toLinearMap

open Classical in
/-- The weight-character action of a point of Spec F[P], expressed by its coordinate map.
The monomials e^μ are units, with inverses e^(-μ), so this is the usual torus action.
Source: Milne, Section 23h, following (152), p.510
(blueprint: lem-sfb-chevalley-opposite-rational-collection). -/
def torusAction {P : Type u} [AddCommGroup P] {ι : Type u} [Fintype ι] [DecidableEq ι]
    {Λ : Type w} [AddCommGroup Λ] (E : ι → Submodule ℤ Λ)
    (hE : DirectSum.IsInternal E) (weight : ι → P)
    {F : Type t} [Field F] {C : Type z} [CommRing C] [Algebra F C]
    (h : AddMonoidAlgebra F P →ₐ[F] C) : Module.End C (C ⊗[ℤ] Λ) :=
  ∑ i, h (AddMonoidAlgebra.single (weight i) 1) • (weightProjection E hE i).baseChange C

/-- Evaluation at the origin on the principal open d ≠ 0, when d(0) = 1.
Source: Milne, Section 23h, local collection argument after (153), pp.510--511
(blueprint: lem-sfb-chevalley-opposite-rational-collection). -/
def origin {ι : Type u} {F : Type t} [Field F] (d : MvPolynomial ι F)
    (hd : MvPolynomial.aeval (fun _ : ι ↦ (0 : F)) d = 1) :
    Localization.Away d →ₐ[F] F :=
  IsLocalization.Away.liftAlgHom d (hd.symm ▸ isUnit_one)

open Classical in
/-- Opposite ordered root products admit rational collection in the full weight torus
on a principal neighborhood of the origin, normalized to identity there.

Source: Milne, Algebraic Groups (2017), Section 23h, (153), Theorem 23.72 and Notes,
pp.510--511; agent-expanded supporting local matrix argument
(blueprint: lem-sfb-chevalley-opposite-rational-collection).

Proof plan:
1. By lem-sfb-root-base-rational-integral-spans the simple coroots generate the coroot
   lattice. Apply lem-sfb-kostant-integral-pbw in the prescribed two root orders. Its
   integral PBW monomials Q_I have coproduct sum_{J+K=I} Q_J tensor Q_K, by the
   primitive coproduct on Lie generators and the divided-power and binomial identities.
2. Expand the product of positive and negative root exponentials coefficientwise in
   the formal parameter ring over Z. The group-like identity gives c_(J+K)=c_J c_K
   and augmentation gives c_0=1. Thus the coefficients factor into powers of the
   degree-one negative, toral, and positive coefficients, all zero at the origin.
3. Reinsert these coefficients into the PBW expansion. The representation preserves
   the lattice by lem-sfb-chevalley-admissible-representation. Toral binomials act on
   a weight by integer binomial coefficients, including negative integer weights via
   binom(-k,m)=(-1)^m binom(k+m-1,m). The toral factor is the character
   lambda ↦ product_i (1+z_i)^(c_delta_i(lambda)). Base change the integral equality
   to F[[a,b]]; nilpotence makes every represented exponential finite.
4. Choose a positive rational functional separating the finitely many weights and
   order their blocks decreasingly. By lem-sfb-chevalley-unipotent-polynomial-coordinates
   the ordered root products identify affine space with closed subgroups of the lower
   and upper block unitriangular groups. The full weight torus is closed in the block
   diagonal group: the weights and their negatives generate F[P].
5. Apply lem-sfb-block-gauss-scheme-chart to g=p_+(b)p_-(a), taking d to be the product
   of its leading block minors. Then d(0)=1 and block Gauss factors exist over
   S=F[a,b,1/d]. The map S→F[[a,b]] is injective: d is a formal unit and a fraction
   with zero image has zero polynomial numerator.
6. Gauss uniqueness over the formal ring identifies these factors with the formal
   root and torus factors of step 3. Equations of the closed subgroups descend by
   the injection, so the factors lie in the required root groups and weight torus
   over S. Invert the two root-coordinate identifications to obtain A and B, and
   take h to be the middle factor.
7. At zero, uniqueness gives identity factors and zero root coordinates. Evaluation
   extends to every F-algebra in which d is a unit, proving the asserted identity
   including nilpotents and characteristics two and three. With no roots all products
   are empty and one takes d=1, the unique coordinate maps, and the identity character.
-/
theorem exists_opposite_rational_collection
    (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (R : Set V) (c : R → Module.Dual ℚ V)
    (hfinite : R.Finite) (hne : ∀ a : R, (a : V) ≠ 0)
    (hspan : Submodule.span ℚ R = ⊤) (htwo : ∀ a : R, c a a = 2)
    (hint : ∀ a b : R, ∃ n : ℤ, c a b = (n : ℚ))
    (hreflect : ∀ a : R, Set.BijOn (fun v : V ↦ v - c a v • (a : V)) R R)
    (hreduced : ∀ a : R,
      R ∩ (Submodule.span ℚ ({(a : V)} : Set V) : Set V) = {(a : V), -(a : V)})
    (P : Submodule ℤ V)
    (hP : ∀ v : V, v ∈ P ↔ ∀ a : R, ∃ n : ℤ, c a v = (n : ℚ))
    (g : Type v) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    [HasTrivialRadical ℚ g] (H : LieSubalgebra ℚ g) [IsLieAbelian H]
    (hmax : ∀ K : LieSubalgebra ℚ g, H ≤ K → IsLieAbelian K → K = H)
    (θ : H ≃ₗ[ℚ] Module.Dual ℚ V) (e : R → g)
    (he : ∀ a : R, e a ≠ 0 ∧ ∀ h : H, ⁅(h : g), e a⁆ = θ h a • e a)
    (hdecomp : DirectSum.IsInternal (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
      (fun a : R ↦ Submodule.span ℚ ({e a} : Set g))))
    (r : ℕ) (b : Module.Basis (Fin r) ℚ V) (hb : ∀ i, b i ∈ R)
    (hbase : ∀ a : R, (∀ i, ∃ n : ℤ, b.repr a i = (n : ℚ)) ∧
      ((∀ i, 0 ≤ b.repr a i) ∨ (∀ i, b.repr a i ≤ 0)))
    (B : Module.Basis (Fin r ⊕ R) ℚ g)
    (Bh : ∀ i, B (Sum.inl i) = (θ.symm (c ⟨b i, hb i⟩) : g))
    (Be : ∀ a : R, B (Sum.inr a) = e a)
    (hopp : ∀ a k : R, (k : V) = -(a : V) → ⁅e a, e k⁆ = (θ.symm (c a) : g))
    (hadd : ∀ a k l : R, (a : V) + (k : V) = (l : V) →
      ∃ p : ℕ, (k : V) - p • (a : V) ∈ R ∧
        (∀ n : ℕ, (k : V) - n • (a : V) ∈ R → n ≤ p) ∧
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ⁅e a, e k⁆ = ((ε : ℚ) * (p + 1 : ℚ)) • e l)
    (hzero : ∀ a k : R, (a : V) + (k : V) ≠ 0 → (a : V) + (k : V) ∉ R →
      ⁅e a, e k⁆ = 0)
    (W : Type w) [AddCommGroup W] [Module ℚ W]
    [LieRingModule g W] [LieModule ℚ g W] [FiniteDimensional ℚ W]
    [LieModule.IsFaithful ℚ g W] (Λ : Submodule ℤ W)
    [Submodule.IsLattice ℚ Λ] [Module.Free ℤ Λ] (Ω : Finset V)
    (hΩP : ∀ μ ∈ Ω, μ ∈ P)
    (hΩne : ∀ μ ∈ Ω, LieModule.weightSpace W (fun h : H ↦ θ h μ) ≠ ⊥)
    (hW : DirectSum.IsInternal (fun μ : Ω ↦
      (LieModule.weightSpace W (fun h : H ↦ θ h μ)).toSubmodule))
    (hgenerate : Submodule.span ℤ (Ω : Set V) = P)
    (hΛ : DirectSum.IsInternal (fun μ : Ω ↦ latticeWeightSpace H θ Λ μ))
    (n : R → ℕ) (hn : ∀ a : R, (LieModule.toEnd ℚ g W (e a)) ^ n a = 0)
    (hstable : ∀ (a : R) (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • (LieModule.toEnd ℚ g W (e a)) ^ m) w ∈ Λ)
    (N : ℕ) (β : Fin N ≃ {a : R // ∀ i, 0 ≤ b.repr (a : V) i})
    (horder : ∀ i j : Fin N, i ≤ j →
      (∑ k, b.repr ((β i).val : V) k) ≤ ∑ k, b.repr ((β j).val : V) k)
    (negative : Fin N → R) (hnegative : ∀ i, (negative i : V) = -((β i).val : V))
    (F : Type t) [Field F] [IsAlgClosed F] :
    ∃ d : MvPolynomial (Fin N ⊕ Fin N) F,
      ∃ hd : MvPolynomial.aeval (fun _ : Fin N ⊕ Fin N ↦ (0 : F)) d = 1,
      ∃ (A B : Fin N → Localization.Away d)
        (h : AddMonoidAlgebra F P →ₐ[F] Localization.Away d),
        ((List.ofFn (fun i : Fin N ↦ rootExponential
          (fun m ↦ latticeDividedPower Λ (LieModule.toEnd ℚ g W (e (β i).val)) m
            (hstable (β i).val m)) (n (β i).val)
          (algebraMap (MvPolynomial (Fin N ⊕ Fin N) F) (Localization.Away d)
            (MvPolynomial.X (Sum.inr i))))).prod *
        (List.ofFn (fun i : Fin N ↦ rootExponential
          (fun m ↦ latticeDividedPower Λ (LieModule.toEnd ℚ g W (e (negative i))) m
            (hstable (negative i) m)) (n (negative i))
          (algebraMap (MvPolynomial (Fin N ⊕ Fin N) F) (Localization.Away d)
            (MvPolynomial.X (Sum.inl i))))).prod =
        (List.ofFn (fun i : Fin N ↦ rootExponential
          (fun m ↦ latticeDividedPower Λ (LieModule.toEnd ℚ g W (e (negative i))) m
            (hstable (negative i) m)) (n (negative i)) (A i))).prod *
        torusAction (fun μ : Ω ↦ latticeWeightSpace H θ Λ μ) hΛ
          (fun μ : Ω ↦ (⟨μ.val, hΩP μ.val μ.property⟩ : P)) h *
        (List.ofFn (fun i : Fin N ↦ rootExponential
          (fun m ↦ latticeDividedPower Λ (LieModule.toEnd ℚ g W (e (β i).val)) m
            (hstable (β i).val m)) (n (β i).val) (B i))).prod) ∧
        (∀ i, origin d hd (A i) = 0 ∧ origin d hd (B i) = 0) ∧
        (∀ μ : P, origin d hd (h (AddMonoidAlgebra.single μ 1)) = 1) ∧
        (R = ∅ → d = 1 ∧ (∀ i, A i = 0 ∧ B i = 0) ∧
          ∀ μ : P, h (AddMonoidAlgebra.single μ 1) = 1) := by
  sorry

end LieAlgebra.ChevalleyCollection
