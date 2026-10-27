module

public import Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Polynomial coordinates for the two one-sign Chevalley groups

Source: Milne, Algebraic Groups (2017), Section 23h, equation (153), Theorem 23.72
and Notes, printed pp.510--511; agent-expanded one-sign collection argument
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates).

An integral basis of the weight-decomposed lattice identifies its scalar extension
with coordinate vectors. Closedness together with the subgroup criterion on every
test algebra specifies the two closed subgroup schemes.
The formulas below characterize the coordinate morphisms on all test algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.ChevalleyCoordinates

/-- The actual weight-character torus with the group-algebra Hopf structure.
Source: Milne, 23h, pp.510--511
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates). -/
def weightTorus {V : Type u} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℤ V) (F : Type u) [Field F] : Over (Spec (.of F)) :=
  StandardGroupSchemes.affine F (AddMonoidAlgebra F P)

/-- Integral matrix of a divided root power in a chosen lattice basis.
Source: Milne, equation (153), p.510
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates). -/
def dividedMatrix {W : Type u} [AddCommGroup W] [Module ℚ W]
    (Λ : Submodule ℤ W) (d : ℕ) (b : Module.Basis (ULift.{u} (Fin d)) ℤ Λ)
    (E : Module.End ℚ W)
    (h : ∀ (m : ℕ) (w : W), w ∈ Λ → ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ)
    (m : ℕ) : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) ℤ :=
  LinearMap.toMatrix b b
    ((((Nat.factorial m : ℚ)⁻¹ • E ^ m).restrictScalars ℤ).restrict (h m))

/-- Finite exponential, with its coefficients reduced only after taking divided powers.
The extra zero term makes the formula valid even for the zero module.
Source: Milne, equation (153), p.510
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates). -/
def rootMatrix {W : Type u} [AddCommGroup W] [Module ℚ W]
    (Λ : Submodule ℤ W) (d : ℕ) (b : Module.Basis (ULift.{u} (Fin d)) ℤ Λ)
    (E : Module.End ℚ W)
    (h : ∀ (m : ℕ) (w : W), w ∈ Λ → ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ)
    (A : Type u) [CommRing A] (a : A) : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A :=
  ∑ m ∈ Finset.range (nilpotencyClass E + 1),
    a ^ m • (dividedMatrix Λ d b E h m).map (Int.castRingHom A)

/-- An ordered product of the actual root exponential matrices.
Source: Milne, equation (153), p.510 and the one-sign collection argument
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates). -/
def orderedProduct {W : Type u} [AddCommGroup W] [Module ℚ W]
    (Λ : Submodule ℤ W) (d : ℕ) (b : Module.Basis (ULift.{u} (Fin d)) ℤ Λ)
    {I : Type u} (E : I → Module.End ℚ W)
    (h : ∀ (i : I) (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • E i ^ m) w ∈ Λ)
    (N : ℕ) (β : Fin N → I) (A : Type u) [CommRing A] (a : Fin N → A) :
    Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A :=
  ((List.finRange N).map (fun i ↦ rootMatrix Λ d b (E (β i)) (h (β i)) A (a i))).prod

/-- The affine point with the given coordinate tuple.
Source: Milne, one-sign root coordinates following (153), pp.510--511
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates). -/
def parameterPoint (F : Type u) [Field F] (N : ℕ)
    (A : Type u) [CommRing A] [Algebra F A] (a : Fin N → A) :
    StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.affine F (MvPolynomial (Fin N) F) :=
  StandardGroupSchemes.map F (MvPolynomial.aeval a)

open Classical in
/-- Ordered positive and negative exponentials give closed subgroup charts, and are
block unitriangular for every positive weight-separating rational functional.

Source: Milne, equation (153), Theorem 23.72 and Notes, printed pp.510--511;
agent-stated supporting lemma, not a reductivity consequence
(blueprint: lem-sfb-chevalley-unipotent-polynomial-coordinates).

Proof plan:
The torus is the spectrum of the standard group-algebra Hopf algebra. The weights
generate P, so the weight characters and their inverses generate its coordinate ring;
its diagonal representation is a closed embedding.

1. Use lem-sfb-root-base-rational-integral-spans on the dual pairing. Simple coroots
   are an integral basis of the coroot lattice. Apply lem-sfb-root-base-reflection-induction:
   simple coroots are primitive, and negation and integral simple reflections preserve
   primitivity. Every coroot therefore takes the value one on some weight in P.
2. If a root operator vanished modulo p, its bracket with the opposite root would
   vanish. Every weight-coroot pairing would be divisible by p. Since the weights
   generate P this contradicts step 1. In characteristic zero use faithfulness.
3. The Cartan bracket makes the m-th divided power shift weight by m times the root.
   Admissibility gives the same integral-block assertion after every base change.
   Positive q makes these strictly upper blocks, and negative roots give lower blocks.
4. The integral divided-power multiplication identity gives x(s)x(t)=x(s+t),
   identity x(0), and inverse x(-s). Thus every finite product lands in GL.
5. For each root beta choose a nonzero entry c_beta of its reduced root operator.
   The corresponding entry of the product is c_beta times its parameter plus a
   polynomial involving only roots of strictly smaller height: a sum of positive
   shifts equal to beta can use no other root of the same or greater height.
6. Recursively subtract that polynomial and divide by c_beta. This recovers each
   parameter as a polynomial in matrix entries. The coordinate-ring pullback is
   surjective, so def-weil-closed-immersion gives a closed immersion for both signs.
7. Apply lem-sfb-chevalley-nonopposite-exponential-commutator to exchange adjacent
   distinct roots. With the signs of the parameters reversed, all extra factors
   have strictly larger height and stand to the right. Equal roots combine by step 4.
8. Collect a finite word in increasing height. Exchanging height-h factors introduces
   only larger heights, so finitely many exchanges collect the height-h tail.
   After the maximal height there is no tail. Products and inverses are thus ordered
   products with polynomial parameters, over arbitrary algebras including nilpotents.
9. Transport those laws to the affine space. Injectivity gives all group identities,
   and def-sc-group-scheme-subgroup gives the closed subgroup assertion.
10. For empty roots N=0 and both products are the identity. The affine source is
    Spec F, closed in GL by the equations saying that all matrix entries are identity.
    No characteristic, positive rank, nonempty roots or ambient reductivity is used. -/
theorem unipotent_polynomial_coordinates
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
    (g : Type u) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    (hsemi : LieAlgebra.HasTrivialRadical ℚ g)
    (H : LieSubalgebra ℚ g) (hab : IsLieAbelian H)
    (hmax : ∀ K : LieSubalgebra ℚ g, H ≤ K → IsLieAbelian K → K = H)
    (θ : H ≃ₗ[ℚ] Module.Dual ℚ V) (e : R → g)
    (he : ∀ a : R, e a ≠ 0 ∧ ∀ h : H, ⁅(h : g), e a⁆ = θ h a • e a)
    (hdecomp : DirectSum.IsInternal (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
      (fun a : R ↦ Submodule.span ℚ ({e a} : Set g))))
    (r : ℕ) (simple : Module.Basis (Fin r) ℚ V) (hsimple : ∀ i, simple i ∈ R)
    (hbase : ∀ a : R, (∀ i, ∃ n : ℤ, simple.repr a i = (n : ℚ)) ∧
      ((∀ i, 0 ≤ simple.repr a i) ∨ (∀ i, simple.repr a i ≤ 0)))
    (B : Module.Basis (Fin r ⊕ R) ℚ g)
    (hB : (∀ i, B (Sum.inl i) = (θ.symm (c ⟨simple i, hsimple i⟩) : g)) ∧
      (∀ a : R, B (Sum.inr a) = e a))
    (neg : R → R) (hneg : ∀ a : R, (neg a : V) = -(a : V))
    (hopposite : ∀ a : R, ⁅e a, e (neg a)⁆ = (θ.symm (c a) : g))
    (hbracket : ∀ a b k : R, (a : V) + (b : V) = (k : V) →
      ∃ p : ℕ, (b : V) - p • (a : V) ∈ R ∧
        (∀ n : ℕ, (b : V) - n • (a : V) ∈ R → n ≤ p) ∧
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ⁅e a, e b⁆ = ((ε : ℚ) * (p + 1 : ℚ)) • e k)
    (hzero : ∀ a b : R, (a : V) + (b : V) ≠ 0 → (a : V) + (b : V) ∉ R → ⁅e a, e b⁆ = 0)
    (W : Type u) [AddCommGroup W] [Module ℚ W] [LieRingModule g W] [LieModule ℚ g W]
    [FiniteDimensional ℚ W] (hfaithful : LieModule.IsFaithful ℚ g W)
    (Λ : Submodule ℤ W) [Submodule.IsLattice ℚ Λ] [Module.Free ℤ Λ]
    (Ω : Finset V)
    (hweights : ∀ μ ∈ Ω, μ ∈ P ∧ LieModule.weightSpace W (fun h : H ↦ θ h μ) ≠ ⊥)
    (hweightSum : DirectSum.IsInternal (fun μ : Ω ↦
      (LieModule.weightSpace W (fun h : H ↦ θ h μ)).toSubmodule))
    (hgenerate : Submodule.span ℤ (Ω : Set V) = P)
    (hlatticeSum : DirectSum.IsInternal (fun μ : Ω ↦
      ((LieModule.weightSpace W (fun h : H ↦ θ h μ)).toSubmodule.restrictScalars
        ℤ).comap Λ.subtype))
    (hnil : ∀ a : R, IsNilpotent (LieModule.toEnd ℚ g W (e a)))
    (hstable : ∀ (a : R) (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • (LieModule.toEnd ℚ g W (e a)) ^ m) w ∈ Λ)
    (d : ℕ) (b : Module.Basis (ULift.{u} (Fin d)) ℤ Λ) (weight : ULift.{u} (Fin d) → Ω)
    (hhomogeneous : ∀ j, (b j : W) ∈
      LieModule.weightSpace W (fun h : H ↦ θ h (weight j)))
    (N : ℕ) (β : Fin N ≃ {a : R // ∀ i, 0 ≤ simple.repr a i})
    (horder : ∀ i j : Fin N, i ≤ j →
      (∑ k, simple.repr (β i).val k) ≤ ∑ k, simple.repr (β j).val k)
    (F : Type u) [Field F] [IsAlgClosed F] :
    ∃ (pPlus pMinus : StandardGroupSchemes.affine F (MvPolynomial (Fin N) F) ⟶
        GeneralLinearGroup (ULift.{u} (Fin d)) F)
      (torusEmbedding : weightTorus P F ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) F),
      IsClosedImmersion pPlus.left ∧ IsClosedImmersion pMinus.left ∧
      IsClosedImmersion torusEmbedding.left ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (χ : AddMonoidAlgebra F P →ₐ[F] A),
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
          (StandardGroupSchemes.map F χ ≫ torusEmbedding) :
            Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A) =
          Matrix.diagonal (fun j ↦ χ (AddMonoidAlgebra.single
            ⟨(weight j).val, (hweights _ (weight j).property).1⟩ 1))) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A] (a : Fin N → A),
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
          (parameterPoint F N A a ≫ pPlus) : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A) =
            orderedProduct Λ d b (fun α : R ↦ LieModule.toEnd ℚ g W (e α))
              hstable N (fun i ↦ (β i).val) A a ∧
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
          (parameterPoint F N A a ≫ pMinus) : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A) =
            orderedProduct Λ d b (fun α : R ↦ LieModule.toEnd ℚ g W (e α))
              hstable N (fun i ↦ neg (β i).val) A a) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A],
        ∃ UPlus UMinus : Subgroup (GL (ULift.{u} (Fin d)) A),
          (UPlus : Set (GL (ULift.{u} (Fin d)) A)) = Set.range (fun a : Fin N → A ↦
            GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
              (parameterPoint F N A a ≫ pPlus)) ∧
          (UMinus : Set (GL (ULift.{u} (Fin d)) A)) = Set.range (fun a : Fin N → A ↦
            GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
              (parameterPoint F N A a ≫ pMinus))) ∧
      (∀ (q : V →ₗ[ℚ] ℚ), (∀ i, 0 < q (simple i)) →
        Set.InjOn q (Ω : Set V) →
        ∀ (A : Type u) [CommRing A] [Algebra F A] (a : Fin N → A) (i j : ULift.{u} (Fin d)),
          (q (weight i) ≤ q (weight j) →
            orderedProduct Λ d b (fun α : R ↦ LieModule.toEnd ℚ g W (e α))
              hstable N (fun k ↦ (β k).val) A a i j =
                (1 : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A) i j) ∧
          (q (weight j) ≤ q (weight i) →
            orderedProduct Λ d b (fun α : R ↦ LieModule.toEnd ℚ g W (e α))
              hstable N (fun k ↦ neg (β k).val) A a i j =
                (1 : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A) i j)) ∧
      (R = ∅ → N = 0 ∧ ∀ (A : Type u) [CommRing A] [Algebra F A] (a : Fin N → A),
        GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
              (parameterPoint F N A a ≫ pPlus) = 1 ∧
        GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A
              (parameterPoint F N A a ≫ pMinus) = 1) := by
  sorry

end AlgebraicGeometry.ChevalleyCoordinates
