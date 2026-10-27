module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Filtration

/-! # Finite jets detect the kernel of an action with a fixed point

Source: Milne, Algebraic Groups (2017), Proposition 8.9, printed p.150,
up to identification of the stable action kernel, and Theorem 7.1, pp.138--139.
(blueprint: lem-sfb-fixed-point-action-finite-jets)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.FixedPointAction

/-- The actual stalk quotient R/m^(n+1) at the rational point.
Source: Milne, Proposition 8.9, p.150
(blueprint: lem-sfb-fixed-point-action-finite-jets). -/
abbrev Jet {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) (n : ℕ) :=
  X.left.presheaf.stalk (x.left (IsLocalRing.closedPoint k)) ⧸
    IsLocalRing.maximalIdeal (X.left.presheaf.stalk (x.left (IsLocalRing.closedPoint k))) ^
      (n + 1)

/-- Scalars on the stalk quotient come from the structure morphism followed by its germ.
Source: Milne, Proposition 8.9, p.150
(blueprint: lem-sfb-fixed-point-action-finite-jets). -/
noncomputable instance jetAlgebra {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) (n : ℕ) : Algebra k (Jet X x n) :=
  ((Ideal.Quotient.mk _).comp
    (StructureSheaf.toStalk k (X.hom (x.left (IsLocalRing.closedPoint k))) ≫
      X.hom.stalkMap (x.left (IsLocalRing.closedPoint k))).hom).toAlgebra

/-- The canonical map Spec(R/m^(n+1)) to X, through Spec of the stalk.
Source: Milne, Proposition 8.9, p.150
(blueprint: lem-sfb-fixed-point-action-finite-jets). -/
noncomputable def jetInclusion {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X) (n : ℕ) :
    Spec (.of (Jet X x n)) ⟶ X.left :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
    X.left.fromSpecStalk (x.left (IsLocalRing.closedPoint k))

/-- Finite jets detect the entire schematic kernel of the action.

Source: Milne, Proposition 8.9, p.150, before using faithfulness; Theorem 7.1,
pp.138--139 (blueprint: lem-sfb-fixed-point-action-finite-jets).

Proof:
1. Rational-point thickenings commute with base change
   (lem-sfb-rational-point-thickenings-base-change). Their coordinate rings are
   nonzero and finite dimensional. Smoothness makes X regular, and connectedness
   makes it integral (lem-weil-pbc-smooth-scheme-over-field-regular,
   lem-sc-regular-connected-integral). Finite type makes H Noetherian
   (lem-weil-pbc-finite-type-over-noetherian).
2. The action of each h preserves the fixed section and its ideal powers.
   Pullback by h inverse on the thickening gives an algebra automorphism T.
   Contravariance and the inverse convention give T_(hh')=T_h T_h'.
   Quotient transition maps are equivariant.
3. In a basis the T_h are invertible matrices, naturally in every test scheme.
   The affine adjunction and Yoneda give rho_n, a group scheme homomorphism
   (lem-a1-locally-ringed-space-affine-adjunction,
   lem-galois-yoneda-fully-faithful).
4. Kernels are closed normal subgroup schemes (lem-sc-kernel-subgroup), and
   finite type as closed subschemes of H. Equivariant surjections of jets give
   descending kernels, or ascending quasi-coherent ideal sheaves
   (lem-weil-pbc-closed-immersion-factor-ideal-inclusion).
5. Noetherian ACC stabilizes these ideals schematically at n0
   (lem-weil-pbc-noetherian-acc-quasi-coherent). The stable kernel K acts
   trivially on every thickening.
6. Its universal fixed subscheme has ideal I contained in every power of the
   fixed-point ideal (lem-sfb-universal-fixed-subscheme). At x, Krull
   intersection gives I_x=0 (lem-weil-pbc-krull-intersection-jacobson).
7. On an integral affine neighborhood, an element killed on localization at x
   is zero in the domain. Any other nonempty affine meets that neighborhood,
   and localization at a nonzero principal-open equation is injective.
   Thus I=0 globally, so K acts trivially on X.
8. This triviality survives every algebra extension. Conversely, universal
   pointwise triviality, tested on affine charts of X_B, makes the action of h
   the identity morphism. Its inverse pullback on every jet is the identity.
   This proves the equivalence even for nonreduced B and B'.

The equation with T specifies inverse-action pullback on Spec(B tensor V_n).
Its matrix in the scalar-extended basis is exactly rho_n(h), fixing rho_n
canonically. Kernel membership is factorization through the actual fibre product.
-/
theorem fixed_point_action_finite_jets
    (k : Type u) [Field k] [IsAlgClosed k]
    (H X : Over (Spec (.of k))) [GrpObj H] [ModObj H X]
    [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [Smooth X.hom] [ConnectedSpace X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)
    (hfixed : ∀ (T : Over (Spec (.of k))) (h : T ⟶ H),
      h • (toUnit T ≫ x) = toUnit T ≫ x) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, 1 ≤ n →
      Nontrivial (Jet X x n) ∧ FiniteDimensional k (Jet X x n) ∧
      ∃ (c : ℕ) (_hc : 1 ≤ c) (b : Module.Basis (LinearGroupSchemes.Index.{u} c) k
          (Jet X x n))
        (jₙ : StandardGroupSchemes.affine k (Jet X x n) ⟶ X)
        (ρ : H ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} c) k)
        (_hρ : IsMonHom ρ),
        jₙ.left = jetInclusion X x n ∧
        IsClosedImmersion jₙ.left ∧
        IsClosedSubgroupScheme (CategoryTheory.GrpObj.kerι ρ) ∧
        IsNormalSubgroupScheme (CategoryTheory.GrpObj.kerι ρ) ∧
        LocallyOfFiniteType (CategoryTheory.GrpObj.ker ρ).hom ∧
        QuasiCompact (CategoryTheory.GrpObj.ker ρ).hom ∧
        (∀ (B : Type u) [CommRing B] [Algebra k B]
            (h : StandardGroupSchemes.affine k B ⟶ H),
          ∃ T : (B ⊗[k] Jet X x n) ≃ₐ[B] (B ⊗[k] Jet X x n),
            StandardGroupSchemes.map k (T.restrictScalars k).toAlgHom ≫
                StandardGroupSchemes.map k
                  (Algebra.TensorProduct.includeRight : Jet X x n →ₐ[k] B ⊗[k] Jet X x n) ≫ jₙ =
              (StandardGroupSchemes.map k
                (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] Jet X x n) ≫ h)⁻¹ •
                (StandardGroupSchemes.map k
                  (Algebra.TensorProduct.includeRight : Jet X x n →ₐ[k] B ⊗[k] Jet X x n) ≫ jₙ) ∧
            ∀ i j : LinearGroupSchemes.Index.{u} c,
              (b.baseChange B).repr (T ((b.baseChange B) j)) i =
                (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} c) k B
                  (h ≫ ρ)).val i j) ∧
        (n₀ ≤ n → ∀ (B : Type u) [CommRing B] [Algebra k B]
            (h : StandardGroupSchemes.affine k B ⟶ H),
          (∃ q : StandardGroupSchemes.affine k B ⟶ CategoryTheory.GrpObj.ker ρ,
            q ≫ CategoryTheory.GrpObj.kerι ρ = h) ↔
          ∀ (B' : Type u) [CommRing B'] [Algebra k B'] (f : B →ₐ[k] B')
            (z : StandardGroupSchemes.affine k B' ⟶ X),
            (StandardGroupSchemes.map k f ≫ h) • z = z) := by
  sorry

end AlgebraicGeometry.FixedPointAction
