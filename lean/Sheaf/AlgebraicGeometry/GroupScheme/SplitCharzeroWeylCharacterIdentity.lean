module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation
public import Sheaf.AlgebraicGeometry.LinearlyReductiveGroupScheme
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights
public import Sheaf.AlgebraicGeometry.RhoSectionModuleData
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.MonoidAlgebra.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.RhoSectionModules
import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit
import Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
import Sheaf.AlgebraicGeometry.GroupScheme.CharacteristicZeroCompleteReducibility
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.RepresentationTheory.CharZeroDifferentiationHom

/-! # The polynomial Weyl character identity over the rationals

Source: Milne, Algebraic Groups (2017), Theorem 22.52 and the definition of J
before Theorem 22.50, p.480, with the characteristic-zero erratum; 22.53, p.481.
(blueprint: lem-sfb-split-charzero-weyl-character-identity)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct BigOperators

namespace AlgebraicGeometry.SplitWeylCharacter

/-- The actual torus character eigenspace in a rational representation, in a basis.
Over the infinite field Q, rational points of a split torus are schematically dense;
these simultaneous eigenspaces therefore agree with the scheme-theoretic weights.
Source: Milne, 22a, p.463, and 12.12(d).
(blueprint: lem-sfb-split-charzero-weyl-character-identity) -/
def weightSpace {G T : Grp (Over (Spec (.of ℚ)))} (i : T ⟶ G)
    {n : ℕ} (r : GeneralLinearGroup.RationalHom G.X (Fin n)) [IsMonHom r]
    (χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative ℚ)) :
    Submodule ℚ (Fin n → ℚ) :=
  ⨅ t : points T.X ℚ,
    LinearMap.ker (Matrix.toLin' (r.points ℚ (t ≫ i.hom.hom) : Matrix (Fin n) (Fin n) ℚ) -
      RhoSection.characterValue (t ≫ χ.hom.hom) • LinearMap.id)

/-- The Weyl alternant in Q[X], with determinant on the rationalized lattice.
This is a finite group-algebra sum, including the trivial Weyl group.
Source: Milne, definition of J before 22.50, p.480.
(blueprint: lem-sfb-split-charzero-weyl-character-identity) -/
def alternant {I : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) [Fintype P.weylGroup] (ν : X) : AddMonoidAlgebra ℚ X :=
  ∑ w : P.weylGroup, AddMonoidAlgebra.single (w • ν)
    (LinearMap.det ((RootPairing.Equiv.weightEquiv P P w.val).toLinearMap.baseChange ℚ))

/-- Weyl's character formula as a polynomial identity, with the full finite weight
space decomposition and an integral representative of the rational half sum.
The coordinate vector space is an arbitrary finite-dimensional representation in a basis.
Semisimplicity and maximality of the torus are tested after algebraic closure;
centrality and invariant subspaces are tested over every algebra.

Source: Milne, 22.52, p.480 (characteristic-zero erratum), and 22.53, p.481.
(blueprint: lem-sfb-split-charzero-weyl-character-identity)

Proof plan:
1. Apply lem-sfb-split-torus-representation-weight-decomposition. Extend to an
   algebraic closure using lem-sfb-split-semisimple-geometric-root-comparison and
   lem-sfb-split-simple-absolute-irreducibility. A weight basis extends to a basis,
   preserving each weight multiplicity and the differentiated highest vector.
2. Use lem-sfb-reductive-borel-pair-structure and lem-sfb-rho-section-modules to
   obtain integral rho. Use lem-sfb-weyl-reflection-realization and
   lem-sfb-rho-regular-weyl-orbit for the longest element w0. Vanishing of the
   positive root actions gives U-invariance by lem-sfb-char-zero-differentiation-hom;
   lem-sfb-simple-module-dual-highest-weight identifies the highest weight lambda.
3. The dual highest weight is mu = -w0 lambda. Apply
   lem-sfb-primitive-cyclic-weight-bound to its primitive line and transport by
   simple-reflection normalizers to prove dominance of mu.
4. By lem-sfb-homogeneous-line-bundle-sections, x maps to the regular function
   g maps to ell(g inverse x), in E(-mu). It is a nonzero equivariant injection.
   Finite dimensionality from lem-sfb-flag-line-euler-alternant, complete
   reducibility from lem-sfb-characteristic-zero-complete-reducibility, and the
   one-dimensional invariant space of lem-sfb-induced-module-primitive-line show
   it is an isomorphism onto H0(M_mu).
5. Multiplication of character lines descends by lem-pc-fpqc-descent and gives
   M_eta tensor M_xi = M_(eta+xi), M_0 = O, and the inverse character line.
6. Pairings of rho are one by lem-sfb-rho-regular-weyl-orbit. Thus mu+2rho is
   strictly dominant. Apply lem-sfb-strict-dominant-flag-line-ample,
   lem-sfb-flag-canonical-character and lem-sfb-kodaira-vanishing to get higher
   cohomology vanishing for M_mu.
7. Apply lem-sfb-flag-line-euler-alternant: q A(-rho) = A(-mu-rho).
   Reindex with w0 and cancel only the scalar unit det(w0), obtaining the identity.
8. Reducible systems use the same full Weyl sum. For empty roots, spanning makes
   X zero. By lem-sfb-regular-cocharacter-borel-description the group is the
   rank-zero torus. Simplicity gives dimension one, hence q = A(0) = 1.
-/
theorem split_charzero_weyl_character_identity
    (G T : Grp (Over (Spec (.of ℚ)))) [IsAffine G.X.left]
    (hsm : Smooth G.X.hom) (hconn : ConnectedSpace G.X.left)
    (hss : IsSemisimpleGroupScheme
      ((MultiplicativeType.baseChange (K := AlgebraicClosure ℚ)).obj G).X)
    (hsc : ∀ H : Grp (Over (Spec (.of ℚ))),
      Smooth H.X.hom → ConnectedSpace H.X.left → IsAffine H.X.left →
      IsSemisimpleGroupScheme
        ((MultiplicativeType.baseChange (K := AlgebraicClosure ℚ)).obj H).X →
      ∀ f : H ⟶ G, Surjective f.hom.hom.left → IsFinite (GrpObj.ker f.hom.hom).hom →
      (∀ (A : Type) [CommRing A] [Algebra ℚ A]
        (x : StandardGroupSchemes.affine ℚ A ⟶ GrpObj.ker f.hom.hom)
        (g : StandardGroupSchemes.affine ℚ A ⟶ H.X),
        (x ≫ GrpObj.kerι f.hom.hom) * g = g * (x ≫ GrpObj.kerι f.hom.hom)) → IsIso f)
    (i : T ⟶ G)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus ℚ r))
    (hmax : ReductiveTorusCentralizer.IsMaximalTorus
      ((MultiplicativeType.baseChange (K := AlgebraicClosure ℚ)).map i))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative ℚ)]
    (a : ModObj T.X G.X)
    (ha : a.smul = (i.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X)
    (Φ : Finset (Additive (RankOneRoots.Character T)))
    [DecidableEq (Additive (RankOneRoots.Character T))]
    [Module.Finite ℤ (Additive (RankOneRoots.Character T))]
    [Module.Finite ℤ (Additive (RankOneRoots.Cocharacter T))]
    (P : RootDatum Φ (Additive (RankOneRoots.Character T))
      (Additive (RankOneRoots.Cocharacter T)))
    [P.IsReduced] [Fintype P.weylGroup] (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (RankOneRoots.Character T))
      (ν : Additive (RankOneRoots.Cocharacter T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative ℚ)) ^ P.toLinearMap χ ν)
    (hweights : ∀ χ : Additive (RankOneRoots.Character T),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace ℚ _ T G a χ.toMul ≠ ⊥)
    (hspan : Submodule.span ℚ (Set.range (fun α : Φ ↦
      TensorProduct.tmul ℤ (1 : ℚ) (P.root α))) = ⊤)
    (ρ : ℚ ⊗[ℤ] Additive (RankOneRoots.Character T))
    (hρ : ρ = (1 / 2 : ℚ) •
      ∑ α ∈ (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ),
        TensorProduct.tmul ℤ (1 : ℚ) (P.root α))
    (n : ℕ) (r : GeneralLinearGroup.RationalHom G.X (Fin n)) [IsMonHom r]
    (hnonzero : Nontrivial (Fin n → ℚ))
    (hsimple : ∀ U : Submodule ℚ (Fin n → ℚ),
      IsInvariantRationalSubspace r U → U = ⊥ ∨ U = ⊤)
    (lam : Additive (RankOneRoots.Character T))
    (hdom : ∀ α ∈ b.support, 0 ≤ P.toLinearMap lam (P.coroot α))
    (hv : ∃ v : Fin n → ℚ, v ≠ 0 ∧ v ∈ weightSpace i r lam.toMul ∧
      ∀ α : Φ, b.IsPos α → ∀ x ∈ @TorusCharacterTangent.weightSpace ℚ _ T G a α.val.toMul,
        Matrix.toLin' (r.differential x) v = 0) :
    DirectSum.IsInternal
      (fun χ : Additive (RankOneRoots.Character T) ↦ weightSpace i r χ.toMul) ∧
    {χ : Additive (RankOneRoots.Character T) | weightSpace i r χ.toMul ≠ ⊥}.Finite ∧
    ∃ ρ₀ : Additive (RankOneRoots.Character T),
      TensorProduct.tmul ℤ (1 : ℚ) ρ₀ = ρ ∧
      ∃ q : AddMonoidAlgebra ℚ (Additive (RankOneRoots.Character T)),
        (∀ χ : Additive (RankOneRoots.Character T),
          q.coeff χ = (Module.finrank ℚ (weightSpace i r χ.toMul) : ℚ)) ∧
        q * alternant P ρ₀ = alternant P (lam + ρ₀) := by
  sorry

end AlgebraicGeometry.SplitWeylCharacter
