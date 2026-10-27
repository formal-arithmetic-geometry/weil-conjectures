module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Semisimplicity and rational spanning by roots

Source: Milne, Algebraic Groups (2017), Proposition 21.48, p.439;
Appendix C.34--C.35, p.615; paragraph 22.9, p.465.
(blueprint: lem-sfb-semisimple-roots-span)

Rationalization is written with the rational factor first, by canonical tensor symmetry.
The rational root pairing in the conclusion is fixed on the lattice tensors by the given
integer pairing, and its roots and coroots are the canonical images of the integral ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- A reductive group is semisimple exactly when its roots span the rational character
space. In that case rational extension gives a finite reduced crystallographic root
system in the paired character and cocharacter spaces, so its coroots span as well.

Source: Milne, Proposition 21.48, p.439; Appendix C.34--C.35, p.615;
paragraph 22.9, p.465. (blueprint: lem-sfb-semisimple-roots-span)

Proof plan:
1. Put L = ZΦ and M = X/L. By lem-sfb-reductive-centre-root-quotient the centre is
   D_F(M). Its coordinate algebra has basis indexed by M, so the centre is finite
   exactly when M is finite. The character lattice is finite free by
   lem-sfb-reductive-borel-pair-structure, hence M is finitely generated.
2. Apply lem-sbc-finitely-generated-abelian-group-structure to write M as Z^r plus
   a finite group C. By lem-sfb-diagonalizable-group-geometric-criteria its diagonalizable
   group is G_m^r times D_F(C). It has a nontrivial subtorus if r > 0. If r = 0 it
   is finite, and cannot contain a positive-dimensional torus: a closed immersion
   would give a surjection onto its infinite-dimensional Laurent coordinate algebra.
   Characteristic-primary torsion in C causes no problem: D_F(C) remains finite.
3. By lem-sfb-reductive-radical-quotient the radical is the largest smooth connected
   solvable normal subgroup and the largest central subtorus. The finite normal-series
   and commutator-series solvability conventions agree: derived subgroups lie in every
   normal subgroup with commutative quotient, and induction follows the series;
   conversely the derived series supplies such a normal series. Thus semisimplicity
   is equivalent to finite M. The radical theorem applies to the given smooth connected
   affine finite-type reductive group over the algebraically closed field.
4. Finite M implies rational spanning by killing each class by a positive integer.
   Conversely, express a finite integral basis in rational combinations of roots and
   clear denominators. The resulting torsion generators show M is finite. Freeness
   ensures equalities in the rational space descend to X. This includes rank zero.
5. Extend the perfect integer pairing using dual integral bases. The lattice maps
   remain injective and both reflection formulas extend by bilinearity, with the same
   permutations. Apply lem-sfb-rational-root-coroot-span to this finite crystallographic
   pairing: root spanning implies coroot spanning. Finiteness, nonzero roots, reducedness
   and integrality persist under rationalization (clear denominators). These are exactly
   the displayed root-system properties. For the trivial group both spaces are zero
   and the two root families are empty. -/
theorem semisimple_iff_roots_span
    {F : Type u} [Field F] [IsAlgClosed F]
    (H T : Grp (Over (Spec (.of F)))) (hH : ReductiveTorusCentralizer.IsReductive H)
    (iT : T ⟶ H) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aH : ModObj T.X H.X)
    (hconj : aH.smul = (iT.hom.hom ⊗ₘ 𝟙 H.X) ≫ GrpObj.conj H.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    [Module.Finite ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))]
    [Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T))]
    (hred : P.IsReduced)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T H aH χ.toMul ≠ ⊥) :
    (IsSemisimpleGroupScheme H.X ↔ Submodule.span ℚ
      (Set.range (fun α : Φ ↦ TensorProduct.tmul ℤ (1 : ℚ) (P.root α))) = ⊤) ∧
    (IsSemisimpleGroupScheme H.X →
      ∃ Q : RootPairing Φ ℚ
          (ℚ ⊗[ℤ] Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ℚ ⊗[ℤ] Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
        (∀ α : Φ, Q.root α = TensorProduct.tmul ℤ (1 : ℚ) (P.root α)) ∧
        (∀ α : Φ, Q.coroot α = TensorProduct.tmul ℤ (1 : ℚ) (P.coroot α)) ∧
        (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
          Q.toLinearMap (TensorProduct.tmul ℤ (1 : ℚ) χ)
            (TensorProduct.tmul ℤ (1 : ℚ) ν) = (P.toLinearMap χ ν : ℚ)) ∧
        Q.IsRootSystem ∧ Q.IsReduced ∧ Q.IsCrystallographic) := by
  sorry

end AlgebraicGeometry
