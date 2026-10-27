/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.LinearAlgebra.RootDatumLatticeEmbedding
import Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation

/-! # Realization of reduced root data by split reductive groups

Source: Milne, Algebraic Groups (2017), Theorem 23.55, p.501;
Definition C.28, pp.613--614.
(blueprint: lem-sfb-root-datum-realization)

The input is the one-sided integral reflection datum of the node. The output uses
actual character and cocharacter groups, with their pairing pinned by composition.
An index equivalence and two lattice equivalences explicitly identify all roots
and coroots. The lattice and field may live in independent universes.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- Every reduced integral root datum is realized by a split reductive group with
split maximal torus and an identification of the full character and cocharacter datum.

Source: Milne, Theorem 23.55, p.501; Definition C.28, pp.613--614.
(blueprint: lem-sfb-root-datum-realization)

Proof plan:
1. Apply lem-sfb-root-datum-lattice-embedding. In the rationalization E, split off
   the root span V from the common coroot annihilator Z. Its weight lattice P and
   central lattice C give an injection j : M → P ⊕ C with finite cokernel. Its
   image N contains (α,0), and the rational coroot on the P projection agrees
   with c α on M. This preserves all central directions.
2. Apply lem-sfb-chevalley-admissible-representation to the rational root system.
   Choose the split rational Lie algebra, faithful representation and integral
   lattice whose weights generate P. The lattice splits into weight sublattices;
   all root divided powers preserve it and eventually vanish.
3. Apply lem-sfb-chevalley-root-exponential-group over F. Reduce those integral
   divided powers to F and sum their finite root exponentials, without dividing
   by factorials in F. Their closed generated group H is split semisimple with
   maximal torus D_F(P), roots R and the prescribed restricted coroots.
4. Apply lem-sfb-central-character-sublattice-quotient to H, C and N. The finite
   central diagonalizable kernel D_F((P ⊕ C)/N) yields the reductive quotient
   G of H × D_F(C). Its maximal torus S has character lattice N, roots (α,0),
   and coroots obtained from projection to P. Nonreduced kernels are allowed.
5. Identify N with M by j⁻¹. The equalities j(α) = (α,0) and
   c α m = c̄ α (π_V m) identify both roots and coroots. Perfect duality gives
   the cocharacter equivalence and compatibility with the composition pairing.
   For empty R the construction has V = P = 0, C = M, H = K = 1 and
   G = D_F(M). For M = 0 this is the trivial group, with no extra hypothesis.
The conjugation action and character weights use precisely the conventions of
lem-sfb-reductive-borel-pair-structure. -/
theorem exists_split_reductive_root_datum_realization
    {F : Type u} [Field F] [IsAlgClosed F]
    (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (R : Set M) (hR : R.Finite) (hzero : (0 : M) ∉ R)
    (c : R → Module.Dual ℤ M) (hc : Function.Injective c)
    (hnorm : ∀ α : R, c α α = 2)
    (hperm : ∀ α : R, Set.BijOn (Module.preReflection (α : M) (c α)) R R)
    (hW : Finite (Subgroup.closure (Set.range (fun α : R ↦ Module.reflection (hnorm α)))))
    (hred : ∀ α : R,
      ((ℚ ∙ (TensorProduct.mk ℤ ℚ M 1 α) : Submodule ℚ (ℚ ⊗[ℤ] M)) : Set _) ∩
        ((TensorProduct.mk ℤ ℚ M 1) '' R) =
          {TensorProduct.mk ℤ ℚ M 1 α, -(TensorProduct.mk ℤ ℚ M 1 α)}) :
    ∃ (G S : Grp (Over (Spec (.of F)))) (iS : S ⟶ G),
      ReductiveTorusCentralizer.IsReductive G ∧
      ReductiveTorusCentralizer.IsMaximalTorus iS ∧
      (∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)) ∧
      ∃ (_ : IsCommMonObj S.X) (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
        (aG : ModObj S.X G.X)
        (Φ : Finset (Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
        (P : RootDatum Φ
          (Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ S)))
        (eX : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) ≃ₗ[ℤ] M)
        (eY : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ S) ≃ₗ[ℤ]
          Module.Dual ℤ M)
        (eR : Φ ≃ R),
        P.IsReduced ∧
        aG.smul = (iS.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X ∧
        (∀ α : Φ, P.root α = α.val) ∧
        (∀ (χ : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ S)),
          ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
            (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν)) ∧
        (∀ χ : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ S G aG χ.toMul ≠ ⊥) ∧
        (∀ (χ : Additive (S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ S)),
          (eY ν) (eX χ) = P.toLinearMap χ ν) ∧
        (∀ α : Φ, eX (P.root α) = (eR α : M)) ∧
        (∀ α : Φ, eY (P.coroot α) = c (eR α)) := by
  sorry

end AlgebraicGeometry
