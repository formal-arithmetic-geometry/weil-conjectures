/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # The character lattice of a simply connected semisimple group

Source: Milne, Algebraic Groups (2017), 22.8--22.11, Proposition 23.59 and C.26.
(blueprint: lem-sfb-simply-connected-character-lattice)

The integral basis below lives in the actual group of torus characters. Rationalization
is written with the rational factor first, using the canonical tensor symmetry.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

open Classical in
/-- The simple roots and coroots are rational bases, and the fundamental weights form
an integral basis of the actual torus-character lattice, which is exactly the set of
rational vectors with integral coroot evaluations.

Source: Milne, 22.8--22.11 (pp.464--465), Proposition 23.59 (p.502) and C.26.
(blueprint: lem-sfb-simply-connected-character-lattice)

Proof plan:
1. The Borel-pair structure identifies the actual character and cocharacter groups,
   their perfect integer pairing, roots and positive base. Semisimple implies reductive.
   By lem-sfb-semisimple-roots-span, roots and coroots span the rationalizations.
   Apply lem-sfb-root-base-rational-integral-spans to obtain the two rational bases
   and the integral expansions of all coroots in the simple coroots.
2. Take the rational basis dual to the simple coroots. Integral coroot evaluations
   are equivalent to integral coordinates in this basis, so the weight lattice is
   its integral direct sum. The character lattice lies between the root and weight
   lattices. Clear denominators in the inverse integral root-coordinate matrix to
   find n > 0 with n times the weight lattice contained in the root lattice.
   Thus the weight lattice modulo the character lattice is finite. In rank zero
   both rational spaces and all these lattices are zero.
3. Apply lem-sfb-central-lattice-enlargement to the full weight lattice, giving a
   semisimple group mapping surjectively to G with finite central scheme-theoretic
   kernel and the prescribed character-lattice inclusion. Simple connectedness
   makes this morphism an isomorphism. The enlargement's isomorphism criterion
   gives equality of the character and weight lattices.
4. Transfer the dual rational basis to the actual character lattice to obtain the
   displayed integral basis and Kronecker pairings. Its vectors are genuine
   group-scheme characters by their type. All arguments use integer lattices and
   scheme-theoretic kernels, so no restriction on the characteristic is needed. -/
theorem simplyConnected_character_lattice
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) (hG : IsSemisimpleGroupScheme G.X)
    (hsc : ∀ (G' : Over (Spec (.of F))) [GrpObj G'],
      IsSemisimpleGroupScheme G' → ∀ (f : G' ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F A ⟶ G'),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (hB : IsBorelGroupScheme iB.hom.hom) (hj : j ≫ iB = iT)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
    (haG : aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ CategoryTheory.GrpObj.conj B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥)
    (hpositive : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥) :
    ∃ (ar : Module.Basis b.support ℚ
        (ℚ ⊗[ℤ] Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
      (ac : Module.Basis b.support ℚ
        (ℚ ⊗[ℤ] Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
      (ω : Module.Basis b.support ℤ
        (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))),
      (∀ i : b.support, ar i = TensorProduct.mk ℤ ℚ _ 1 (P.root i)) ∧
      (∀ i : b.support, ac i = TensorProduct.mk ℤ ℚ _ 1 (P.coroot i)) ∧
      (∀ i j : b.support, P.toLinearMap (ω i) (P.coroot j) = if i = j then 1 else 0) ∧
      ∀ v : ℚ ⊗[ℤ] Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        (∃ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          TensorProduct.mk ℤ ℚ _ 1 χ = v) ↔
        ∀ α : Φ, ∃ n : ℤ,
          (((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' α)).liftBaseChange ℚ) v =
            (n : ℚ) := by
  sorry

end AlgebraicGeometry
