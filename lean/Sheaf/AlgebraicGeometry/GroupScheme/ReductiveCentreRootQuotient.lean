module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The centre of a reductive group and the root quotient

Source: Milne, Algebraic Groups (2017), Propositions 21.7--21.8, printed p.427,
and paragraph 21.1, printed p.425 (blueprint: lem-sfb-reductive-centre-root-quotient).

The central subgroup and the intersection of root kernels are identified on every
commutative test algebra. The isomorphism with the group-algebra spectrum is normalized
on every character by its actual Laurent coordinate, so its character identification
and the restriction formula refer to the same isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The centre is the closed intersection of root kernels in a split maximal torus,
and is the diagonalizable group of the quotient of its character lattice by the roots.
The action witness is pinned to conjugation. The finite set Φ is specified as exactly
the nonzero character weights, and L as its integral span (additive subgroup closure).
The equivalence c identifies characters of Z with X/L; its coordinate normalization
pins it to e, and its restriction formula is the quotient map.

Source: Milne, Algebraic Groups (2017), Propositions 21.7--21.8, printed p.427,
and paragraph 21.1, printed p.425 (blueprint: lem-sfb-reductive-centre-root-quotient).

Proof plan:
1. By lem-sfb-affine-group-centre-base-change the universal centralizer condition
   represents a closed centre Z. Its points centralize T, so
   lem-sfb-reductive-torus-self-centralizer gives Z contained in T. Differentiating
   the identity conjugation morphism shows Z is contained in the adjoint kernel N.
2. The weight decomposition in lem-sfb-reductive-rank-one-reflections identifies
   N intersect T with K, the intersection of root kernels: each one-dimensional
   root space is multiplied by the scalar α(t), even over nonreduced algebras.
   The finitely many equations α - 1 define a closed subgroup by
   def-weil-closed-immersion. Thus Z is contained in K.
3. By lem-sfb-split-torus-subgroups-diagonalizable, K is diagonalizable. Apply
   lem-sfb-adjoint-kernel-central-quotient-unipotent to N/Z and
   lem-sfb-diagonalizable-to-unipotent-trivial to the map K to this unipotent
   quotient. It is trivial, proving K contained in Z on every algebra.
4. By lem-sfb-multiplicative-character-antiduality, T is D(X). An A-point is
   a homomorphism X to Aˣ, by def-weil-affine-spectrum and the group-algebra
   basis. It kills every root exactly when it kills L, and then factors uniquely
   through X/L. This is natural in A and multiplicative; its mutually inverse
   universal points give e : Z ≅ D(X/L). On coordinates the inclusion is the
   Hopf map e_x ↦ e_[x], compatible with all three Hopf operations.
5. Character antiduality identifies the character group of D(X/L) with X/L.
   Pulling back a character x along the inclusion evaluates as [x], giving c
   and its restriction formula. The Laurent-coordinate formula is precisely
   this basis-character identification under e. All test algebras are arbitrary,
   including nilpotents. For Φ empty, L is zero and K = T, so Z = T.
-/
theorem reductive_centre_root_quotient {F : Type u} [Field F] [IsAlgClosed F]
    (H T : Grp (Over (Spec (.of F)))) (iT : T ⟶ H)
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) :
    ∃ (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
      (aH : ModObj T.X H.X)
      (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
      (L : AddSubgroup (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))),
      aH.smul = (iT.hom.hom ⊗ₘ 𝟙 H.X) ≫ CategoryTheory.GrpObj.conj H.X ∧
      (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T H aH χ.toMul ≠ ⊥) ∧
      L = AddSubgroup.closure (Φ : Set
        (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))) ∧
      ∃ (Z : Grp (Over (Spec (.of F)))) (j : Z ⟶ T),
          IsClosedSubgroupScheme j.hom.hom ∧
          (∀ (A : Type u) [CommRing A] [Algebra F A],
            ReductiveTorusCentralizer.centralizerPoints (𝟙 H) A =
              Set.range (fun z : StandardGroupSchemes.affine F A ⟶ Z.X ↦
                z ≫ j.hom.hom ≫ iT.hom.hom)) ∧
          (∀ (A : Type u) [CommRing A] [Algebra F A],
            Set.range (fun z : StandardGroupSchemes.affine F A ⟶ Z.X ↦ z ≫ j.hom.hom) =
              {t : StandardGroupSchemes.affine F A ⟶ T.X |
                ∀ α ∈ Φ, t ≫ α.toMul.hom.hom = 1}) ∧
          ∃ e : Z ≅ diagonalizableGroup F
              ((Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ⧸ L),
            ∃ c : Additive (Z ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) ≃+
                ((Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ⧸ L),
              (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
                c (Additive.ofMul (j ≫ χ.toMul)) = QuotientAddGroup.mk' L χ) ∧
              ∀ χ : Additive (Z ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
                (Scheme.ΓSpecIso (.of (AddMonoidAlgebra F
                  ((Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ⧸ L)))).hom
                    ((e.inv ≫ χ.toMul).hom.hom.left.appTop
                      ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
                        (LaurentPolynomial.T 1))) = AddMonoidAlgebra.single (c χ) 1 := by
  sorry

end AlgebraicGeometry
