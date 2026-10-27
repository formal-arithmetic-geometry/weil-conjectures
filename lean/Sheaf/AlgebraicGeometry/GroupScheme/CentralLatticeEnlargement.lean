module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Central isogenies realizing integral lattice enlargements

Source: Milne, Algebraic Groups (2017), Appendix C.35, p.615; Theorem 23.55 and
Corollary 23.56, p.501; Theorem 23.9, p.487; Proposition 23.5, pp.485--486.
(blueprint: lem-sfb-central-lattice-enlargement)

The rationalization has its rational factor first, by canonical tensor symmetry.
The lattice is an actual integral submodule of that rationalization. Its identification
with the new torus's character group records the specified inclusion pointwise.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- An integral finite enlargement of the character lattice of a semisimple group
is realized by a central isogeny, which is an isomorphism exactly for no enlargement.

Source: Milne, Appendix C.35, p.615; Theorem 23.55 and Corollary 23.56, p.501;
Theorem 23.9, p.487; Proposition 23.5, pp.485--486.
(blueprint: lem-sfb-central-lattice-enlargement)

Proof plan:
1. Restrict each rational coroot functional to L. The integral-evaluation hypothesis
   makes it integer valued. It pairs with its root to 2. Each reflection preserves L:
   subtract the integer coroot evaluation times its root, which belongs to X ⊆ L.
   The reflection squares to the identity and permutes the original finite root set.
   Since the roots span the rational space, the reflection group acts faithfully on
   that set and is finite. Distinct coroots remain distinct upon restriction to X;
   reducedness is unchanged. This checks every reduced-root-datum axiom on L.
2. Apply lem-sfb-root-datum-realization to this datum to obtain a split reductive
   group with the prescribed character lattice L. Its roots still span, so
   lem-sfb-semisimple-roots-span makes the realized group semisimple.
3. For X → L use the identity root bijection and exponent 1 for every root.
   Restricting a new coroot back to X recovers the original coroot. The inclusion
   is injective with finite cokernel. Apply lem-sfb-root-datum-isogeny-realization
   to obtain the surjective group homomorphism and its surjective torus restriction.
   Exponents 1 imply centrality of the full scheme-theoretic kernel. Its isomorphism
   criterion is exactly that X → L is an isomorphism, equivalently L equals the
   canonical image of X. No separability or prime-to-characteristic condition occurs.
The hypotheses specifying P unpack the root-datum conventions of
lem-sfb-reductive-borel-pair-structure: actual characters, composition pairing and
exactly the nonzero weights of conjugation on the tangent space. -/
theorem exists_central_isogeny_of_lattice_enlargement
    {F : Type u} [Field F] [IsAlgClosed F]
    (H T : Grp (Over (Spec (.of F)))) (hH : IsSemisimpleGroupScheme H.X)
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
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T H aH χ.toMul ≠ ⊥)
    (hspan : Submodule.span ℚ
      (Set.range (fun α : Φ ↦ TensorProduct.tmul ℤ (1 : ℚ) (P.root α))) = ⊤)
    (L : Submodule ℤ
      (ℚ ⊗[ℤ] Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (hrank : Module.finrank ℤ L = Module.finrank ℚ
      (ℚ ⊗[ℤ] Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (hXL : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      TensorProduct.tmul ℤ (1 : ℚ) χ ∈ L)
    (hindex : Finite (L ⧸ Submodule.comap L.subtype
      (LinearMap.range (TensorProduct.mk ℤ ℚ _ 1))))
    (hintegral : ∀ (l : L) (α : Φ), ∃ n : ℤ,
      (((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' α)).liftBaseChange ℚ) l.val =
        (n : ℚ)) :
    ∃ (HL TL : Grp (Over (Spec (.of F)))) (iTL : TL ⟶ HL)
      (_ : IsCommMonObj TL.X)
      (e : Additive (TL ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) ≃ₗ[ℤ] L)
      (f : HL ⟶ H) (fT : TL ⟶ T),
      IsSemisimpleGroupScheme HL.X ∧
      ReductiveTorusCentralizer.IsMaximalTorus iTL ∧
      (∃ r : ℕ, Nonempty (TL ≅ MultiplicativeType.splitTorus F r)) ∧
      Surjective f.hom.hom.left ∧ IsFinite (GrpObj.ker f.hom.hom).hom ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f.hom.hom)
        (g : StandardGroupSchemes.affine F A ⟶ HL.X),
        (x ≫ GrpObj.kerι f.hom.hom) * g = g * (x ≫ GrpObj.kerι f.hom.hom)) ∧
      iTL ≫ f = fT ≫ iT ∧ Surjective fT.hom.hom.left ∧
      (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        (e (Additive.ofMul (fT ≫ χ.toMul))).val = TensorProduct.tmul ℤ (1 : ℚ) χ) ∧
      (IsIso f ↔ L = LinearMap.range (TensorProduct.mk ℤ ℚ _ 1)) := by
  sorry

end AlgebraicGeometry
