/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q159
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra

/-! # Frobenius twist of a reductive group and its full root datum

Source: Milne, Algebraic Groups (2017), 2.25--2.29, pp.47--49; 12.9 and 21.11;
proof of 23.27, p.493 (blueprint: lem-sfb-reductive-frobenius-twist).

The twist is the existing scalar-extension functor specialized to Frobenius.
Its underlying pullback is the spectrum of C tensor_{F,sigma} F. The maps below
are characterized on the old coordinates and on the Laurent variable, so their
existential presentation does not allow an arbitrary Frobenius or lattice map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.GroupSchemeFrobenius

/-- Scalar extension along a ↦ a^p, using the existing group-scheme base change.
Source: Milne, 2.26 and 2.28, pp.47--48
(blueprint: lem-sfb-reductive-frobenius-twist). -/
noncomputable abbrev twist (F : Type u) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    Grp (Over (Spec (.of F))) ⥤ Grp (Over (Spec (.of F))) :=
  @MultiplicativeType.baseChange F F _ _ (frobenius F p).toAlgebra

/-- Frobenius preserves reductivity, split maximal tori, and the entire reduced
root datum, and its relative map is a faithfully flat surjection with finite kernel.
The Laurent-coordinate equation fixes the identification of the twisted G_m.
The equation on all old global functions, together with F-linearity, is exactly
b tensor c ↦ c b^p. The two additive equivalences are fixed to scalar extension
of characters and cocharacters, including the central directions.

Source: Milne, 2.25--2.29, pp.47--49; 12.9 and 21.11; proof of 23.27, p.493
(blueprint: lem-sfb-reductive-frobenius-twist).

Proof plan, following the eleven steps of the node:
1. Algebraic closedness makes sigma bijective. The balancing relation gives
   j_A(a) = a tensor 1 with inverse a tensor c ↦ sigma^{-1}(c)a; these commute
   with algebra maps (lem-weil-pbc-algebra-tensor-pushout-universal-property).
2. Twisting by the inverse automorphism reverses presentations and square-zero
   lifting problems. Thus affineness, finite type, connectedness and smoothness
   are preserved (def-sbc-smooth-morphisms).
3. Closed subgroup and normality diagrams twist invertibly. Faithful matrix
   representations and (u-I)^n=0 twist as well. Hence unipotence, reductivity,
   splitting and maximality of T are preserved and reflected.
4. Twist character and cocharacter maps and identify G_m by its Laurent variable.
   Composition z ↦ z^n is unchanged for every integer n, so the pairing is fixed
   (lem-sfb-reductive-borel-pair-structure).
5. Apply the twist to dual numbers. It gives a sigma-semilinear tangent bijection
   respecting conjugation and all character weights, so roots correspond exactly
   (lem-sfb-reductive-rank-one-reflections).
6. Twist the rank-one centralizers and their normalizer quotients. Their unique
   nonidentity Weyl elements correspond. The reflection identity and uniqueness
   of its cocharacter give precisely the asserted coroot correspondence, using
   lem-sfb-reductive-rank-one-reflections, without differentials of characters.
7. The tensor map b tensor c ↦ c b^p respects comultiplication, counit and antipode
   on pure tensors (lem-sfb-affine-group-coordinate-hopf and
   lem-sfb-hopf-spectrum-functor). It defines the specified group homomorphism.
8. Smoothness implies reducedness (sbc-lem-smooth-geometrically-reduced and
   lem-weil-pbc-affine-scheme-reduced-iff). Write each tensor as d tensor 1;
   d^p=0 implies d=0. Both coordinate algebras are finitely generated, by
   lem-pc-affine-finite-type-algebra.
9. Apply lem-sfb-hopf-subalgebra-faithfully-flat to that injective Hopf map.
   Absolute Frobenius fixes prime ideals, proving surjectivity on spectra.
10. If z_1,...,z_N generate C, their images in the kernel algebra satisfy
    z_i^p=epsilon(z_i)^p. Monomials of exponents less than p span it, including
    the empty monomial when N=0. Thus the scheme-theoretic kernel is finite.
11. Frobenius commutes with subgroup coordinate quotients, yielding the torus
    square. Pullback of u_chi tensor 1 is u_chi^p, proving the p-character law.
    Empty root families (tori) and the trivial group require no exceptions. -/
theorem reductive_frobenius_twist
    {F : Type u} [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (G T : Grp (Over (Spec (.of F)))) (i : T ⟶ G)
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) :
    ReductiveTorusCentralizer.IsReductive ((twist F p).obj G) ∧
    ReductiveTorusCentralizer.IsMaximalTorus ((twist F p).map i) ∧
    (∃ r : ℕ, Nonempty ((twist F p).obj T ≅ MultiplicativeType.splitTorus F r)) ∧
    ∃ (fG : G ⟶ (twist F p).obj G) (fT : T ⟶ (twist F p).obj T)
      (e : (twist F p).obj (Grp.mk (StandardGroupSchemes.multiplicative F)) ≅
        Grp.mk (StandardGroupSchemes.multiplicative F))
      (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
      (_ : IsCommMonObj T.X) (_ : IsCommMonObj ((twist F p).obj T).X)
      (iota : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) ≃+
        Additive ((twist F p).obj T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (kappa : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T) ≃+
        Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ (twist F p).obj T))
      (a : ModObj T.X G.X)
      (ap : ModObj ((twist F p).obj T).X ((twist F p).obj G).X)
      (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
      (P : RootDatum Φ
        (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
      (Pp : RootDatum Φ
        (Additive ((twist F p).obj T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ (twist F p).obj T))),
      (∀ b : Γ(G.X.left, ⊤),
        fG.hom.hom.left.appTop
          ((pullback.fst G.X.hom
            (Spec.map (CommRingCat.ofHom (frobenius F p)))).appTop b) = b ^ p) ∧
      (∀ b : Γ(T.X.left, ⊤),
        fT.hom.hom.left.appTop
          ((pullback.fst T.X.hom
            (Spec.map (CommRingCat.ofHom (frobenius F p)))).appTop b) = b ^ p) ∧
      e.hom.hom.hom.left.appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1)) =
        (pullback.fst (StandardGroupSchemes.multiplicative F).hom
          (Spec.map (CommRingCat.ofHom (frobenius F p)))).appTop
            ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1)) ∧
      (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        (iota χ).toMul = (twist F p).map χ.toMul ≫ e.hom) ∧
      (∀ ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T),
        (kappa ν).toMul = e.inv ≫ (twist F p).map ν.toMul) ∧
      Surjective fG.hom.hom.left ∧ fG.hom.hom.left.appTop.hom.FaithfullyFlat ∧
      IsFinite (GrpObj.ker fG.hom.hom).hom ∧
      i ≫ fG = fT ≫ (twist F p).map i ∧
      (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        fT.hom.hom ≫ (iota χ).toMul.hom.hom = χ.toMul.hom.hom ^ p) ∧
      Module.Finite ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
      Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)) ∧
      Module.Finite ℤ
        (Additive ((twist F p).obj T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
      Module.Finite ℤ
        (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ (twist F p).obj T)) ∧
      P.IsReduced ∧ Pp.IsReduced ∧
      a.smul = (i.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X ∧
      ap.smul = (((twist F p).map i).hom.hom ⊗ₘ 𝟙 ((twist F p).obj G).X) ≫
        GrpObj.conj ((twist F p).obj G).X ∧
      (∀ α : Φ, P.root α = α.val) ∧
      (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G a χ.toMul ≠ ⊥) ∧
      (∀ χ : Additive ((twist F p).obj T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        (∃ α : Φ, Pp.root α = χ) ↔ χ ≠ 0 ∧
          @TorusCharacterTangent.weightSpace F _ ((twist F p).obj T)
            ((twist F p).obj G) ap χ.toMul ≠ ⊥) ∧
      (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
        ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
          (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν)) ∧
      (∀ (χ : Additive ((twist F p).obj T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ (twist F p).obj T)),
        ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
          (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (Pp.toLinearMap χ ν)) ∧
      (∀ α : Φ, Pp.root α = iota (P.root α) ∧ Pp.coroot α = kappa (P.coroot α)) ∧
      ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
        Pp.toLinearMap (iota χ) (kappa ν) = P.toLinearMap χ ν := by
  sorry

end AlgebraicGeometry.GroupSchemeFrobenius
