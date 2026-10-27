/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Central quotients prescribed by a character sublattice

Source: Milne, Algebraic Groups (2017), Exercise 21-4, p.461; 19.26--19.27,
pp.404--405; Section 21a; Proposition 23.5, pp.485--486.
(blueprint: lem-sfb-central-character-sublattice-quotient)

The splitting is normalized on every group-algebra basis element. Thus its induced
kernel is the canonical diagonalizable subgroup, and the character identification
in the conclusion is pullback by the displayed quotient map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

open RankOneRoots

/-- A finite-index character subgroup containing the roots prescribes a finite central
kernel and a reductive quotient, including its maximal torus, roots and integral coroots.
Source: Milne, Exercise 21-4, p.461; 19.26--19.27, pp.404--405; Section 21a;
Proposition 23.5, pp.485--486.
(blueprint: lem-sfb-central-character-sublattice-quotient)

Proof plan:
1. By lem-sfb-diagonalizable-group-geometric-criteria the free finite-rank group C
   gives a split torus. The torus projection and smooth composition lemmas give
   smoothness of H × D(C). The connected-product and rational-point geometric
   connectedness lemmas give geometric connectedness; tensor generators give finite type.
2. A smooth connected normal unipotent subgroup projects trivially into H and D(C),
   by the affine-flat-image, unipotent-normal-image and unipotent-to-multiplicative
   lemmas. Hence the product is reductive.
3. A torus containing T_H × D(C) projects to a torus containing T_H, by the
   torus-homomorphism-image lemma, and therefore equals it. Character antiduality
   identifies its character group with X_H × C and gives the normalized splitting.
4. Character antiduality makes D(X/N) a closed subgroup. Its group algebra has
   finite basis X/N. All roots vanish on it; the centre-root-quotient lemma places
   its H-projection in Z(H). It is central on every algebra, including nonreduced ones.
5. The affine-normal-quotient-geometry lemma represents the fppf coset sheaf, with
   faithfully flat quotient map and the specified scheme-theoretic kernel. It also
   descends smoothness and geometric connectedness.
6. Lift a smooth connected normal unipotent subgroup of the quotient to a smooth
   connected solvable normal subgroup of the product, using the smooth-unipotent-
   solvable and central-isogeny-solvable-normal-lift lemmas. The reductive-radical-
   quotient lemma places the lift in a central torus. Split-torus subgroup
   diagonalizability and the geometric-unitriangular-embedding and diagonalizable-
   to-unipotent-trivial lemmas make its map trivial. Faithful flatness forces the
   original unipotent subgroup to be trivial, proving reductivity.
7. The quotient-borel-torus-images lemma gives the split maximal image torus.
   The faithfully-flat-group-quotient-universal lemma identifies it with T_A/K,
   and identifies its characters with characters upstairs trivial on K, namely N.
8. Choose a Borel at this torus using reductive-borel-pair-structure and
   borel-maximal-torus-conjugacy. The central-isogeny-borel-root-compatibility lemma
   and its product clause identify roots with (α,0) and restrict coroot pairings
   along N → X_H × C. These are integral identities; no separability is used. -/
theorem central_character_sublattice_quotient
    {F : Type u} [Field F] [IsAlgClosed F]
    (H T : Grp (Over (Spec (.of F)))) (hH : IsSemisimpleGroupScheme H.X)
    (iT : T ⟶ H) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aH : ModObj T.X H.X)
    (haH : aH.smul = (iT.hom.hom ⊗ₘ 𝟙 H.X) ≫ CategoryTheory.GrpObj.conj H.X)
    (Φ : Finset (Additive (Character T)))
    (P : RootDatum Φ (Additive (Character T)) (Additive (Cocharacter T)))
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (Character T)) (ν : Additive (Cocharacter T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (Character T),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T H aH χ.toMul ≠ ⊥)
    (C : Type u) [AddCommGroup C] [Module.Free ℤ C] [Module.Finite ℤ C]
    (N : AddSubgroup (Additive (Character T) × C)) [N.FiniteIndex]
    (hN : ∀ α : Φ, (α.val, (0 : C)) ∈ N) :
    ∃ θ : T ⊗ diagonalizableGroup F C ≅
        diagonalizableGroup F (Additive (Character T) × C),
      (∀ (χ : Additive (Character T)) (c : C),
        θ.hom.hom.hom.left.appTop
            ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra F (Additive (Character T) × C)))).inv
              (AddMonoidAlgebra.single (χ, c) 1)) =
          (fst T.X (diagonalizableGroup F C).X ≫ χ.toMul.hom.hom).left.appTop
              ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1)) *
            (snd T.X (diagonalizableGroup F C).X).left.appTop
              ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra F C))).inv
                (AddMonoidAlgebra.single c 1))) ∧
      ∃ kT : diagonalizableGroup F ((Additive (Character T) × C) ⧸ N) ⟶
          T ⊗ diagonalizableGroup F C,
        kT = diagonalizableGroupMap F (QuotientAddGroup.mk' N) ≫ θ.inv ∧
        IsClosedImmersion kT.hom.hom.left ∧
        IsFinite (diagonalizableGroup F ((Additive (Character T) × C) ⧸ N)).X.hom ∧
        (∀ (R : Type u) [CommRing R] [Algebra F R]
          (k : StandardGroupSchemes.affine F R ⟶
            (diagonalizableGroup F ((Additive (Character T) × C) ⧸ N)).X)
          (g : StandardGroupSchemes.affine F R ⟶ H.X ⊗ (diagonalizableGroup F C).X),
          @Commute (StandardGroupSchemes.affine F R ⟶
            H.X ⊗ (diagonalizableGroup F C).X) _
            (k ≫ (kT ≫ (iT ⊗ₘ 𝟙 (diagonalizableGroup F C))).hom.hom) g) ∧
        ∃ (G S : Grp (Over (Spec (.of F))))
          (q : H ⊗ diagonalizableGroup F C ⟶ G)
          (iS : S ⟶ G) (qT : T ⊗ diagonalizableGroup F C ⟶ S),
          IsFppfGroupQuotient (kT ≫ (iT ⊗ₘ 𝟙 (diagonalizableGroup F C))) q ∧
          Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
          Smooth G.X.hom ∧ ConnectedSpace G.X.left ∧ IsAffine G.X.left ∧
          LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom ∧
          ReductiveTorusCentralizer.IsReductive G ∧
          ReductiveTorusCentralizer.IsMaximalTorus iS ∧
          (∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)) ∧
          (iT ⊗ₘ 𝟙 (diagonalizableGroup F C)) ≫ q = qT ≫ iS ∧
          IsFppfGroupQuotient kT qT ∧
          ∃ (_ : IsCommMonObj S.X) (e : Additive (Character S) ≃+ N)
            (aG : ModObj S.X G.X)
            (Q : RootDatum Φ (Additive (Character S)) (Additive (Cocharacter S))),
            aG.smul = (iS.hom.hom ⊗ₘ 𝟙 G.X) ≫ CategoryTheory.GrpObj.conj G.X ∧
            (∀ χ : Additive (Character S),
              (qT ≫ χ.toMul).hom.hom.left.appTop
                  ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
                    (LaurentPolynomial.T 1)) =
                θ.hom.hom.hom.left.appTop
                  ((Scheme.ΓSpecIso (.of
                    (AddMonoidAlgebra F (Additive (Character T) × C)))).inv
                      (AddMonoidAlgebra.single (e χ).val 1))) ∧
            (∀ χ : Additive (Character S),
              (∃ α : Φ, Q.root α = χ) ↔
                χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ S G aG χ.toMul ≠ ⊥) ∧
            (∀ α : Φ, (e (Q.root α)).val = (α.val, (0 : C))) ∧
            (∀ (χ : Additive (Character S)) (ν : Additive (Cocharacter S)),
              ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
                (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (Q.toLinearMap χ ν)) ∧
            ∀ (α : Φ) (χ : Additive (Character S)),
              Q.toLinearMap χ (Q.coroot α) =
                P.toLinearMap (e χ).val.1 (P.coroot α) := by
  sorry

end AlgebraicGeometry
