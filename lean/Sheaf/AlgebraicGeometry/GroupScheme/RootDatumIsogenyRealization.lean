/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.BorelPairRootDatumNormalization
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
public import Mathlib.Algebra.CharP.Defs
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.GroupScheme.CompatibleRankOneGraphGeometry
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts

/-! # Realization of root-datum isogenies

Source: Milne, Algebraic Groups (2017), Definitions 23.1--23.2, pp.483--484;
Proposition 23.5, pp.485--486; Theorem 23.9, p.487; Theorem 23.25, pp.492--493.
(blueprint: lem-sfb-root-datum-isogeny-realization)

The indices 1 and 0 denote source and target. Characters and cocharacters are the
actual group-scheme Hom groups, written additively, as in the Borel-pair structure
statement. Perfectness identifies cocharacters with the integer dual of characters.
The coroot reflection is required to be induced by a normalizing group element;
thus the input is the root datum of the given group, including its coroots.
The dual-map condition is written pointwise, as restriction of integer functionals.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every isogeny of the actual reduced root data of two split reductive groups
is realized by an isogeny of those groups. Every realization is central exactly
when all root exponents are one, and is invertible exactly when in addition the
character-lattice map is invertible.

Source: Milne, Definitions 23.1--23.2, Proposition 23.5, Theorem 23.9 and
Theorem 23.25, pp.483--493. The geometric coroot normalization is Theorem 21.11(d)--(e).
(blueprint: lem-sfb-root-datum-isogeny-realization)

Proof plan:
1. By lem-sfb-multiplicative-character-antiduality the map u gives the unique
   torus map h. Coset representatives for coker(u) make F[M₁] finite free of
   positive rank over F[M₀]. The faithfully flat spectrum lemma gives surjectivity,
   and the identity fibre has algebra F[coker(u)], hence is finite. The dual
   equation says h composed with each coroot is the corresponding coroot
   composed with the q-th power map.
2. Choose a Borel and regular cocharacter by reductive-borel-pair-structure and
   regular-cocharacter-borel-description. Its image is regular with the same
   positive roots under b. The positive cones correspond, and their extremal
   rays give corresponding simple bases by reducedness. Also b(-α)=-b(α) and
   q(-α)=q(α). For empty roots both groups are tori, so h is the realization.
3. For each simple root use reductive-rank-one-reflections. Antiduality identifies
   the roots trivial on the codimension-one torus with the rational root line;
   reducedness leaves just ±α. The ambient coroot is the rank-one coroot by
   reflection uniqueness. The two given equations then permit
   rank-one-frobenius-extension with the same torus map h for every simple root.
4. Apply compatible-rank-one-graph-geometry to the torus graph and these maps.
   The generated reduced closed group L is reductive, its graph torus is maximal,
   and its first projection identifies full root data. Applying
   root-monomial-kernel-coordinates gives a faithfully flat first projection
   with trivial scheme-theoretic kernel, since all its root exponents are one.
5. Apply faithfully-flat-group-quotient-universal to factor the identity of L
   through that projection. Uniqueness makes the resulting section a two-sided
   inverse j. The second projection composed with j gives g and restricts to h.
   Root-monomial-kernel-coordinates makes g surjective with finite kernel.
6. For any realization use root-monomial-kernel-coordinates. If its kernel K
   is central, reductive-torus-self-centralizer puts K inside the torus. Thus
   K intersects each root group trivially, whereas that intersection has algebra
   F[z]/(z^q). Its basis 1,z,...,z^(q-1) forces q=1, including infinitesimal K.
7. Conversely, if all q=1, the kernel coordinates give K=ker(h). Every root
   character is one on K. Reductive-root-subgroup-parametrizations then makes K
   commute with every root group and the torus, hence with the big cell.
   Bruhat-longest-cell-charts makes G₁ integral. Restriction to its dense big
   cell is injective on functions and remains so after tensoring with F[K].
   Equality of the two conjugation morphisms extends to K × G₁. Thus K is
   central over every algebra, including nonreduced algebras.
8. An isomorphism has trivial, hence central, kernel; step 6 gives q=1.
   The torus kernel algebra F[coker(u)] is then F, so the coset basis gives
   coker(u)=0. Conversely, if q=1 and u is bijective, antiduality makes h
   invertible, the kernel coordinates give K=1, and the quotient universal
   property constructs the two-sided inverse of g. For empty roots every
   torus kernel is central and the same argument gives the isomorphism test.
-/
theorem rootDatum_isogeny_realization
    {F : Type u} [Field F] [IsAlgClosed F] (p : ℕ) [ExpChar F p]
    (G T : Fin 2 → Grp (Over (Spec (.of F))))
    (iT : ∀ i : Fin 2, T i ⟶ G i)
    (hG : ∀ i, ReductiveTorusCentralizer.IsReductive (G i))
    (hT : ∀ i, ReductiveTorusCentralizer.IsMaximalTorus (iT i))
    (hsplit : ∀ i, ∃ r : ℕ, Nonempty (T i ≅ MultiplicativeType.splitTorus F r))
    [∀ i, IsCommMonObj (T i).X]
    [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aG : ∀ i, ModObj (T i).X (G i).X)
    (hconj : ∀ i, (aG i).smul = ((iT i).hom.hom ⊗ₘ 𝟙 (G i).X) ≫ GrpObj.conj (G i).X)
    (Φ : ∀ i, Finset (Additive (RankOneRoots.Character (T i))))
    (D : ∀ i, RootDatum (Φ i)
      (Additive (RankOneRoots.Character (T i))) (Additive (RankOneRoots.Cocharacter (T i))))
    [∀ i, Module.Finite ℤ (Additive (RankOneRoots.Character (T i)))]
    [∀ i, Module.Finite ℤ (Additive (RankOneRoots.Cocharacter (T i)))]
    (hred : ∀ i, (D i).IsReduced)
    (hroot : ∀ i (α : Φ i), (D i).root α = α.val)
    (hpair : ∀ i (χ : Additive (RankOneRoots.Character (T i)))
      (ν : Additive (RankOneRoots.Cocharacter (T i))),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ ((D i).toLinearMap χ ν))
    (hweights : ∀ i (χ : Additive (RankOneRoots.Character (T i))),
      χ ∈ Φ i ↔ χ ≠ 0 ∧
        @TorusCharacterTangent.weightSpace F _ (T i) (G i) (aG i) χ.toMul ≠ ⊥)
    (hcoroot : ∀ i (α : Φ i),
      ∃ (n : 𝟙_ (Over (Spec (.of F))) ⟶ (G i).X) (s : T i ≅ T i),
        (∀ (A : CommAlgCat.{u} F) (t : StandardGroupSchemes.affine F A ⟶ (T i).X),
          t ≫ s.hom.hom.hom ≫ (iT i).hom.hom =
            (toUnit (StandardGroupSchemes.affine F A) ≫ n) * (t ≫ (iT i).hom.hom) *
              (toUnit (StandardGroupSchemes.affine F A) ≫ n)⁻¹) ∧
        ∀ χ : Additive (RankOneRoots.Character (T i)),
          Additive.ofMul (s.hom ≫ χ.toMul) =
            χ - ((D i).toLinearMap χ ((D i).coroot α)) • α.val)
    (u : Additive (RankOneRoots.Character (T 0)) →+
      Additive (RankOneRoots.Character (T 1)))
    (hinj : Function.Injective u) (hfinite : Finite (_ ⧸ u.range))
    (b : Φ 1 ≃ Φ 0) (q : Φ 1 → ℕ)
    (hq : ∀ α, ∃ e : ℕ, q α = p ^ e)
    (hu : ∀ α : Φ 1, u ((D 0).root (b α)) = q α • (D 1).root α)
    (hdual : ∀ (α : Φ 1) (χ : Additive (RankOneRoots.Character (T 0))),
      (D 1).toLinearMap (u χ) ((D 1).coroot α) =
        (q α : ℤ) * (D 0).toLinearMap χ ((D 0).coroot (b α))) :
    (∃ (g : G 1 ⟶ G 0) (gT : T 1 ⟶ T 0),
      Surjective g.hom.hom.left ∧ IsFinite (GrpObj.ker g.hom.hom).hom ∧
      iT 1 ≫ g = gT ≫ iT 0 ∧ Surjective gT.hom.hom.left ∧
      ∀ χ : Additive (RankOneRoots.Character (T 0)),
        Additive.ofMul (gT ≫ χ.toMul) = u χ) ∧
    ∀ (g : G 1 ⟶ G 0) (gT : T 1 ⟶ T 0),
      Surjective g.hom.hom.left → IsFinite (GrpObj.ker g.hom.hom).hom →
      iT 1 ≫ g = gT ≫ iT 0 → Surjective gT.hom.hom.left →
      (∀ χ : Additive (RankOneRoots.Character (T 0)),
        Additive.ofMul (gT ≫ χ.toMul) = u χ) →
      ((∀ (A : Type u) [CommRing A] [Algebra F A]
          (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker g.hom.hom)
          (y : StandardGroupSchemes.affine F A ⟶ (G 1).X),
          (x ≫ GrpObj.kerι g.hom.hom) * y = y * (x ≫ GrpObj.kerι g.hom.hom)) ↔
        ∀ α : Φ 1, q α = 1) ∧
      (IsIso g ↔ (∀ α : Φ 1, q α = 1) ∧ Function.Bijective u) := by
  sorry

end AlgebraicGeometry
