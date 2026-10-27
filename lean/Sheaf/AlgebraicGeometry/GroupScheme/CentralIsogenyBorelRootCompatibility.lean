/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Artinian.Module

/-! # Borel pairs and root pairings under central isogenies

Source: Milne, Algebraic Groups (2017), proof of Proposition 18.18, Corollary 17.84,
Definitions 23.1--23.2, Propositions 23.4--23.5, and the product decomposition in 23.13.
(blueprint: lem-sfb-central-isogeny-borel-root-compatibility)

The two statements give central-isogeny compatibility and the product specialization.
All subgroups, characters, cocharacters, and maps are actual group schemes or morphisms.
Root data and radical projections have the specifications of
`reductive_borel_pair_structure`; no smoothness condition is imposed on the kernel.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A faithfully flat map with finite central scheme-theoretic kernel onto a reductive
algebraic group has reductive source. Every split Borel pair lifts by scheme-theoretic
inverse image; the radicals, torus projections, roots, positive and simple roots, and
all character-coroot pairings are compatible.

Source: Milne, proof of 18.18, 17.84, Definitions 23.1--23.2 and Propositions 23.4--23.5.
(blueprint: lem-sfb-central-isogeny-borel-root-compatibility)

Proof plan:
1. Factor a smooth connected normal unipotent N in H through its faithfully flat
   image I using lem-sfb-affine-homomorphism-flat-image. By
   lem-sfb-unipotent-normal-quotient-image, I is smooth connected normal unipotent
   in G, hence trivial. Thus N lies scheme-theoretically in the finite kernel.
2. Its coordinate algebra is finite dimensional and reduced by
   sbc-lem-smooth-geometrically-reduced. Apply lem-sfb-reduced-artinian-residue-product
   and lem-wf-affine-nullstellensatz-vanishing: it is a finite product of F's.
   The identity makes the product nonempty; connectedness makes it a single F.
   Therefore N is trivial and H is reductive.
3. Choose a maximal torus above T by lem-sfb-quotient-borel-torus-images.
   The kernel centralizes it, so lem-sfb-reductive-torus-self-centralizer puts K
   in it. Lift points faithfully flat locally and descend closed-subgroup
   membership to obtain the scheme-theoretic inverse-image equality.
4. By lem-sfb-split-torus-subgroups-diagonalizable K is diagonalizable. Apply
   lem-sfb-multiplicative-isogeny-borel-comparison to lift B, with faithfully flat
   restriction. Apply lem-sfb-reductive-borel-pair-structure to both pairs.
5. By lem-sfb-isogeny-root-power-laws centrality forces every root exponent to
   be one: root subgroups map isomorphically and coroots push forward to coroots.
   By lem-sfb-borel-root-product-coordinates and the Lie(B) weight criterion,
   positive roots correspond. Nonnegative integral expansions in the two bases
   show that simple roots correspond too.
6. Ordered root-product coordinates identify the map of radicals with the
   product of root-subgroup isomorphisms. For b = ut, its image is q(u)q(t),
   so the two torus projections commute with q.
7. Compose an arbitrary character with corresponding coroots. The resulting
   power maps on G_m agree, hence their integer exponents agree. -/
theorem centralIsogeny_borel_root_compatibility
    {F : Type u} [Field F] [IsAlgClosed F]
    (G H : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hH : SolvableGroupStructure.IsAlgebraic H)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (q : H ⟶ G) (hq : q.hom.hom.left.appTop.hom.FaithfullyFlat)
    (hK : IsFinite (GrpObj.ker q.hom.hom).hom)
    (hcentral : ∀ (A : Over (Spec (.of F)))
      (x : A ⟶ GrpObj.ker q.hom.hom) (g : A ⟶ H.X),
      (x ≫ GrpObj.kerι q.hom.hom) * g = g * (x ≫ GrpObj.kerι q.hom.hom)) :
    ReductiveTorusCentralizer.IsReductive H ∧
    ∀ (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ G) (iB : B ⟶ G),
      ReductiveTorusCentralizer.IsMaximalTorus iT →
      (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r)) →
      IsBorelGroupScheme iB.hom.hom → ∀ j : T ⟶ B, j ≫ iB = iT →
      ∃ (TH BH : Grp (Over (Spec (.of F))))
        (iTH : TH ⟶ H) (iBH : BH ⟶ H) (jH : TH ⟶ BH)
        (qT : TH ⟶ T) (qB : BH ⟶ B)
        (kT : Grp.mk (GrpObj.ker q.hom.hom) ⟶ TH)
        (U UH : Grp (Over (Spec (.of F)))) (iU : U ⟶ B) (iUH : UH ⟶ BH)
        (p : B ⟶ T) (pH : BH ⟶ TH) (qU : UH ⟶ U)
        (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
        (_ : IsCommMonObj T.X)
        (aG : ModObj T.X G.X) (aB : ModObj T.X B.X)
        (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
        (P : RootDatum Φ
          (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T))) (b : P.Base)
        (_ : IsCommMonObj TH.X)
        (aH : ModObj TH.X H.X) (aBH : ModObj TH.X BH.X)
        (ΦH : Finset (Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
        (PH : RootDatum ΦH
          (Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TH))) (bH : PH.Base),
        ReductiveTorusCentralizer.IsMaximalTorus iTH ∧
        (∃ r : ℕ, Nonempty (TH ≅ MultiplicativeType.splitTorus F r)) ∧
        IsBorelGroupScheme iBH.hom.hom ∧ jH ≫ iBH = iTH ∧
        IsPullback iTH.hom.hom qT.hom.hom q.hom.hom iT.hom.hom ∧
        IsPullback iBH.hom.hom qB.hom.hom q.hom.hom iB.hom.hom ∧
        kT.hom.hom ≫ iTH.hom.hom = GrpObj.kerι q.hom.hom ∧
        qT.hom.hom.left.appTop.hom.FaithfullyFlat ∧
        qB.hom.hom.left.appTop.hom.FaithfullyFlat ∧
        IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
        Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ SolvableGroupStructure.IsUnipotent U ∧
        (∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
          IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
          Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
          ∃ f : N ⟶ U, f ≫ iU = iN) ∧
        j ≫ p = 𝟙 T ∧
        IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X] ∧
        IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom)) ∧
        IsClosedSubgroupScheme iUH.hom.hom ∧ IsNormalSubgroupScheme iUH.hom.hom ∧
        Smooth UH.X.hom ∧ ConnectedSpace UH.X.left ∧ SolvableGroupStructure.IsUnipotent UH ∧
        (∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ BH),
          IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
          Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
          ∃ f : N ⟶ UH, f ≫ iUH = iN) ∧
        jH ≫ pH = 𝟙 TH ∧
        IsPullback iUH.hom.hom (toUnit UH.X) pH.hom.hom η[TH.X] ∧
        IsIso ((fst UH.X TH.X ≫ iUH.hom.hom) * (snd UH.X TH.X ≫ jH.hom.hom)) ∧
        IsIso qU ∧ qU ≫ iU = iUH ≫ qB ∧ qB ≫ p = pH ≫ qT ∧
        Module.Finite ℤ (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
        Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)) ∧
        P.IsReduced ∧
        aG.smul = (iT.hom.hom ⊗ₘ 𝟙 G.X) ≫ GrpObj.conj G.X ∧
        aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X ∧
        (∀ α : Φ, P.root α = α.val) ∧
        (∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
          ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
            (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν)) ∧
        (∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T G aG χ.toMul ≠ ⊥) ∧
        (∀ α : Φ,
          b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥) ∧
        Module.Finite ℤ (Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
        Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TH)) ∧
        PH.IsReduced ∧
        aH.smul = (iTH.hom.hom ⊗ₘ 𝟙 H.X) ≫ GrpObj.conj H.X ∧
        aBH.smul = (jH.hom.hom ⊗ₘ 𝟙 BH.X) ≫ GrpObj.conj BH.X ∧
        (∀ α : ΦH, PH.root α = α.val) ∧
        (∀ (χ : Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TH)),
          ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
            (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (PH.toLinearMap χ ν)) ∧
        (∀ χ : Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
          χ ∈ ΦH ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ TH H aH χ.toMul ≠ ⊥) ∧
        (∀ α : ΦH,
          bH.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ TH BH aBH α.val.toMul ≠ ⊥) ∧
        ∃ e : Φ ≃ ΦH,
          (∀ α : Φ, (PH.root (e α)).toMul = qT ≫ (P.root α).toMul) ∧
          (∀ α : Φ, (PH.coroot (e α)).toMul ≫ qT = (P.coroot α).toMul) ∧
          (∀ α : Φ, bH.IsPos (e α) ↔ b.IsPos α) ∧
          (∀ α : Φ, e α ∈ bH.support ↔ α ∈ b.support) ∧
          ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) (α : Φ),
            PH.toLinearMap (Additive.ofMul (qT ≫ χ.toMul)) (PH.coroot (e α)) =
              P.toLinearMap χ (P.coroot α) := by
  sorry

/-- For a product of a split torus with a semisimple group, every split Borel pair
is the product of the torus with a split Borel pair of the semisimple factor. The
roots extend trivially across the torus and the coroots have trivial torus component.
This applies in particular to the lifted pair in `centralIsogeny_borel_root_compatibility`.

Source: Milne, 21.29--21.35, 21.60, 17.86 and proof of 23.13.
(blueprint: lem-sfb-central-isogeny-borel-root-compatibility)

Proof plan (steps 8--9 of the node): the central Z factor centralizes TH, so
lem-sfb-reductive-torus-self-centralizer puts it inside TH and BH. Project to S
and apply lem-sfb-quotient-borel-torus-images. Multiplying a local lift (z,s) by
(z⁻¹,1) and descending closed-subgroup membership proves the product equalities.
Conjugation on Lie(Z) is trivial, so the nonzero weights and the positive weights
are exactly those of S extended trivially across Z. The normalizer is the product
of Z with the normalizer in S. By lem-sfb-reductive-rank-one-reflections its
reflections fix all Z-characters, so the Z-component of each coroot is zero by
perfectness. Compare its S-component with the S-coroot: the product of their
reflections is y ↦ y + φ(y)α with φ(α)=0. Iteration gives y + nφ(y)α.
Finiteness of the Weyl group and torsion freeness imply φ=0, so perfectness
identifies the two coroots. This includes the empty root system. -/
theorem splitTorus_semisimple_borel_root_compatibility
    {F : Type u} [Field F] [IsAlgClosed F]
    (Z S TH BH : Grp (Over (Spec (.of F))))
    (hZ : ∃ r : ℕ, Nonempty (Z ≅ MultiplicativeType.splitTorus F r))
    (hS : IsSemisimpleGroupScheme S.X)
    (iTH : TH ⟶ Z ⊗ S) (iBH : BH ⟶ Z ⊗ S) (jH : TH ⟶ BH)
    (hTH : ReductiveTorusCentralizer.IsMaximalTorus iTH)
    (hTHs : ∃ r : ℕ, Nonempty (TH ≅ MultiplicativeType.splitTorus F r))
    (hBH : @IsBorelGroupScheme F _ _ (Z ⊗ S).X BH.X
      (Z ⊗ S).grp BH.grp iBH.hom.hom) (hjH : jH ≫ iBH = iTH) :
    ∃ (TS BS : Grp (Over (Spec (.of F)))) (iTS : TS ⟶ S) (iBS : BS ⟶ S)
      (jS : TS ⟶ BS) (eT : TH ≅ Z ⊗ TS) (eB : BH ≅ Z ⊗ BS)
      (_ : IsCommMonObj (StandardGroupSchemes.multiplicative F))
        (_ : IsCommMonObj TH.X)
        (aHS : ModObj TH.X (Z ⊗ S).X) (aBH : ModObj TH.X BH.X)
        (ΦH : Finset (Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
        (PH : RootDatum ΦH
          (Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TH))) (bH : PH.Base)
        (_ : IsCommMonObj TS.X)
        (aS : ModObj TS.X S.X) (aBS : ModObj TS.X BS.X)
        (ΦS : Finset (Additive (TS ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
        (PS : RootDatum ΦS
          (Additive (TS ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
          (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TS))) (bS : PS.Base),
      ReductiveTorusCentralizer.IsMaximalTorus iTS ∧
      (∃ r : ℕ, Nonempty (TS ≅ MultiplicativeType.splitTorus F r)) ∧
      IsBorelGroupScheme iBS.hom.hom ∧ jS ≫ iBS = iTS ∧
      eT.hom ≫ (𝟙 Z ⊗ₘ iTS) = iTH ∧ eB.hom ≫ (𝟙 Z ⊗ₘ iBS) = iBH ∧
      Module.Finite ℤ (Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
      Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TH)) ∧
      PH.IsReduced ∧
      aHS.smul = (iTH.hom.hom ⊗ₘ 𝟙 (Z ⊗ S).X) ≫ GrpObj.conj (Z ⊗ S).X ∧
      aBH.smul = (jH.hom.hom ⊗ₘ 𝟙 BH.X) ≫ GrpObj.conj BH.X ∧
      (∀ α : ΦH, PH.root α = α.val) ∧
      (∀ (χ : Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TH)),
        ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
          (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (PH.toLinearMap χ ν)) ∧
      (∀ χ : Additive (TH ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        χ ∈ ΦH ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ TH (Z ⊗ S) aHS χ.toMul ≠ ⊥) ∧
      (∀ α : ΦH,
        bH.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ TH BH aBH α.val.toMul ≠ ⊥) ∧
      Module.Finite ℤ (Additive (TS ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))) ∧
      Module.Finite ℤ (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TS)) ∧
      PS.IsReduced ∧
      aS.smul = (iTS.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X ∧
      aBS.smul = (jS.hom.hom ⊗ₘ 𝟙 BS.X) ≫ GrpObj.conj BS.X ∧
      (∀ α : ΦS, PS.root α = α.val) ∧
      (∀ (χ : Additive (TS ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
        (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ TS)),
        ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
          (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (PS.toLinearMap χ ν)) ∧
      (∀ χ : Additive (TS ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
        χ ∈ ΦS ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ TS S aS χ.toMul ≠ ⊥) ∧
      (∀ α : ΦS,
        bS.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ TS BS aBS α.val.toMul ≠ ⊥) ∧
      ∃ e : ΦS ≃ ΦH,
        (∀ α : ΦS, (PH.root (e α)).toMul =
          eT.hom ≫ snd Z TS ≫ (PS.root α).toMul) ∧
        (∀ α : ΦS, (PH.coroot (e α)).toMul ≫ eT.hom =
          lift (0 : Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ Z)
            (PS.coroot α).toMul) ∧
        (∀ α : ΦS, bH.IsPos (e α) ↔ bS.IsPos α) ∧
        (∀ α : ΦS, e α ∈ bH.support ↔ α ∈ bS.support) := by
  sorry

end AlgebraicGeometry
