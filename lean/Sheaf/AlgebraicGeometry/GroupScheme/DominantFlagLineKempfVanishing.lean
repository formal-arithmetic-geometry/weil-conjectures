/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.GroupScheme.RhoRegularWeylOrbit
import WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing

/-! # Kempf vanishing for dominant flag line bundles

Source: Milne, Algebraic Groups (2017), Section 22d, Theorems 22.50--22.51,
pp.479--480, with the sign fixed by the quotient action in Section 18c and 22.48.
(blueprint: lem-sfb-dominant-flag-line-kempf-vanishing)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Higher Zariski cohomology vanishes for the associated line of a dominant character.
The presentation is for the character -λ composed with B → T: its quotient action
therefore has fibre multiplier λ(b), exactly as in the node. The character root datum,
positive base and integer pairing are the ones identified with conjugation weights
and character/cocharacter composition, rather than an unrelated abstract root datum.
The projection p and the unipotent radical U are pinned by their kernel square
and the semidirect multiplication isomorphism from the Borel-pair theorem.

Source: Milne, Algebraic Groups (2017), Section 22d, Theorems 22.50--22.51,
pp.479--480, with the sign convention of Section 18c and 22.48.
(blueprint: lem-sfb-dominant-flag-line-kempf-vanishing)

Proof plan:
1. Put M_μ = L_{-μ}. Tensor the trivial lines on S and descend their multiplication
   by lem-pc-fpqc-descent and lem-sfb-homogeneous-line-bundle-sections. This gives
   M_μ tensor M_ν ≅ M_{μ+ν}, M_0 ≅ O_Q, and the corresponding powers and inverses.
2. By lem-sfb-strict-dominant-flag-line-ample the flag is smooth projective and
   geometrically integral. By lem-sfb-rho-regular-weyl-orbit, rho pairs to 1 with
   every simple coroot. Thus M_{λ+ρ} and M_{λ+2ρ} are ample, including rank zero.
3. In characteristic p > 0, lem-trf-proper-field-invertible-coherent makes Q
   Noetherian and M_{-ρ} coherent. Apply lem-weil-pbc-coherent-serre-vanishing
   with ample M_{λ+ρ}. For q = p^r sufficiently large, the higher cohomology of
   M_{qλ+(q-1)ρ} vanishes by the tensor identities of step 1.
4. By lem-sfb-flag-frobenius-rho-pushforward, f = Fr_Q^r is finite and
   f_*M_{(q-1)ρ} ≅ O_Q^{d_r}, where d_r ≥ 1. Transition functions give
   f^*M_λ ≅ M_{qλ}. Apply lem-trf-finite-ideal-twist-cohomology-comparison with
   the unit ideal and exponent 1 to identify the cohomology of M_λ^{d_r}
   with that of M_{qλ+(q-1)ρ}, which is zero by step 3.
5. Inclusion in and projection out of the first summand exhibit M_λ as a retract.
   The cohomology functors of pqf-def-cohomology preserve the composite identity,
   so their value on M_λ is a retract of zero and is zero.
6. In characteristic zero, lem-sfb-flag-canonical-character gives omega_Q ≅ M_{-2ρ}.
   Step 1 identifies omega_Q tensor M_{λ+2ρ} with M_λ. Apply
   lem-sfb-kodaira-vanishing using step 2 and pure dimension |Phi^+|. Its
   dimension-zero case includes empty roots. The two characteristic cases exhaust
   fields. No strict dominance, characteristic restriction or nonempty roots are assumed. -/
theorem dominant_flag_line_kempf_vanishing
    {F : Type u} [Field F] [IsAlgClosed F]
    (S : Grp (Over (Spec (.of F)))) (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B : Grp (Over (Spec (.of F)))) (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B)
    (hTB : IsRhoBorelPair iT iB j)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aS : ModObj T.X S.X) (aB : ModObj T.X B.X)
    (Φ : Finset (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))))
    (P : RootDatum Φ
      (Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)))
    (b : P.Base) [P.IsReduced]
    (hconjS : aS.smul = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (hconjB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (hroot : ∀ α : Φ, P.root α = α.val)
    (hpair : ∀ (χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (ν : Additive (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T)),
      ν.toMul.hom.hom ≫ χ.toMul.hom.hom =
        (𝟙 (StandardGroupSchemes.multiplicative F)) ^ (P.toLinearMap χ ν))
    (hweights : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T S aS χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ, b.IsPos α ↔
      @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (ρ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hρ : 2 • ρ = ∑ α ∈ (@Finset.filter Φ b.IsPos (Classical.decPred _) Finset.univ),
      P.root α)
    (lam : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hlam : ∀ α ∈ b.support, 0 ≤ P.toLinearMap lam (P.coroot α))
    (U : Grp (Over (Spec (.of F)))) (iU : U ⟶ B) (p : B ⟶ T)
    (hUc : IsClosedSubgroupScheme iU.hom.hom)
    (hUn : IsNormalSubgroupScheme iU.hom.hom)
    (hUs : Smooth U.X.hom) (hUconn : ConnectedSpace U.X.left)
    (hUu : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left → SolvableGroupStructure.IsUnipotent N →
      ∃ f : N ⟶ U, f ≫ iU = iN)
    (hp : j ≫ p = 𝟙 T)
    (hker : IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X])
    (hsplit : IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom)))
    (Q : Over (Spec (.of F))) (π : S.X ⟶ Q)
    (hQ : IsProper Q.hom) (hQft : LocallyOfFiniteType Q.hom) (hQqc : QuasiCompact Q.hom)
    (hπf : Flat π.left) (hπs : Surjective π.left)
    (hπi : (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) ≫ π = fst S.X B.X ≫ π)
    (hπt : IsPullback (fst S.X B.X)
      (fst S.X B.X * (snd S.X B.X ≫ iB.hom.hom)) π π)
    (L : AssociatedCharacterLineBundle.Presentation S B iB Q π (p ≫ (-lam).toMul)) :
    ∀ i : ℕ, 0 < i → IsZero ((RingedSpace.moduleCohomology Q.left.toRingedSpace i).obj L.L) := by
  sorry

end AlgebraicGeometry
