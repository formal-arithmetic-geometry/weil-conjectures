/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
import Sheaf.AlgebraicGeometry.GroupScheme.SimpleModuleDualHighestWeight
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Dimension multiplication at a restricted highest weight

Source: Jantzen, Representations of Algebraic Groups, Part II, 3.16--3.17;
Williamson, Algebraic representations and constructible sheaves, Section 1.4,
Theorem 1.3 and equation (1.7), pp.6--7, https://arxiv.org/pdf/1610.06261.
(blueprint: lem-sfb-restricted-highest-weight-dimension-product)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w z
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry.RationalHighestWeight

/-- The dimensions of simple rational modules multiply at a p-restricted first weight.
The root datum is the actual character/cocharacter datum: its pairing is composition
of group-scheme characters and cocharacters, its roots are the nonzero conjugation
weights on Lie(S), and its positive system is the one on Lie(B). Dimensions are natural
numbers, with no reduction to F. No Frobenius map or induced-module identification
is an argument.

Source: Jantzen, Part II, 3.16--3.17; Williamson, Section 1.4, Theorem 1.3 and (1.7).
(blueprint: lem-sfb-restricted-highest-weight-dimension-product)

Proof plan:
1. By lem-sfb-reductive-borel-pair-structure S is reductive. Multiplication by p
   on its free finite-rank character lattice is injective with finite cokernel.
   With identity root correspondence and all root exponents p, apply
   lem-sfb-root-datum-isogeny-realization to obtain a surjective endomorphism f
   with finite kernel and torus pullback p times the identity.
2. Smoothness makes S reduced by sbc-lem-smooth-geometrically-reduced.
   By lem-sfb-algebraic-group-homomorphism-factorization, f is faithfully flat
   onto a closed subgroup. Surjectivity gives full support, and reducedness kills
   its defining ideal. Thus f is faithfully flat onto S.
3. By lem-sfb-isogeny-root-power-laws and reducedness of the root system, f
   preserves every root subgroup with exponent p. By
   lem-sfb-borel-root-product-coordinates, f preserves U, even for no roots.
4. Pull back the coaction of Vmu along the actual coordinate map of f, retaining
   its vector space. The diagonal coaction on Q = Vlam tensor f*Vmu satisfies
   the coaction identities. By lem-sfb-restricted-frobenius-tensor-simplicity,
   Q is simple, using precisely dominance and the p-restriction of lam.
5. Nonzero U-fixed highest vectors v and w have nonzero tensor, as is checked
   by linear forms taking value 1 on each. It is U-fixed since f preserves U;
   its torus character is lam times mu to the pth power. By
   lem-sfb-simple-module-dual-highest-weight, Q has a one-dimensional highest
   line, and uniqueness gives an equivariant linear isomorphism with Vsum.
6. Tensor products of bases give dim Q = dim Vlam times dim Vmu. Pullback
   leaves the vector space unchanged, and the isomorphism preserves dimension.
   This includes zero weights, p=2, and the trivial group (the identity 1=1*1).
-/
theorem restricted_highest_weight_dimension_product
    {F : Type u} [Field F] [IsAlgClosed F] (p : ℕ) [CharP F p] (hp : 0 < p)
    (S T B U : Grp (Over (Spec (.of F))))
    [IsAffine S.X.left] [IsAffine T.X.left] [IsAffine U.X.left]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (iT : T ⟶ S) (iB : B ⟶ S) (j : T ⟶ B) (iU : U ⟶ B)
    (hTB : IsRhoBorelPair iT iB j)
    (hUclosed : IsClosedSubgroupScheme iU.hom.hom)
    (hUnormal : IsNormalSubgroupScheme iU.hom.hom)
    (hUsmooth : Smooth U.X.hom) (hUconnected : ConnectedSpace U.X.left)
    (hUunipotent : SolvableGroupStructure.IsUnipotent U)
    (hUmax : ∀ (N : Grp (Over (Spec (.of F)))) (iN : N ⟶ B),
      IsClosedSubgroupScheme iN.hom.hom → IsNormalSubgroupScheme iN.hom.hom →
      Smooth N.X.hom → ConnectedSpace N.X.left →
      SolvableGroupStructure.IsUnipotent N → ∃ f : N ⟶ U, f ≫ iU = iN)
    [IsCommMonObj T.X] [IsCommMonObj (StandardGroupSchemes.multiplicative F)]
    (aS : ModObj T.X S.X) (aB : ModObj T.X B.X)
    (haS : aS.smul = (iT.hom.hom ⊗ₘ 𝟙 S.X) ≫ GrpObj.conj S.X)
    (haB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
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
    (hΦ : ∀ χ : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)),
      χ ∈ Φ ↔ χ ≠ 0 ∧ @TorusCharacterTangent.weightSpace F _ T S aS χ.toMul ≠ ⊥)
    (hpos : ∀ α : Φ,
      b.IsPos α ↔ @TorusCharacterTangent.weightSpace F _ T B aB α.val.toMul ≠ ⊥)
    (lam mu : Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hlam : ∀ α ∈ b.support, 0 ≤ P.toLinearMap lam (P.coroot α))
    (hmu : ∀ α ∈ b.support, 0 ≤ P.toLinearMap mu (P.coroot α))
    (hrestricted : ∀ α ∈ b.support, P.toLinearMap lam (P.coroot α) < (p : ℤ))
    {Vlam : Type v} [AddCommGroup Vlam] [Module F Vlam] [FiniteDimensional F Vlam]
    {Vmu : Type w} [AddCommGroup Vmu] [Module F Vmu] [FiniteDimensional F Vmu]
    {Vsum : Type z} [AddCommGroup Vsum] [Module F Vsum] [FiniteDimensional F Vsum]
    (clam : Vlam →ₗ[F] Vlam ⊗[F] coordinateAlgebra S)
    (cmu : Vmu →ₗ[F] Vmu ⊗[F] coordinateAlgebra S)
    (csum : Vsum →ₗ[F] Vsum ⊗[F] coordinateAlgebra S)
    (hlamcoassoc : HopfAction.Coassociative F (coordinateAlgebra S) Vlam clam)
    (hlamcounit : HopfAction.Counital F (coordinateAlgebra S) Vlam clam)
    (hmucoassoc : HopfAction.Coassociative F (coordinateAlgebra S) Vmu cmu)
    (hmucounit : HopfAction.Counital F (coordinateAlgebra S) Vmu cmu)
    (hsumcoassoc : HopfAction.Coassociative F (coordinateAlgebra S) Vsum csum)
    (hsumcounit : HopfAction.Counital F (coordinateAlgebra S) Vsum csum)
    (hlamsimple : IsSimple clam) (hmusimple : IsSimple cmu) (hsumsimple : IsSimple csum)
    (hlamweight : HasHighestWeight clam iT (iU ≫ iB) lam.toMul)
    (hmuweight : HasHighestWeight cmu iT (iU ≫ iB) mu.toMul)
    (hsumweight : HasHighestWeight csum iT (iU ≫ iB) (lam + p • mu).toMul) :
    Module.finrank F Vsum = Module.finrank F Vlam * Module.finrank F Vmu := by
  sorry

end AlgebraicGeometry.RationalHighestWeight
