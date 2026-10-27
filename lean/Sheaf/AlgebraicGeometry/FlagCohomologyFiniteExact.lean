/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.RhoSectionModules
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.HomogeneousVectorBundle
public import Sheaf.AlgebraicGeometry.RationalCharacterFiltration
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientAffineCell
import WeilConjectures.AlgebraicGeometry.Descent
import Sheaf.AlgebraicGeometry.FpqcTensorSections
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections

/-! # Finite rational flag cohomology and character filtrations

Source: Andersen, The strong linkage principle (1980), pp.55--58;
Milne, Algebraic Groups (2017), Sections 18c and 22.29--22.30, Theorem 22.48;
Stacks Tags 02O6 and 02UZ.
(blueprint: lem-sfb-flag-cohomology-finite-exact)

## Main statements

- `flag_cohomology_finite_exact`: existence, finiteness, exactness and character filtrations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct MonObj
namespace AlgebraicGeometry
open EquivariantCoherent RationalHighestWeight RationalCharacterFiltration
open HomogeneousVectorBundle Scheme.Modules

/-- The homogeneous vector bundles exist; their actual Zariski cohomology has
finite-dimensional rational coactions, vanishes above the number of positive roots,
and has the canonical equivariant long exact sequence. Character filtrations exist,
their quotients are weights, and every simple cohomology constituent occurs in the
cohomology of a character quotient of every such filtration. In degree zero,
cohomology is the actual inverse-semi-invariant regular-function subspace.

Source: Andersen, pp.55--58; Milne, Sections 18c and 22.29--22.30, 22.48;
Stacks Tags 02O6 and 02UZ.
(blueprint: lem-sfb-flag-cohomology-finite-exact)

Proof plan:
1. Apply lem-sfb-reductive-borel-pair-structure to the opposite Borel. Its quotient
   is proper of finite type and its projection is a faithfully flat right torsor.
   Lemma lem-sfb-borel-quotient-affine-cell supplies regular Noetherian geometry;
   lem-sfb-flag-canonical-character gives dimension equal to the root count.
2. Descend O_S tensor M along that fpqc torsor by lem-pc-fpqc-descent. The descent
   relation is (g,m)b=(gb,b inverse m). Cocycle and identity follow from the module
   laws. Finite local freeness descends. Section descent
   lem-sc-etale-qcoherent-descent-fpqc-sections gives exactly f(gb)=b inverse f(g).
   The Noetherian source is quasi-compact over every affine open, using
   lem-wf-affine-noetherian-components and lem-sfb-noetherian-space-compact-subsets.
3. Glue the free local vector bundles (lem-weil-pbc-glue-schemes). Descend left
   multiplication, which commutes with the right Borel action, on the quotient
   and sheaves. The quotient represents the fppf quotient, so Yoneda gives its
   base action and all action identities. The inverse action gives the displayed
   normalization on cohomology. Finite locally free sheaves are coherent on the
   Noetherian quotient (pqf-lem-coherent-ft-locnoeth).
4. Pull a representation short exact sequence to S, where it splits F-linearly.
   Flat pullback is exact (lem-weil-pbc-flat-module-pullback-exact-pushforward-injective).
   Faithfully flat local stalk maps reflect zero homology, by
   lem-pc-local-flat-faithful-flat-reflects-surjective, lem-sc-faithfully-flat-tensor-zero
   and pqf-lem-sheaf-zero-stalks. Apply lem-sfb-linearized-qcoherent-cohomology-coaction
   to obtain the normalized coactions and equivariance including connecting maps.
5. Proper coherent cohomology is finite (lem-pc-coherent-hi, Stacks 02O6).
   Lemma lem-sc-noetherian-cohomology-above-dimension (02UZ) gives vanishing above N.
6. Embed the opposite Borel in an upper triangular group by
   lem-sfb-lie-kolchin-triangular-embedding. For a nonzero module,
   lem-sfb-triangular-group-representation-eigenline gives a stable line.
   Its character is trivial on the unipotent radical by
   lem-sfb-unipotent-to-multiplicative-trivial. Induct on dimension of the quotient
   and take inverse images. For any character filtration, decompose a lift of a
   quotient vector into torus weight components using
   lem-sfb-split-torus-representation-weight-decomposition; its character component
   has nonzero image. Thus every quotient character is a weight of M.
7. In the exact triple H^i(M_prev) to H^i(M) to H^i(character), let A be the
   incoming image. For a simple subquotient P/R, the image of P intersect A is
   either zero or all. In the latter case it is a subquotient of H^i(M_prev);
   in the former it is a subquotient of H^i(character). Induct on filtration length.
8. Lemma lem-sfb-homogeneous-line-bundle-sections identifies H^0 of a character
   with the actual regular semi-invariants, with left translation f(s inverse g).
   The displayed coordinate map is pullback through the fixed trivialization.
   Negative degrees are zero by HomogeneousVectorBundle.cohomology. The zero
   module and the empty-root case are included in all preceding steps. -/
theorem flag_cohomology_finite_exact {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (S : Grp (Over (Spec (.of F)))) [IsAffine S.X.left]
    (hS : IsSemisimpleGroupScheme S.X)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : StandardGroupSchemes.affine F A ⟶ GrpObj.ker f)
        (s : StandardGroupSchemes.affine F A ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    (T B Bm : Grp (Over (Spec (.of F)))) [IsAffine T.X.left] [IsAffine Bm.X.left]
    (iT : T ⟶ S) (iB : B ⟶ S) (im : Bm ⟶ S) (j : T ⟶ B) (jm : T ⟶ Bm)
    (hpair : IsRhoBorelPair iT iB j) (hpairm : IsRhoBorelPair iT im jm)
    (aB : ModObj T.X B.X) (am : ModObj T.X Bm.X)
    (hB : aB.smul = (j.hom.hom ⊗ₘ 𝟙 B.X) ≫ GrpObj.conj B.X)
    (hm : am.smul = (jm.hom.hom ⊗ₘ 𝟙 Bm.X) ≫ GrpObj.conj Bm.X)
    (Φ : Finset (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
    (hΦ : ∀ χ, χ ∈ Φ ↔ χ.hom.hom ≠ 1 ∧
      @TorusCharacterTangent.weightSpace F _ T B aB χ ≠ ⊥)
    (hopposite : ∀ χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
      χ.hom.hom ≠ 1 → (@TorusCharacterTangent.weightSpace F _ T Bm am χ ≠ ⊥ ↔
        ∃ α ∈ Φ, χ.hom.hom = α.hom.hom⁻¹)) :
    ∃ (Q : Over (Spec (.of F))) (π : S.X ⟶ Q),
      IsProper Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
      Flat π.left ∧ Surjective π.left ∧
      IsPullback (fst S.X Bm.X)
        (fst S.X Bm.X * (snd S.X Bm.X ≫ im.hom.hom)) π π ∧
      topologicalKrullDim Q.left = (Φ.card : WithBot ℕ∞) ∧
      ∃ D : HomogeneousVectorBundle.System S Bm im Q π,
      (∀ M : Representation F Bm.X,
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (D.L M) (Module.finrank F M.space)) ∧
      ∃ c : ∀ (M : Representation F Bm.X) (i : ℕ),
        HOver Q.hom (D.L M) i →ₗ[F]
          HOver Q.hom (D.L M) i ⊗[F] coordinateAlgebra S,
      (∀ (M : Representation F Bm.X) (i : ℕ),
        HopfAction.Counital F (coordinateAlgebra S) (HOver Q.hom (D.L M) i) (c M i) ∧
        HopfAction.Coassociative F (coordinateAlgebra S) (HOver Q.hom (D.L M) i) (c M i) ∧
        IsNaturalCoaction D M i (c M i) ∧
        Module.Finite F (HOver Q.hom (D.L M) i) ∧
        (Φ.card < i → Subsingleton (HOver Q.hom (D.L M) i))) ∧
      (∀ (M N : Representation F Bm.X) (f : M.space →ₗ[F] N.space)
        (hf : IsRepresentationMap M N f) (i : ℕ),
        ∃ l : HOver Q.hom (D.L M) i →ₗ[F] HOver Q.hom (D.L N) i,
          (∀ v, l v = H.map (D.map M N f hf) i v) ∧
          l.rTensor (coordinateAlgebra S) ∘ₗ c M i = c N i ∘ₗ l) ∧
      (∀ (M₁ M₂ M₃ : Representation F Bm.X)
        (f : M₁.space →ₗ[F] M₂.space) (g : M₂.space →ₗ[F] M₃.space)
        (hf : IsRepresentationMap M₁ M₂ f) (hg : IsRepresentationMap M₂ M₃ g),
        Function.Injective f → Function.Exact f g → Function.Surjective g →
        ∃ hzero : D.map M₁ M₂ f hf ≫ D.map M₂ M₃ g hg = 0,
        ∃ hE : (ShortComplex.mk (D.map M₁ M₂ f hf) (D.map M₂ M₃ g hg) hzero).ShortExact,
          Function.Injective (H.map (D.map M₁ M₂ f hf) 0) ∧
          ∀ i : ℕ, ∃ δ : HOver Q.hom (D.L M₃) i →ₗ[F] HOver Q.hom (D.L M₁) (i + 1),
            (∀ v, δ v = H.δ hE i v) ∧
            δ.rTensor (coordinateAlgebra S) ∘ₗ c M₃ i = c M₁ (i + 1) ∘ₗ δ ∧
            Function.Exact (H.map (D.map M₁ M₂ f hf) i)
              (H.map (D.map M₂ M₃ g hg) i) ∧
            Function.Exact (H.map (D.map M₂ M₃ g hg) i) δ ∧
            Function.Exact δ (H.map (D.map M₁ M₂ f hf) (i + 1))) ∧
      (∀ M : Representation F Bm.X, Nonempty (RationalCharacterFiltration.Filtration M)) ∧
      (∀ (M : Representation F Bm.X) (K : RationalCharacterFiltration.Filtration M),
        (∀ j : Fin K.length,
          (∀ (U : Grp (Over (Spec (.of F)))) (l : U ⟶ Bm),
            IsClosedSubgroupScheme l.hom.hom → IsNormalSubgroupScheme l.hom.hom →
            Smooth U.X.hom → ConnectedSpace U.X.left → SolvableGroupStructure.IsUnipotent U →
              l.hom.hom ≫ (K.character j).hom.hom = 1) ∧
          ∃ v : M.space, v ≠ 0 ∧
          (coordinateMap jm).toLinearMap.lTensor M.space (M.coaction v) =
            v ⊗ₜ[F] characterElement (jm ≫ K.character j)) ∧
        ∀ (i : ℕ) (V : Representation F S.X), IsSimple V.coaction →
          IsSubquotient V.coaction (c M i) → ∃ j : Fin K.length,
            IsSubquotient V.coaction (c (characterModule (K.character j)) i)) ∧
      ∀ χ : Bm ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
        ∃ ψ : Bm ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
          ψ.hom.hom = χ.hom.hom⁻¹ ∧
          ∃ e : HOver Q.hom (D.L (characterModule χ)) 0 ≃ₗ[F]
            RhoSection.sectionModule S Bm im ψ 1,
            (∀ v, (e v).val =
              (TensorProduct.AlgebraTensorModule.rid F
                (RhoSection.Coordinate S.X) (RhoSection.Coordinate S.X)).toLinearMap
                (D.coordinate (characterModule χ) S.X (𝟙 S.X)
                  (AssociatedCharacterLineBundle.pullTopSection π.left
                    (D.L (characterModule χ)) (H.zeroLinearEquiv _ v)))) ∧
            ((RhoSection.sectionModule S Bm im ψ 1).subtype ∘ₗ e.toLinearMap).rTensor
                (coordinateAlgebra S) ∘ₗ c (characterModule χ) 0 =
              regularLeftCoaction S ∘ₗ
                (RhoSection.sectionModule S Bm im ψ 1).subtype ∘ₗ e.toLinearMap ∧
            RhoSection.HasRationalLeftTranslation S (RhoSection.sectionModule S Bm im ψ 1) := by
  sorry

end AlgebraicGeometry
