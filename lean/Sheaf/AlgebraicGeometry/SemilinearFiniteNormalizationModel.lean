module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Localization.Integral

/-! # Semilinear action on a finite normalization model

Source: Stacks Project, Morphisms, Tags 035H, 035I, 035L and 0AVK;
Varieties, Tag 0GK4, with the equivariant integral-closure-chart expansion.
(blueprint: lem-sfb-semilinear-finite-normalization-model).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A compatible semilinear action extends uniquely to the finite normalization model.
The canonical generic map is the `toNormalization` map of `Spec M ⟶ S`.
`IsPullback` identifies its generic fibre with `Spec M`, including both projections.
The residue-field isomorphism at the image of the unique point identifies the function field
with `M`. No faithfulness, separability, scalar-fixing or projective linearization is assumed.

Source: Stacks Project, Morphisms, Tags 035H, 035I, 035L and 0AVK;
Varieties, Tag 0GK4 (blueprint: lem-sfb-semilinear-finite-normalization-model).

Proof plan:
1. Projectivity makes the structure map proper and separated, and finite type makes `S`
   quasi-compact and quasi-separated (lem-pc-projective-proper, def-weil-proper-morphism,
   lem-weil-pbc-qcqs-over-affine). Apply
   lem-weil-pbc-normalization-in-residue-field-extension at the generic point. Its relative
   normalization is `S.normalizationIn M`; the canonical generic map identifies its generic
   point and function field, and it has integrally closed domain stalks.
2. By lem-fin-normalization-extension-finite the normalization map is finite. Its closed
   image contains the generic point, so it is surjective
   (lem-weil-pbc-finite-closed-map-finite-fibres).
3. A field is Noetherian. Apply lem-fin-finite-over-projective over the affine base `Spec k`
   to obtain the finite projective-space embedding. Finiteness gives properness and finite
   type, and composition gives finite type over `k` (lem-weil-pbc-finite-proper,
   def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change).
4. On a nonempty affine `Spec A`, let `C` be its integral closure in `M` and invert all
   nonzero elements of `A`. Integral closure commutes with localization
   (lem-weil-pbc-integral-closure-commutes-localization). The resulting integral closure of
   `K` in `M` is `M`, since `M/K` is finite. Thus `C ⊗[A] K = M`. Reduce the fibre product
   through this affine open and apply lem-weil-pbc-fibre-product-affine-spectra; its
   projections are the canonical generic map and the field inclusion.
5. Put `t_j = Spec (σ_j⁻¹)`. The field compatibility gives `f t_j = h_j f`. The twisted
   target map `h_j⁻¹ u` is integral. Apply lem-sbc-relative-normalization-universal-property
   to the factorization through `η_B t_j` to obtain the unique lift `a_j`, with both
   required squares (def-weil-finite-integral-morphism).
6. Uniqueness in that universal property identifies the identity lift and the composite
   lifts: `a_1 = 1`, `a_i a_j = a_(ij)`. Inverse elements yield inverse morphisms, giving
   an action by automorphisms, including when the actions have kernels.
7. Any other action has the same componentwise squares, hence equals this one by
   uniqueness. Composing its equivariance square with the structure map and using the
   given scalar square proves compatibility with the specified action on `k`.
-/
theorem semilinear_finite_normalization_model
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (p : S ⟶ Spec (.of k)) [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]
    (M : Type u) [Field M] [Algebra S.functionField M] [Module.Finite S.functionField M]
    (J : Type v) [Group J] [Finite J]
    (σk : J →* (k ≃+* k)) (h : J →* Aut S)
    (hscalar : ∀ j : J, (h j).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (σk j⁻¹).toRingHom))
    (σ : J →* (M ≃+* M))
    (hgeneric : ∀ (j : J) (z : S.functionField),
      σ j (algebraMap S.functionField M z) =
        algebraMap S.functionField M ((Scheme.functionFieldAut (h j⁻¹)).hom z)) :
    IsIntegral (S.normalizationIn M) ∧
      (∀ b : S.normalizationIn M,
        IsDomain ((S.normalizationIn M).presheaf.stalk b) ∧
          IsIntegrallyClosed ((S.normalizationIn M).presheaf.stalk b)) ∧
      IsHProjective (S.fromNormalizationIn M ≫ p) ∧
      LocallyOfFiniteType (S.fromNormalizationIn M ≫ p) ∧
      QuasiCompact (S.fromNormalizationIn M ≫ p) ∧
      IsFinite (S.fromNormalizationIn M) ∧ Surjective (S.fromNormalizationIn M) ∧
      (∃ ξ : S.normalizationIn M, IsGenericPoint ξ Set.univ ∧
        (S.fromSpecOfAlgebraFunctionField M).toNormalization (IsLocalRing.closedPoint M) = ξ ∧
        IsIso ((S.fromSpecOfAlgebraFunctionField M).toNormalization.residueFieldMap
          (IsLocalRing.closedPoint M))) ∧
      IsPullback (S.fromSpecOfAlgebraFunctionField M).toNormalization
        (Spec.map (CommRingCat.ofHom (algebraMap S.functionField M)))
        (S.fromNormalizationIn M) S.fromSpecFunctionField ∧
      ∃! a : J →* Aut (S.normalizationIn M), ∀ j : J,
        (a j).hom ≫ S.fromNormalizationIn M = S.fromNormalizationIn M ≫ (h j).hom ∧
        (S.fromSpecOfAlgebraFunctionField M).toNormalization ≫ (a j).hom =
          Spec.map (CommRingCat.ofHom (σ j⁻¹).toRingHom) ≫
            (S.fromSpecOfAlgebraFunctionField M).toNormalization ∧
        (a j).hom ≫ S.fromNormalizationIn M ≫ p =
          (S.fromNormalizationIn M ≫ p) ≫
            Spec.map (CommRingCat.ofHom (σk j⁻¹).toRingHom) := by
  sorry

end AlgebraicGeometry
