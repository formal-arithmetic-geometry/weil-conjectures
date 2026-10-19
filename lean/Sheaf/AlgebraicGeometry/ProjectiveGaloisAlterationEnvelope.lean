/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import Sheaf.AlgebraicGeometry.ChowProjectiveClosedImmersions
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition
import Sheaf.AlgebraicGeometry.ProjectiveGenericallyFinite
import WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataDomainN2
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# A normal projective Galois envelope of a separable alteration

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, Definition 3.3.1,
printed p.158, and Theorem 3.4, proof Step 4, printed pp.160--161
(blueprint: lem-per-projective-galois-alteration-envelope).

The extension `L` is realized as `W.functionField`. Its algebra structures and its
embedding of `V.functionField` are pinned to the generic stalk maps of `c` and `t`.
The Galois group acts on `W` on the left; its action on functions is pullback by
inverse scheme automorphisms. The torsor clause uses geometric points of the actual
inverse-image open and the restriction of that same action.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Every proper generically finite separable alteration of an excellent integral
Noetherian scheme is dominated by a normal integral excellent Noetherian projective
Galois alteration. Here projective means the EGA projective-bundle convention.
Source: ILO, Expose X, Definition 3.3.1 and Theorem 3.4, Step 4, pp.158,160--161
(blueprint: lem-per-projective-galois-alteration-envelope).

Proof, following the node's steps.
1. Write `E = k(V)`. Chow's lemma over the Noetherian base gives a projective modification of
`V`; replacing it by the reduced closure of the dense open where it is an isomorphism gives an
integral closed subscheme `P` of some `ℙⁿ_S`, with function field `E` and a surjective proper
`S`-map `P → V`.
2. Embed `E` in a finite Galois extension `L/K` and put `G = Aut_K(L)`; the tensor
decomposition of `L ⊗_K L` shows `G` is finite, and Galois correspondence gives `L^G = K`.
3. Let `Y → P` be the normalization of `P` in `L`. Its charts are integral closures of
excellent, hence Nagata and N-2, coordinate domains, so `Y → P` is finite and `k(Y) = L`.
4. Form the fibre products `D = ∏_{g ∈ G, S} P` and `B = ∏_{g ∈ G, S} Y`. Then `B → D` is
finite, and iterated Segre embeddings embed `D` as a closed subscheme of one `ℙᴺ_S`.
5. The generic fibres are `P_K = Spec E` and `Y_K = Spec L`, so `B_K` is the spectrum of
`⊗_{G,K} L`; the multiplication map twisted by the conjugates gives a closed point `b` of
`B_K` with residue field `L`.
6. Let `Z` be the reduced closure of `b` in `B`. It is integral with `Z_K = Spec L`, so
`k(Z) = L`, and `Z → D` is finite.
7. `G` acts on `B` over `S` by permuting factors; this action fixes `b`, restricts to `Z`, and
acts on the generic point by `Spec` of the inverse Galois automorphisms.
8. `D`, `B`, `Z` are of finite type over `S`, hence excellent and Noetherian. The
normalization `W → Z` is finite and surjective, `W` is normal, integral, excellent and
Noetherian, and `k(W) = L`.
9. The finite map `W → D` and the closed embedding `D → ℙᴺ_S` are projective in the
projective-bundle sense; their composite `c : W → S` is projective, hence proper, with closed
image containing the generic point, so it is surjective. The projections give `t : W → V`
over `S`.
10. Each automorphism of `Z` lifts uniquely to `W` by the dominant-lift property of
normalization; uniqueness gives a group action of `G` on `W` over `S` whose generic pullback
is the given Galois action.
11. Over a nonempty affine open of `S`, generic finiteness makes `D`, hence `W`, finite;
spreading out the separable generic extension shrinks it to an open over which `W` is finite
etale.
12. There the torsor map `∐_G W → W ×_S W` is an isomorphism over `K` by the Galois tensor
decomposition; clearing finitely many annihilators of its kernel and cokernel gives a dense
open `U` over which it is an isomorphism, so `c⁻¹U → U` is a finite etale `G`-torsor and `G`
acts simply transitively on every geometric fibre. -/
theorem exists_projective_galois_alteration_envelope
    {S V : Scheme.{u}} [IsIntegral S] [IsNoetherian S] [IsIntegral V]
    (hExcellent : ∀ A : S.affineOpens, IsExcellent Γ(S, A))
    (r : V ⟶ S) [IsProper r] [Surjective r]
    (hFinite : ∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (r ∣_ U))
    [Algebra S.functionField V.functionField]
    (hAlgebra : algebraMap S.functionField V.functionField =
      (r.functionFieldMap r.apply_genericPoint_of_isDominant).hom)
    [FiniteDimensional S.functionField V.functionField]
    [Algebra.IsSeparable S.functionField V.functionField] :
    ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsNoetherian W)
      (c : W ⟶ S) (_ : Surjective c) (t : W ⟶ V),
      IsNormalScheme W ∧ (∀ A : W.affineOpens, IsExcellent Γ(W, A)) ∧
      IsProjectiveBundle c ∧ t ≫ r = c ∧
      ∃ (hc : c (genericPoint W) = genericPoint S)
        (ht : t (genericPoint W) = genericPoint V)
        (_ : Algebra S.functionField W.functionField),
        algebraMap S.functionField W.functionField = (c.functionFieldMap hc).hom ∧
        FiniteDimensional S.functionField W.functionField ∧
        IsGalois S.functionField W.functionField ∧
        IntermediateField.fixedField
          (⊤ : Subgroup (W.functionField ≃ₐ[S.functionField] W.functionField)) = ⊥ ∧
        Finite (W.functionField ≃ₐ[S.functionField] W.functionField) ∧
        ∃ (i : V.functionField →ₐ[S.functionField] W.functionField)
          (a : (W.functionField ≃ₐ[S.functionField] W.functionField) →* Aut W),
          i.toRingHom = (t.functionFieldMap ht).hom ∧
          (∀ g, (a g).hom ≫ c = c) ∧
          (∀ g, ∃ hg : (a g⁻¹).hom (genericPoint W) = genericPoint W,
            ((a g⁻¹).hom.functionFieldMap hg).hom = g.toRingHom) ∧
          ∃ U : S.Opens, Dense (U : Set S) ∧
            IsFinite (c ∣_ U) ∧ Etale (c ∣_ U) ∧ Surjective (c ∣_ U) ∧
            ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
              (x y : Spec (.of Ω) ⟶ (c ⁻¹ᵁ U).toScheme),
              x ≫ (c ∣_ U) = y ≫ (c ∣_ U) →
              ∃! g : W.functionField ≃ₐ[S.functionField] W.functionField,
                x ≫ (c ⁻¹ᵁ U).ι ≫ (a g).hom = y ≫ (c ⁻¹ᵁ U).ι := by
  sorry

end AlgebraicGeometry
