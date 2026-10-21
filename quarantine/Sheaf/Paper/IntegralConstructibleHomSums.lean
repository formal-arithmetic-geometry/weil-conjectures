/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness
import Sheaf.Paper.AdicGlobalDerivedHom
import WeilConjectures.CategoryTheory.DerivedModuleHomologyCoproduct
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel

/-! # Shifted Hom from integral constructible complexes and countable sums

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12
(blueprint: lem-weil-pbc-integral-constructible-hom-sums).

We use the completed coefficient presentation of the integral category. The scalar
ring is its recorded `ULift` of the valuation ring, canonically ring-isomorphic to
that valuation ring. A colimit cofan supplies the ambient derived coproduct and its
coprojections without choosing a second coproduct object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

open Classical in
/-- The canonical map from the direct sum of shifted Hom modules is bijective,
and hence is an isomorphism of modules over the integral coefficient ring.
Its component at `i` is postcomposition with the shifted coprojection `s.inj i`.
The countable family may be empty and its common lower bound may be any integer.
The source belongs to the recorded bounded constructible complete category, using
the canonical continuous-coefficient/completed-coefficient identification.

Source: Bhatt--Scholze, Lemma 6.8.12
(blueprint: lem-weil-pbc-integral-constructible-hom-sums).

Proof:
1. Apply integralConstructible_boundedBelow_compactness with this scheme, coefficient
extension, source and common lower bound. With G = adicGlobalRHom X d K.obj, it
identifies the sum of G(M i) with G(s.pt); its legs are G.map (s.inj i).
2. Apply derivedModuleHomology_coproduct in degree q. Exactness of module direct
sums identifies the source cohomology with the sum of H^q G(M i), including for the
empty family and negative q.
3. The ringedDerived_closed_symmetric_monoidal tensor-Hom adjunction and symmetry
identify internal Hom from K as the right adjoint of tensoring with K.
Apply derived_internalHom_sections_model to identify H^q G(N) with Hom(K,N[q]).
The scalar-valued global sections defining G and the abelian-group-valued sections
in that model have the same underlying complexes on K-injective resolutions.
Naturality for multiplication by each constant scalar makes the identification
linear; naturality on target maps descends through localization to every s.inj i.
4. Conjugate the cohomology comparison by these linear identifications. Its component
on the ith summand sends f to f followed by (s.inj i)[q]. The direct-sum universal
property identifies it with the displayed DirectSum.toModule map. It is bijective
because the three comparison maps are isomorphisms. For the empty family the
ambient coproduct and both Hom modules are zero. -/
theorem integralConstructible_hom_sums
    (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hdim : ∃ N : ℕ, topologicalKrullDim X ≤ (N : WithBot ℕ∞))
    (hℓ : ∀ x : X, IsUnit (ℓ : X.presheaf.stalk x))
    (K : PbcIntegralCategory ℓ E X hdim hℓ)
    (I : Type (u + 1)) [Countable I]
    (M : I → PbcCompletedDerived X (pbcIntegralDatum ℓ E))
    (_hM : ∃ n : ℤ, ∀ i : I, DerivedCategory.IsGE (M i) n)
    (q : ℤ) (s : Cofan M) (_hs : IsColimit s) :
    Function.Bijective
      (DirectSum.toModule (PbcIntegralRing ℓ E) I (K.obj ⟶ s.pt⟦q⟧)
        (fun i : I ↦ Linear.rightComp (PbcIntegralRing ℓ E) K.obj
          ((shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum ℓ E)) q).map
            (s.inj i)))) := by
  sorry

end AlgebraicGeometry.Scheme
