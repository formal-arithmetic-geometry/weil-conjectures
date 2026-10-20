/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor


import Sheaf.AlgebraicGeometry.ProEtaleAffineLinePullbackLift

/-!
# Endomorphism rigidity for an affine-line pullback

Source: Stacks Project, Tag 0A3H, lemma-sections-upstairs, final connected-fibre argument;
Tag 099Y, lemma-compare-locally-constant
(blueprint: lem-pur-a1-pullback-endomorphism-rigidity).

The coefficient category is modules over the constant ring sheaf. All inverse images are
ordinary fixed-coefficient inverse images, with their published canonical composition maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical identification `p^* ⋙ e^* ≅ id`, where `p` is the affine-line projection
and `e` is the section with coordinate one. It is the inverse composition comparison,
followed by the equality `e ≫ p = id` and the identity-pullback comparison.
Source: Stacks Project, Tag 00YV, functoriality of fixed-ring inverse images
(blueprint: lem-pur-a1-pullback-endomorphism-rigidity). -/
noncomputable def proEtaleAffineLineUnitPullbackIso (S : Scheme.{u})
    (Λ : Type u) [CommRing Λ] [Finite Λ] :
    sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) ⋙
      sfIntrinsicPullback Λ
        (AffineSpace.homOfVector (𝟙 S) (fun _ : ULift.{u} (Fin 1) ↦ 1)) ≅ 𝟭 _ :=
  (sfIntrinsicPullbackComp Λ
    (AffineSpace.homOfVector (𝟙 S) (fun _ : ULift.{u} (Fin 1) ↦ 1))
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).symm ≪≫
    eqToIso (congrArg (sfIntrinsicPullback Λ)
      (AffineSpace.homOfVector_over (𝟙 S) (fun _ : ULift.{u} (Fin 1) ↦ 1))) ≪≫
    sfIntrinsicPullbackId Λ S

/-- An endomorphism of an affine-line pullback of a finite locally constant module sheaf
is the identity if its restriction at coordinate one is the identity. The normalization
is written after the canonical identification `e^*p^*M ≅ M`.
No separatedness, finite-type, quasi-compactness or reducedness of `S` is assumed.
Source: Stacks Project, Tags 0A3H and 099Y
(blueprint: lem-pur-a1-pullback-endomorphism-rigidity).

Proof plan:
1. Use lem-pe-constant-left-module-inverse-image: the constant-ring comparison and the
structure map of def-weil-proetale-inverse-image both fix constant scalar sections.
Sheafification makes them equal, so the tensor-product module inverse image is the
fixed-coefficient inverse image, compatibly with units and composition.
2. By lem-sf-proetale-locally-constant-origin choose a finite lisse etale sheaf G whose
comparison pullback is M. The ordinary unit is invertible by
prop-weil-pbc-site-comparison-finite-level, so comparison pullback is fully faithful.
3. By lem-weil-pbc-comparison-pullback transport h to an endomorphism a of p_et^*G.
Identity and composite coherence transports the normalization to e_et^*a = id_G.
4. Every geometric fibre of the affine-line projection is Spec of a polynomial ring
over an algebraically closed field (def-sbc-affine-space). This ring is a domain by
lem-weil-pbc-polynomial-ring-domain. Its zero prime has dense closure by
lem-weil-pbc-spec-irreducible-closed-subsets-primes, so the fibre is connected.
5. For every etale V over S, use lem-weil-pbc-etale-base-change-finite-limits,
lem-weil-pbc-sets-etale-inverse-image-restriction and
lem-weil-pbc-sets-etale-inverse-image-composition-units to identify sections on V and
on A1_V. By lem-weil-pbc-etale-connected-fibres-section-compatible the two pullbacks
of any upstairs section to A1_V times_V A1_V agree. Restrict along (id, e_V p_V):
the section equals p_V^*e_V^* of itself. Conversely e_V^*p_V^* is the identity.
6. Thus the unit G -> p_et,*p_et^*G is a bijection on every etale object. These are
linear maps, so their inverses are linear and natural. The unit is a module isomorphism
(def-weil-pbc-inverse-image, def-weil-pbc-direct-image).
7. Set b = eta_G^(-1) p_et,*(a) eta_G. Naturality of the adjunction unit shows that
a and p_et^*b have the same adjoint, hence agree. The unit-compatible section comparison
of lem-pe-constant-left-module-inverse-image gives b = e_et^*a = id_G.
8. Transport a = id back through the fully faithful comparison and the chosen isomorphism
to obtain h = id. The empty base is included: its section maps and sheaf maps are unique. -/
theorem proEtale_a1_pullback_endomorphism_rigidity (S : Scheme.{u})
    (Λ : Type u) [CommRing Λ] [Finite Λ]
    (M : proEtaleRingModules S (proEtaleConstantRing S Λ))
    (hM : IsLocallyConstantProEtaleModuleSheaf S Λ M)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
      Finite ((finiteCoefficientModuleStalkFunctor y Λ).obj M))
    (h : (sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M ⟶
      (sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M)
    (he : (sfIntrinsicPullback Λ
        (AffineSpace.homOfVector (𝟙 S) (fun _ : ULift.{u} (Fin 1) ↦ 1))).map h ≫
      (proEtaleAffineLineUnitPullbackIso S Λ).hom.app M =
        (proEtaleAffineLineUnitPullbackIso S Λ).hom.app M) :
    h = 𝟙 ((sfIntrinsicPullback Λ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M) := by
  obtain ⟨b, hb⟩ := proEtale_a1_pullback_lift S Λ M hM hfinite h
  have he' := he
  rw [← hb] at he'
  -- The section is a left inverse to the affine-line projection.
  have hn := (proEtaleAffineLineUnitPullbackIso S Λ).hom.naturality b
  have hb' : b = 𝟙 M := by
    apply (cancel_epi ((proEtaleAffineLineUnitPullbackIso S Λ).hom.app M)).1
    exact (hn.symm.trans he').trans (Category.comp_id _).symm
  rw [← hb, hb']
  exact CategoryTheory.Functor.map_id _ _

end AlgebraicGeometry.Scheme
