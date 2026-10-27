/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.FiniteFreeScalarCalculusData

import Sheaf.Paper.FiniteFreeScalarTensorCalculus
import Sheaf.Paper.FiniteFreeScalarDerivedTensorModels
import Sheaf.Paper.ConstructibleCoefficientSiteSquare
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite-free derived scalar calculus on the two small sites

The exact scalar and normalized tensor constructions are assembled with constructibility
and the degree-zero Tor tests.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

private theorem scalar_tor_amplitude
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Algebra A B] (r : ℕ) (basis : Module.Basis (Fin r) A B)
    (s : FiniteFreeScalarTensorCalculus J r basis)
    (t : letI := s.extension_limits
      letI := s.extension_colimits
      letI := s.restriction_limits
      letI := s.restriction_colimits
      FiniteScalarDerivedTensorModels
        (finiteScalarExtension J (algebraMap A B)) (Sheaf.restrictScalars J (algebraMap A B))
        s.sheaf_balance) :
    letI := s.extension_limits
    letI := s.extension_colimits
    ∀ (a b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))),
      DerivedCategory.torAmplitudeIn _ a b K →
      DerivedCategory.torAmplitudeIn _ a b
        ((finiteScalarExtension J (algebraMap A B)).mapDerivedCategory.obj K) := by
  let := s.extension_limits
  let := s.extension_colimits
  let := s.restriction_limits
  let := s.restriction_colimits
  intro a b K hK F
  let U := Sheaf.restrictScalars J (algebraMap A B)
  apply U.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
  let e := t.tensor_iso K ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
    whiskerLeftIso K ((U.mapDerivedCategorySingleFunctor 0).app F)
  exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso e.symm (hK (U.obj F))

private theorem scalar_etale_constructible
    (W : Scheme.{u}) [IsNoetherian W]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B] [Algebra A B]
    (r : ℕ) (basis : Module.Basis (Fin r) A B)
    (s : FiniteFreeScalarTensorCalculus W.smallEtaleTopology r basis) :
    letI := s.extension_limits
    letI := s.extension_colimits
    ∀ K : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Etale.DerivedCategory.isBoundedConstructible A W K →
      Etale.DerivedCategory.isBoundedConstructible B W
        ((finiteScalarExtension W.smallEtaleTopology (algebraMap A B)).mapDerivedCategory.obj
          K) := by
  let := s.extension_limits
  let := s.extension_colimits
  let E := finiteScalarExtension W.smallEtaleTopology (algebraMap A B)
  intro K hK
  refine ⟨fun q ↦ ?_, ?_⟩
  · have hc := (constructibleCoefficientSheaf W A B (algebraMap A B)
        ((DerivedCategory.homologyFunctor _ q).obj K) (hK.1 q)).1
    have : Scheme.IsConstructibleSheaf
        (FA := fun M N : ModuleCat.{u + 1} B ↦ M →ₗ[B] N)
        (CA := fun M : ModuleCat.{u + 1} B ↦ M)
        ((DerivedCategory.homologyFunctor _ q ⋙ E).obj K) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso
        (FA := fun M N : ModuleCat.{u + 1} B ↦ M →ₗ[B] N)
        (CA := fun M : ModuleCat.{u + 1} B ↦ M)
        ((E.mapDerivedCategoryHomologyFunctorIso q).app K))
  · obtain ⟨a, b, hab, hz⟩ := hK.2
    exact ⟨a, b, hab, fun q hq ↦ E.isZero_homologyFunctor_mapDerivedCategory_obj (hz q hq)⟩

private theorem scalar_proetale_constructible
    (W : Scheme.{u}) [IsNoetherian W]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B] [Algebra A B]
    (r : ℕ) (basis : Module.Basis (Fin r) A B)
    (s : FiniteFreeScalarTensorCalculus W.smallEtaleTopology r basis)
    (p : FiniteFreeScalarTensorCalculus (Scheme.ProEt.topology W) r basis) :
    letI := s.extension_limits
    letI := s.extension_colimits
    letI := p.extension_limits
    letI := p.extension_colimits
    ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)),
      ((Etale.DerivedCategory.isBoundedConstructible A W).map
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategory) K →
      ((Etale.DerivedCategory.isBoundedConstructible B W).map
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) W).mapDerivedCategory)
        ((finiteScalarExtension (Scheme.ProEt.topology W) (algebraMap A B)).mapDerivedCategory.obj
          K) := by
  let := s.extension_limits
  let := s.extension_colimits
  let := p.extension_limits
  let := p.extension_colimits
  let EA := finiteScalarExtension W.smallEtaleTopology (algebraMap A B)
  let EP := finiteScalarExtension (Scheme.ProEt.topology W) (algebraMap A B)
  let NA := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) W
  let NB := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) W
  have : PreservesFiniteLimits (EA ⋙ NB) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (EA ⋙ NB) := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits (NA ⋙ EP) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (NA ⋙ EP) := comp_preservesFiniteColimits _ _
  let e₀ : EA ⋙ NB ≅ NA ⋙ EP :=
    ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso (algebraMap A B) W
  let e : EA.mapDerivedCategory ⋙ NB.mapDerivedCategory ≅
      NA.mapDerivedCategory ⋙ EP.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso EA NB).symm ≪≫
      Functor.mapDerivedCategoryNatIso e₀ ≪≫
      Functor.mapDerivedCategoryCompIso NA EP
  rintro K ⟨L, hL, ⟨i⟩⟩
  exact ⟨EA.mapDerivedCategory.obj L, scalar_etale_constructible W A B r basis s L hL,
    ⟨e.app L ≪≫ EP.mapDerivedCategory.mapIso i⟩⟩

/-- Finite-free scalar calculus holds on both small sites, with the ordinary unbounded
module derived categories and the finite-coefficient pro-etale realization.
Source: blueprint main-20261015, finite-free-extension proof, paragraphs 1-2;
Stacks 03CZ, 05V4, 06YS, 06YY, 06YU, 0G7E, 05RT and 03EL
(blueprint: lem-sf-finite-free-derived-scalar-calculus).
Proof: (1) Sheafify the basis and coordinate maps, identifying UE(M) with a finite
sum of M. Restriction keeps the underlying abelian sheaf, so it is exact and reflects
isomorphisms. Finite sums are exact, hence E is exact, including rank zero.
(2) Exact descent (lem-sf-exact-functor-derived-triangulated) gives D(E), D(U) and their
canonical termwise factorizations. K-flat resolutions (lem-pc-kflat-resolution) and
lem-pur-derived-change-of-rings identify D(E) with T by the universal
counit. Localize the basis maps; the j-th inclusion is the scalar unit followed by b_j.
(3) The scalar unit and counit satisfy the triangle identities on local generators.
lem-sfb-adjunction-localization descends these very maps to D(E) adjoint to D(U).
(4) Homology commutes with exact restriction. The unbounded cohomology criterion for
isomorphisms and sectionwise conservativity imply both derived reflection assertions.
(5) lem-pur-kflat-change-of-rings-all-independent gives K-flat EP, without termwise-flat
hypotheses; lem-weil-pbc-ringed-pullback-preserves-kflat also handles flat terms.
(6) Tensor cancellation, exact E and exact U imply that a K-flat B-complex restricts
to a K-flat A-complex. For flat-term models it also preserves termwise flatness.
(7) Use lem-pur-change-of-rings-tensor-cancellation-independent on each homogeneous
summand with the two displayed balancing maps. Their
composites are identities by balancedness; they commute with the total differential
because b has degree zero. Restriction commutes with the total sums. Descend through
the two K-flat localizations; naturality and the universal property give precisely
tensor_normalized, independently of representatives.
(8) lem-sp-constructible-coefficient-site-square preserves finite constant local values;
the B-action is the constant matrix of multiplication in the chosen basis. Exact
homology preserves cohomological bounds. Comparison and coefficient extension commute,
so this also preserves every finite-coefficient pro-etale realization, including the
empty scheme (use one empty stratum with zero module).
(9) Test the tensor comparison with an arbitrary degree-zero B-module sheaf F.
Its restriction is degree zero. The assumed Tor interval kills the A-side cohomology;
exact restriction reflects vanishing and gives the same interval on the B-side. -/
theorem finiteFreeDerivedScalarCalculus (W : Scheme.{u}) [IsNoetherian W]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B] [Algebra A B]
    (r : ℕ) (basis : Module.Basis (Fin r) A B) :
    Nonempty (FiniteFreeScalarCalculus.{u} W.smallEtaleTopology r basis
      (Etale.DerivedCategory.isBoundedConstructible A W)
      (Etale.DerivedCategory.isBoundedConstructible B W)) ∧
    Nonempty (FiniteFreeScalarCalculus.{u} (Scheme.ProEt.topology W) r basis
      ((Etale.DerivedCategory.isBoundedConstructible A W).map
        (Functor.mapDerivedCategory.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2}
          (ProEtale.comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} A) W)))
      ((Etale.DerivedCategory.isBoundedConstructible B W).map
        (Functor.mapDerivedCategory.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2}
          (ProEtale.comparisonUpperStar.{u + 2, u} (ModuleCat.{u + 1} B) W)))) := by
  obtain ⟨s⟩ := finiteFreeScalarTensorCalculus W.smallEtaleTopology r basis
  obtain ⟨p⟩ := finiteFreeScalarTensorCalculus (Scheme.ProEt.topology W) r basis
  obtain ⟨t⟩ := finiteFreeScalarDerivedTensorModels W.smallEtaleTopology r basis s
  obtain ⟨v⟩ := finiteFreeScalarDerivedTensorModels (Scheme.ProEt.topology W) r basis p
  exact ⟨⟨{ toFiniteFreeScalarTensorCalculus := s
            derived_tensor := t
            bounded_constructible := scalar_etale_constructible W A B r basis s
            tor_amplitude := scalar_tor_amplitude W.smallEtaleTopology r basis s t }⟩,
    ⟨{ toFiniteFreeScalarTensorCalculus := p
       derived_tensor := v
       bounded_constructible := scalar_proetale_constructible W A B r basis s p
       tor_amplitude := scalar_tor_amplitude (Scheme.ProEt.topology W) r basis p v }⟩⟩

end AlgebraicGeometry
