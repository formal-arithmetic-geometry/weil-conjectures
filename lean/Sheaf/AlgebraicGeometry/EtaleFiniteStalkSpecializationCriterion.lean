/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.EtaleModuleStalkSpecialization
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.GeometricStalkComparisonConstant
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.GeometricSpecializationStrictLocalLift
import Sheaf.AlgebraicGeometry.StrictHenselization

/-! # Finite stalks and specialization imply finite local constancy

Source: Stacks Project, Tag 0GKC, lemma-characterize-locally-constant-module, (2) implies (1)
(blueprint: lem-weil-pbc-etale-finite-stalk-specialization-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A module sheaf over a finite commutative ring on a Noetherian scheme is finite locally
constant if its geometric stalks are finite sets and all strict-localization specialization
maps are bijective. The conclusion gives the finite module and trivialization on every
member of a jointly surjective étale cover, using restriction to the localized site.
Source: Stacks Project, Tag 0GKC, lemma-characterize-locally-constant-module, (2) implies (1)
(blueprint: lem-weil-pbc-etale-finite-stalk-specialization-criterion).

Proof:
1. Fix a geometric point and its finite stalk M. Represent all elements on one affine
pointed étale neighbourhood. Filtered-colimit equality and the finiteness of M and Λ let
one refine until zero, addition and scalar multiplication relations hold there. The
constant-sheaf adjunction gives a map from the constant M sheaf, bijective at this stalk
(`def-weil-pbc-geometric-stalks`, `def-constructible-constant`,
`lem-weil-pbc-filtered-colimit-modules-elementwise`,
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`,
`lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`,
`lem-weil-pbc-inverse-image-stalk-germ`, `lem-weil-pbc-constant-sheaf-geometric-stalk`).
2. Pull back pointed neighbourhoods along a scheme morphism and refine them affinely.
The compatible limit projections induce the strict-localization comparison. Computing
both maps on section germs shows that specialization commutes with pullback, using
`def-weil-pbc-strict-henselization-limit`, `def-weil-pbc-inverse-image` and
`def-weil-pbc-strict-henselization-structural-map`.
3. On germs, specialization is natural in the sheaf; for a constant sheaf it preserves
the constant label, so it is the identity under the constant-stalk identifications.
4. The locus where the map from constant M is bijective is independent of the geometric
point chosen over each ordinary point (`lem-weil-pbc-geometric-stalk-comparison-constant`).
Lift generalizations to the strict localization using
`lem-weil-pbc-geometric-specialization-strict-local-lift`. Steps 2 and 3 and the hypothesis
show that this locus is stable under both specialization and generalization.
5. The affine étale neighbourhood is Noetherian: étale implies locally finitely presented,
hence locally of finite type, so it is locally Noetherian over S and is quasi-compact.
It has finitely many irreducible components. Remove those not through the chosen point.
Sobriety gives generic points for the remaining components, so stability in both
directions makes the bijectivity locus contain the resulting open neighbourhood
(`def-weil-etale-morphism`, `def-sbc-locally-finite-presentation`, `pqf-lem-locnoeth-lft`,
`lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-noetherian-finitely-many-components`,
`lem-weil-pbc-scheme-sober`).
6. Stalkwise bijectivity gives an isomorphism of the underlying set sheaves
(`lem-weil-pbc-sets-etale-iso-on-geometric-stalks`). Injectivity makes its inverse linear,
and naturality makes the inverse commute with restriction. Repeat at every point to
obtain the covering and finite modules. For the empty scheme use the empty cover. -/
theorem finiteLocallyConstant_of_finite_stalks_of_bijective_specialization
    {S : Scheme.{u}} [IsNoetherian S]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Finite (↑((pointSmallEtale s).sheafFiber.obj G) : Type (u + 1)))
    (hsp : ∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
      (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s),
      Function.Bijective (etaleModuleStalkSpecialization s t G)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage S, ∀ i : 𝒰.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf (S.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
