/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.Paper.OrientedConstructibleSheafVanishing
public import Sheaf.TraceFormula.OrientedPointCohomology

/-!
# Reading constructible strata through the canonical geometric inverse image

Source: ILO XI §§1.1, 1.7, 1.9; Stacks 03CY; Lu--Zheng, definition after
Theorem 4.27 (blueprint: lem-trf-constructible-vanishing-canonical-strata).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.OrientedNearbyCycles CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedConstructibleSheaf

/-- A finite locally constant normalized stratum restriction has finite constant
trivializations for the canonical geometric module pullback.
The hypothesis on `r` specifies its set inverse image by the concrete triple-site
base-change functor; it imposes no condition on the module being restricted.

Source: ILO XI §§1.1, 1.7, 1.9; Stacks 03CY; Lu--Zheng, definition following
Theorem 4.27 (blueprint: lem-trf-constructible-vanishing-canonical-strata).

Proof: normalize pullback along the identity on S by its first projection, an isomorphism.
The composite of this normalization with stratum base change identifies with the functor
in the hypothesis on r: on the first component use base-change associativity for i,f,
and on the second component use the identity-pullback projection followed by base change
along j. These identifications respect all three generating covering types. Thus the
two sheaf inverse images agree, by uniqueness of the left adjoint to precomposition.
The scalar-restriction equivalence for constant ring modules carries this agreement
to the module inverse images: both actions restrict to the same constant scalar action,
and extensions of that action along the sheafification unit are unique. This identifies
the fixed-ring sheaf of r*F with the fixed-ring sheaf of the normalized stratum restriction.
Apply the local-constancy witness to the terminal triple. Pull the resulting isomorphisms
through scalar restriction and through the slice functor. A constant module sheaf on a
slice restricts to the constant fixed-ring module sheaf with the same value; this follows
from the constant-sheaf adjunction and the same scalar equivalence. Finally a finite-type
module over the finite coefficient ring has finite underlying set. Keep the original
covering sieve and its models. This works also for empty strata and the zero ring: the
same adjunction and finite-generation arguments apply, without choosing a point.
-/
theorem canonical_stratum_trivializations {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (i : X' ⟶ X) (j : S' ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (r : Morphism (vanishingDatum.{u, u + 1} f)
        (OrientedPointCohomology.datum.{u, u} (i ≫ f) j))
    (hr : Nonempty (r.inverse ≅
        sheafToPresheaf (vanishingTopology.{u, u + 1} f) (Type (u + 1)) ⋙
          (Comma.map
            ((Functor.rightUnitor ((etaleBaseChange i).prod (etaleBaseChange j)) ≪≫
              (Functor.leftUnitor ((etaleBaseChange i).prod (etaleBaseChange j))).symm).hom)
            (show (etaleBaseChange.{u, u + 1} f).prod' (𝟭 (EtaleSite S)) ⋙
                (etaleBaseChange i).prod (etaleBaseChange j) ⟶
              𝟭 (EtaleSite S) ⋙
                (etaleBaseChange (i ≫ f)).prod' (etaleBaseChange j) from
              { app := fun V ↦ ((etaleBaseChangeComp i f).inv.app V, 𝟙 _)
                naturality := fun V W h ↦
                  Prod.ext ((etaleBaseChangeComp i f).inv.naturality h) (by simp) })).op.lan ⋙
          presheafToSheaf (OrientedPointCohomology.datum.{u, u} (i ≫ f) j).topology
            (Type (u + 1))))
    (F : (vanishingDatum.{u, u + 1} f).modules (Coeff.{u, u + 1} Λ))
    (hF : SheafOfModules.IsFiniteTypeLocallyConstant
      (productTopology (i ≫ f) (j ≫ 𝟙 S)) (Coeff Λ)
      ((stratumRestriction f (𝟙 S) i j Λ).obj ((vanishingModuleTransport f Λ).obj F))) :
    letI : HasFiniteLimits (OrientedPointCohomology.datum.{u, u} (i ≫ f) j).objects :=
      OrientedPointCohomology.triples_finiteLimits (i ≫ f) j
    ∃ R : (OrientedPointCohomology.datum.{u, u} (i ≫ f) j).topology.Cover
      (⊤_ (OrientedPointCohomology.datum.{u, u} (i ≫ f) j).objects),
    ∀ (Z : (OrientedPointCohomology.datum.{u, u} (i ≫ f) j).objects)
      (k : Z ⟶ ⊤_ (OrientedPointCohomology.datum.{u, u} (i ≫ f) j).objects), R k →
      ∃ M : ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ), Finite M ∧
        Nonempty
          (((constantRingModuleRestriction _ (Coeff Λ)).obj
            ((SheafOfModules.restrictScalars (realizationRingIso _ (Coeff Λ)).inv).obj
              ((r.modulePull (Coeff Λ)).obj F))).over Z ≅
            (constantSheaf
              ((OrientedPointCohomology.datum.{u, u} (i ≫ f) j).topology.over Z)
              (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ))).obj M) := by
  sorry

end AlgebraicGeometry.OrientedConstructibleSheaf
