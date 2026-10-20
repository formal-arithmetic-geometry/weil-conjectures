/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import Sheaf.Algebra.Homology.ModuleCohomologyBaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.AlgebraicGeometry.AffineResidueScalarTransport
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Canonical base change through an affine stalk

Source: Stacks Project, Tags 01HV (7), 06YB, 064L and 0A1U.
(blueprint: lem-sc-affine-model-stalk-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Affine localization preserves K-flatness and the surjectivity of canonical fibre arrows.
Source: Stacks Project, Tags 01HV (7), 06YB, 064L and 0A1U.
(blueprint: lem-sc-affine-model-stalk-base-change).

Proof: Put A = Gamma(X,U), p = hU.isoSpec(z), and S = O_X,z. The associated-sheaf
stalk of M is naturally S tensor_A M, degree by degree: the associated-sheaf germ
is localization at p, and the chart and open-immersion stalk maps identify its
local ring with S. These maps commute with every module morphism, so they give
an isomorphism of complexes. Localization is exact. Tensor associativity identifies
N tensor_S (S tensor_A M) with N tensor_A M for every S-module complex N;
restriction of scalars preserves acyclicity, so K-flatness of M proves K-flatness
of this stalk complex. The residue-field isomorphism from the open immersion,
the chart and Spec.residueFieldIso identifies kappa(S) with kappa(p), compatibly
with A acting by section evaluation. Flat localization commutes with homology.
Use these natural homology and scalar-extension isomorphisms at the two ends of
the cohomology base-change arrow. Its defining extension-restriction adjunction
unit sends a cycle class c to the class of 1 tensor c. Tensor associativity and
the residue-field comparison preserve this formula, so the resulting square of
base-change arrows commutes. Its vertical maps are isomorphisms, hence either
horizontal arrow is epi exactly when the other is. No finiteness, boundedness,
perfection, derived model or fibre-surjectivity assumption is needed. Zero modules
and acyclic complexes obey the same comparisons; the empty open has no z. -/
theorem affine_model_stalk_baseChange (X : Scheme.{u})
    (U : X.Opens) (hU : IsAffineOpen U) (z : U.toScheme)
    (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (hM : (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.obj (.op U))) (.up ℤ)).kFlat M) :
    let L := ((Scheme.affinePerfectSheafification X U hU).mapHomologicalComplex
      (.up ℤ)).obj M
    let C := ((openModuleStalkFunctor X U z).mapHomologicalComplex (.up ℤ)).obj L
    (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.stalk (U.ι z))) (.up ℤ)).kFlat C ∧
    (Epi (ModuleCat.cohomologyBaseChange
      (B := (hU.isoSpec.hom z).asIdeal.ResidueField) M 0) ↔
      Epi (ModuleCat.cohomologyBaseChange
        (B := IsLocalRing.ResidueField (X.presheaf.stalk (U.ι z))) C 0)) := by
  sorry

end AlgebraicGeometry
