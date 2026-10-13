/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # The affine coefficient augmentation is a quasi-isomorphism

Source: Stacks Project, Tags 03P2 and 01EQ. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The fixed coefficient augmentation extends to a quasi-isomorphism from the
lifted ordinary unit Cech complex. No covering or compactness assumption is needed.
Source: Stacks Project, Theorem 59.22.4 (Tag 03P2), separated affine intersections;
Lemma 20.11.2 (Tag 01EQ), the beta augmentation, and Homology Lemma 12.25.4.
(blueprint: lem-pbc-additive-cech-beta-quasi-iso)

Proof: Forget the scalars of the ordinary unit Cech complex and apply ULift.
For every tuple of opens the inverse of restrictFunctorGamma identifies unit
sections with functions on the corresponding open subscheme. These maps commute
with restrictions, including the structural scalar restriction along toSpecGamma.
Since the tuple index sets are finite, forgetting scalars and ULift commute with
these products. Thus this identifies the lifted complex with the Cech complex of
etaleAdditiveSheaf restricted to opens, with exactly the coordinates displayed
in additiveCechBeta. Apply the resolution augmentation into I^0 on every tuple.
Naturality makes these maps commute with the alternating horizontal differential;
the augmentation followed by the vertical differential is zero. Inclusion into
bidegree (n,0) therefore yields a chain map b with the displayed components.
Each tuple intersection is affine by hU (categorical products of opens agree with
their infima). Positive derived evaluation of the additive structure sheaf there
vanishes by affine quasi-coherent acyclicity, while degree zero is evaluation of
the sheaf itself. Products of abelian groups are exact, so every augmented
vertical column is a resolution. The first-quadrant augmentation comparison,
applied after exchanging indices, makes b a quasi-isomorphism. This does not use
exactness of augmented horizontal rows or a covering condition. For degree zero
it is the kernel computation of the resolution. Empty tuple families give zero
complexes; empty intersections have zero sections; repeated opens cause no change.
The component equation determines b uniquely, so no arbitrary existence witness
is used as data in a definition. -/
theorem exists_additiveCech_beta_quasiIso
    (X : Scheme.{u}) [X.IsSeparated] {ι : Type u} [Finite ι]
    (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf) :
    ∃ b : (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
          (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf))) ⟶
        additiveCechTotal U I,
      (∀ (n : ℕ) (x : (cechOver X.toSpecΓ U
        (SheafOfModules.unit X.ringCatSheaf)).X n),
        b.f n (ULift.up x) = additiveCechBeta U I n x) ∧ QuasiIso b := by sorry

end AlgebraicGeometry.Scheme.Modules
