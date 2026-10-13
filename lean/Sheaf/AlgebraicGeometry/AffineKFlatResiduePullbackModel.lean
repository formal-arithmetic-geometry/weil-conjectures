/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # An affine K-flat model of the ambient derived residue pullback

Source: Stacks Project, Tags 0BDI and 08DW(2).
(blueprint: lem-sc-affine-kflat-residue-pullback-model).
-/

@[expose] public section

universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A supplied K-flat affine module model computes the ambient derived residue pullback
as an object, before taking any cohomology or dimensions. The scalar field is transported
by the explicitly constructed residue-field isomorphism `e`.

Source: Stacks Project, Tag 0BDI, affine reduction; Tag 08DW(2), affine derived pullback.
(blueprint: lem-sc-affine-kflat-residue-pullback-model).

Proof:
1. Factor `X.fromSpecResidueField z` through the open immersion `U.ι`, since its image
   is the singleton z contained in U. Identify sheaves on the localized site with
   sheaves on U.toScheme using Modules.overEquiv. Then transport along hU.isoSpec.
   These are exact equivalences. Their derived comparisons with Q take the supplied
   hmodel to the termwise associated sheaf of F on Spec A. Derived pullback commutes
   with this open restriction, by Tag 08DW. Use the canonical restriction equivalence,
   rather than an arbitrary equivalence with the same source and target categories.
2. Put p = hU.isoSpec.hom z. The residue maps of U.ι and hU.isoSpec.hom are invertible.
   Compose U.ι's residue map with the inverse of hU.isoSpec.hom's residue map and with
   Spec.residueFieldIso A p. This is precisely e : kappa_X(z) -> kappa(p) written below.
   Naturality of residue points and Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
   identify the factored residue morphism with the affine residue point, after this
   field change. Naturality of germs and residues and Spec.algebraMap_residueFieldIso_inv
   show that e.inv composed with A -> kappa(p) equals evaluation A -> kappa_X(z).
3. Apply the affine derived-pullback formula to F with the identity resolution F -> F;
   hF is its K-flat hypothesis. It gives Q of tilde of the termwise scalar-extension
   complex over kappa(p). The field isomorphism changes that complex into its restriction
   of scalars along e.hom. This scalar restriction is exact, and the tilde/base-change
   comparison commutes with the differentials, so transports Q as well. Compose with
   the open-restriction and model comparisons from step 1 to obtain the displayed iso.

No cohomology, finrank, freeness, boundedness or finite-dimensionality is used here.
For an empty open there is no z. The zero complex and arbitrary unbounded K-flat
complexes are included; all scalar maps are isomorphisms where asserted. -/
theorem affine_kFlat_residuePullback_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (U : X.Opens) (hU : IsAffineOpen U)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (hF : (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.obj (.op U))) (.up ℤ)).kFlat F)
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj F)))
    (z : U) :
    let e := asIso (U.ι.residueFieldMap z) ≪≫
      (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫
        Spec.residueFieldIso (X.presheaf.obj (.op U)) (hU.isoSpec.hom z)
    Nonempty ((derivedPullback (X.fromSpecResidueField z)).obj E ≅
      DerivedCategory.Q.obj
        (((tilde.functor (X.residueField z)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars e.hom.hom).mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.extendScalars
              (algebraMap (X.presheaf.obj (.op U))
                (hU.isoSpec.hom z).asIdeal.ResidueField)).mapHomologicalComplex
                  (.up ℤ)).obj F)))) := by
  sorry

end AlgebraicGeometry.Scheme
