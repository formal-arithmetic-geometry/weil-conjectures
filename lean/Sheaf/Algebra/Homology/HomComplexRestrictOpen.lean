/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Paper.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Hom complexes commute with open restriction

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Section 0A8X.
(blueprint: lem-sc-hom-complex-restrict-open).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory

/-- The ordinary sheaf Hom complex commutes with restriction to an open.
No boundedness or K-injectivity assumption is needed.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Section 0A8X.

Proof: In degree n the Hom complex is the product, over p in Z, of the
internal Homs from L.X p to M.X (p+n). Open restriction preserves products:
products of sheaves of modules are computed sectionwise and restriction is
precomposition with the forgetful functor from the localized site.
For each factor use SheafOfModules.overHomObjIso, which identifies a local
linear map with the same map on the further localized site. The resulting
product isomorphisms commute with pre- and post-composition. Restriction is
additive, so these isomorphisms identify the differential
 d_M f - (-1)^n f d_L with the differential of the restricted Hom complex.
They therefore define a chain isomorphism. This works also for the empty
open, zero complexes and unbounded complexes: no finite-product truncation
or global-section acyclicity assertion is involved.
(blueprint: lem-sc-hom-complex-restrict-open). -/
theorem homComplex_restrict_open (X : RingedSpace.{u}) (U : Opens X)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) :
    Nonempty (
      homComplex (R := X.sheaf.over U)
        (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)
        (((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (homComplex (R := X.sheaf) L M)) := by sorry

end CategoryTheory
