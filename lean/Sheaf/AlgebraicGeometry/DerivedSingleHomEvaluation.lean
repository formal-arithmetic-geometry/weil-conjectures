/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Derived single-source Hom evaluation

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
-/

@[expose] public section
universe u wY
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry
/-- A natural unit-Hom identification descends to the derived category together
with K-injective comparisons compatible with every map out of the unit.

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95;
the localization calculation in lem-sc-affine-hom-kinjective-evaluation, step 1.
(blueprint: lem-sc-derived-single-hom-evaluation).

Proof:
1. Write I0 for the functorial K-injective replacement and eta for its augmentation.
   Use derivedInternalHom_comparison for this replacement. Fixing its first
   variable at O_Y[0], compose it with e on I0 and the inverse of Q(eta).
   This gives a natural isomorphism after precomposition by Q. Fully faithful
   precomposition by Q descends it to j on the derived category.
2. For a K-injective complex I, eta_I is a quasi-isomorphism between K-injectives.
   Hence Hom(B[0], eta_I) is a quasi-isomorphism by quasiIso_homComplex_map.
   Compose Q of this map with the inverse of the comparison at (B[0], I) to
   obtain c from the unresolved Hom complex to derived internal Hom.
3. Naturality of the comparison in the first variable moves precomposition by
   k[0] across it. The comparison at O_Y[0] cancels against its inverse in j.
   Naturality of the Hom-complex bifunctor moves eta across precomposition by k.
   Finally naturality of e moves eta across evaluation, and Q(eta) cancels
   with its inverse. The resulting composite is Q of precomposition by k[0]
   followed by e_I, as asserted. No finiteness or boundedness hypothesis is used;
   the zero map k, zero B, zero ring and empty scheme obey the same identities. -/
theorem derived_single_hom_evaluation (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) :
    ∃ j : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
      ∀ (B : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (k : SheafOfModules.unit Y.ringCatSheaf ⟶ B)
        (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (_ : I.IsKInjective),
      ∃ c : DerivedCategory.Q.obj
          (homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B) I) ≅
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
            (op ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B),
              DerivedCategory.Q.obj I),
        c.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y)
            Y.toRingedSpace.sheaf).map
          (((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op,
            𝟙 (DerivedCategory.Q.obj I)) ≫
          j.hom.app (DerivedCategory.Q.obj I) =
            DerivedCategory.Q.map
              (((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
                (((CochainComplex.singleFunctor
                  (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op)).app I ≫
                    e.hom.app I) := by sorry

end AlgebraicGeometry
