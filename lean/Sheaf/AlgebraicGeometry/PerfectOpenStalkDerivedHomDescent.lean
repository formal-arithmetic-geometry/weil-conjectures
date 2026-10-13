/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso

/-! # Descent of derived morphisms between open perfect stalks

Source: Stacks Project, Tags 09RE (affine proof), 0BC7 (2), 00CR, and 06Z0.
(blueprint: lem-sc-perfect-open-stalk-derived-hom-descent).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A derived morphism between the open stalks of two strictly perfect complexes descends
as a derived morphism on a smaller affine open. This does not choose a chain representative
and does not involve a comparison with any global complex.

Source: Stacks Project, Tag 09RE affine proof; Tag 0BC7 (2), with Tags 00CR and 06Z0.
(blueprint: lem-sc-perfect-open-stalk-derived-hom-descent).

Proof: On U, finite-free retracts are quasi-coherent. Global sections identify P and Q
with bounded complexes of finite projective modules over A = Gamma(X,U). The stalk at x
is scalar extension to A localized at the prime corresponding to x. Present this ring
as the filtered colimit of A_f for f outside that prime (00CR). The affine perfect Hom
comparison is surjective by 09RE, affine proof, or 0BC7 (2). Thus the given arrow is
represented in the derived category of A_f for one f. The basic open D(f) is affine,
contains x, and lies in U. The affine derived equivalence (06Z0) carries this arrow to g
between the restrictions of P and Q. Restriction does not change the stalk at x, giving
cP and cQ. Naturality of scalar extension and the localization factorization identifies
the derived stalk image of g with the transported original arrow, giving the equation.
Only Hom surjectivity is used; neither inverse descent nor Hom injectivity is needed.
The assumptions exclude an empty U, while zero complexes and zero ranks are allowed:
their Hom groups are zero and the zero arrow descends on U itself. -/
theorem exists_affine_perfect_open_stalk_derived_hom_descent
    (X : Scheme.{u})
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    :
    let SU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X U ⟨x, hxU⟩
    letI : SU.PreservesZeroMorphisms :=
      AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X U ⟨x, hxU⟩
    ∀ t : DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((SU.mapHomologicalComplex (.up ℤ)).obj Q),
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      letI : S.Additive :=
        AlgebraicGeometry.openModuleStalkFunctor_additive X V ⟨x, hxV⟩
      letI : PreservesFiniteLimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteLimits X V ⟨x, hxV⟩
      letI : PreservesFiniteColimits S :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesFiniteColimits X V ⟨x, hxV⟩
      ∃ (cP : DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj (T.obj P)) ≅
          DerivedCategory.Q.obj
            ((SU.mapHomologicalComplex (.up ℤ)).obj P))
        (cQ : DerivedCategory.Q.obj ((S.mapHomologicalComplex (.up ℤ)).obj (T.obj Q)) ≅
          DerivedCategory.Q.obj
            ((SU.mapHomologicalComplex (.up ℤ)).obj Q))
        (g : DerivedCategory.Q.obj (T.obj P) ⟶ DerivedCategory.Q.obj (T.obj Q)),
        (S.mapDerivedCategoryFactors.app (T.obj P)).inv ≫
          S.mapDerivedCategory.map g ≫ (S.mapDerivedCategoryFactors.app (T.obj Q)).hom =
            cP.hom ≫ t ≫ cQ.inv := by sorry

end AlgebraicGeometry.Scheme
