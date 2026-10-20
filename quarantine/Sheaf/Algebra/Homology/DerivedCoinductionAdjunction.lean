/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Derived coinduction and its evaluation counit

Source: Stacks Project, dualizing.tex, Tags 0A70 and 0A71
(blueprint: lem-trf-derived-coinduction-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u wR wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

variable {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wB} (ModuleCat.{u} B)]

/-- Ordinary coinduction on unbounded complexes: degree n is Hom_R(B,Iⁿ), with
(b • h)(b') = h(b'b), and differential postcomposition with d_I.
Source: Stacks 0A70 and 0A71 (blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def coinductionComplexFunctor :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  (coextendScalars f).mapHomologicalComplex (.up ℤ)

/-- Evaluation h ↦ h(1), degreewise as a map of R-module complexes. Its data is the
ordinary restriction/coextension counit, applied to complexes.
Source: Stacks 0A70 (blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def coinductionEvaluation (I : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      ((coinductionComplexFunctor f).obj I) ⟶ I :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  ((restrictCoextendScalarsAdj.{u, u, u} f).mapHomologicalComplex (.up ℤ)).counit.app I

/-- The total right derived functor of ordinary coinduction. The existing K-injective
localization construction fixes its data, rather than choosing a right adjoint from existence.
Source: Stacks 0A70 (blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def derivedCoinduction :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  (coextendScalars f).rightDerivedFunctor

/-- The canonical comparison with every K-injective representative, obtained by inverting
its derived-functor unit. Source: Stacks 0A71
(blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def derivedCoinductionModel
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] :
    (derivedCoinduction f).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((coinductionComplexFunctor f).obj I) :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  (coextendScalars f).rightDerivedFunctorObjQIso I

/-- Ordinary RHom_R(B[0],-): derive the R-module-valued functor Hom_R(B,-).
The composite coextendScalars ⋙ restrictScalars has exactly the linear-map carrier,
R-action and postcomposition maps of this Hom functor; its B-action has been forgotten.
Thus this is the ordinary-module specialization of def-pur-derived-internal-hom,
using the existing total right derived construction on K-injectives.
Source: Stacks 0A71 (blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def derivedCoinductionUnderlyingHom :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  (coextendScalars f ⋙ restrictScalars f).rightDerivedFunctor

/-- The canonical Hom_R(B[0],I) comparison for the underlying ordinary RHom.
Source: Stacks 0A71 (blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def derivedCoinductionUnderlyingModel
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] :
    (derivedCoinductionUnderlyingHom f).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        ((coinductionComplexFunctor f).obj I)) :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  (coextendScalars f ⋙ restrictScalars f).rightDerivedFunctorObjQIso I

/-- The actual restriction/coinduction adjunction on unbounded derived categories, obtained
by deriving the ordinary evaluation-at-one adjunction with exact left adjoint.
Source: Stacks 0A70 (blueprint: lem-trf-derived-coinduction-adjunction). -/
noncomputable def derivedCoinductionAdjunction :
    (restrictScalars f).mapDerivedCategory ⊣ derivedCoinduction f :=
  letI := (restrictCoextendScalarsAdj.{u, u, u} f).right_adjoint_additive
  (restrictCoextendScalarsAdj.{u, u, u} f).mapDerivedCategoryRightDerivedAdjunction

/-- Derived coinduction is independent of the K-injective representative, is right adjoint
to restriction, has underlying R-object RHom_R(B[0],K), and has evaluation-at-one counit.
Restriction is conservative. There are no boundedness or flatness hypotheses.
The underlying comparison is characterized on every K-injective, and the model comparisons
are natural for all maps between K-injectives (in particular every quasi-isomorphism).
Source: Stacks 0A70, 0A71 and 05RT
(blueprint: lem-trf-derived-coinduction-adjunction).

Proof:
1. K-injective replacements exist by prop-pur-kinjective-resolutions-exist, specialized to
ordinary modules. The total right derived construction uses these replacements. By
lem-pur-rhom-well-defined, comparison quasi-isomorphisms between K-injectives are homotopy
equivalences and induce quasi-isomorphisms of Hom_R(B,-). Naturality of the derived unit
therefore gives the displayed naturality of derivedCoinductionModel, independently of all
choices of representative and replacement.
2. The ordinary coextendScalars action is (b • h)(b') = h(b'b); it commutes with the Hom
complex differential. Forgetting it gives Hom_R(B[0],I). Exact restriction commutes with
localization, so the two K-injective comparisons give the natural underlying-RHom
isomorphism characterized by the first equality (def-pur-derived-internal-hom).
3. Derive the ordinary restriction/coextension adjunction with its exact left adjoint.
Equivalently, lem-trf-algebraic-shriek-derived-hom-adjunction gives evaluation at one on
Hom complexes, with inverse g ↦ (x ↦ (b ↦ g(bx))). Taking H⁰ and applying
lem-pur-rhom-global-sections gives the derived Hom-set adjunction. This is the canonical
adjunction explicitly constructed in derivedCoinductionAdjunction.
4. The ordinary adjunction counit is h ↦ h(1) in each degree. The derived adjunction,
computed on a K-injective I, gives the second equality by the derived counit factorization.
5. Restriction is exact and leaves kernels, images, and cohomology unchanged as underlying
modules. It reflects module isomorphisms. The criterion
lem-weil-pbc-unbounded-derived-iso-cohomology (DerivedCategory.isIso_iff) therefore proves
that derived restriction reflects isomorphisms. -/
theorem derivedCoinductionAdjunction_spec :
    ∃ e : derivedCoinduction f ⋙ (restrictScalars f).mapDerivedCategory ≅
        derivedCoinductionUnderlyingHom f,
      (∀ (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective],
        e.hom.app (DerivedCategory.Q.obj I) ≫ (derivedCoinductionUnderlyingModel f I).hom =
          (restrictScalars f).mapDerivedCategory.map (derivedCoinductionModel f I).hom ≫
            (restrictScalars f).mapDerivedCategoryFactors.hom.app
              ((coinductionComplexFunctor f).obj I)) ∧
      (∀ (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective],
        (derivedCoinductionAdjunction f).counit.app (DerivedCategory.Q.obj I) =
          (restrictScalars f).mapDerivedCategory.map (derivedCoinductionModel f I).hom ≫
            (restrictScalars f).mapDerivedCategoryFactors.hom.app
              ((coinductionComplexFunctor f).obj I) ≫
            DerivedCategory.Q.map (coinductionEvaluation f I)) ∧
      (∀ (I J : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] [J.IsKInjective]
          (t : I ⟶ J),
        (derivedCoinduction f).map (DerivedCategory.Q.map t) ≫
            (derivedCoinductionModel f J).hom =
          (derivedCoinductionModel f I).hom ≫
            DerivedCategory.Q.map ((coinductionComplexFunctor f).map t)) ∧
      (restrictScalars f).mapDerivedCategory.ReflectsIsomorphisms := by
  sorry

end ModuleCat
