/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The cohomology map of a module morphism over the displayed common affine base.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial.
(blueprint: def-pbc-unit-cohomology-pullback-linear)

The map is the adjoint coefficient map after exact inverse image on Ext. The
projection identity identifies the structural scalars; coefficient naturality
therefore proves linearity. No equivalence or witness is chosen. -/
def unitCohomologyPullbackLinear
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (f' : X ⟶ Spec (.of R)) (d : X ⟶ Y)
    (hd : d ≫ f = f') (M : Y.Modules)
    (φ : M ⟶ (pushforward d).obj (SheafOfModules.unit X.ringCatSheaf)) (n : ℕ) :
    HOver f M n →ₗ[R] HOver f' (SheafOfModules.unit X.ringCatSheaf) n :=
  cohomologyComparisonLinear (R := R) (invImage d) (constIso d).symm (coeff d φ)
    ((scalarRep M).comp (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom))
    ((scalarRep (SheafOfModules.unit X.ringCatSheaf)).comp
      (((Scheme.ΓSpecIso (.of R)).inv ≫ f'.appTop).hom)) (fun a ↦ by
        have hs : d.appTop (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom a) =
            ((Scheme.ΓSpecIso (.of R)).inv ≫ f'.appTop).hom a := by
          have he := congrArg Scheme.Hom.appTop hd
          rw [Scheme.Hom.comp_appTop] at he
          exact ConcreteCategory.congr_hom
            (congrArg ((Scheme.ΓSpecIso (.of R)).inv ≫ ·) he) a
        change (invImage d).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map
            (M.smulHom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom a))) ≫
            coeff d φ = coeff d φ ≫
              (SheafOfModules.toSheaf X.ringCatSheaf).map
                ((smulHom (X := X) (SheafOfModules.unit X.ringCatSheaf))
                  (((Scheme.ΓSpecIso (.of R)).inv ≫ f'.appTop).hom a))
        rw [← hs]
        apply coeff_naturality
        rw [pushforward_map_smulHom]
        exact smulHom_naturality φ _) n

/-- Transport through a scheme isomorphism and a specified unit-module isomorphism
is bijective on ordinary cohomology.
Source: Stacks Project, Tag 01F7; `Sheaf.H.mapFunctor_bijective`.
(blueprint: lem-pbc-unit-cohomology-pullback-linear-bijective)

Proof: Inverse image along d is an equivalence of abelian sheaf categories: its
inverse is inverse image along the inverse scheme morphism, with unit and counit
from the inverse-image composition and identity comparisons. Thus it is fully
faithful and preserves injectives, and mapFunctor_bijective applies to its action
on Ext. The adjoint of the structural unit map is an isomorphism because d is an
isomorphism of ringed spaces. Precomposing the structural map by e.hom transports
this adjoint by the forgotten isomorphism e, so coeff d of the displayed composite
is an isomorphism too. Its cohomology map is bijective by functoriality on
isomorphisms. Compose these two bijections. The defined linear map has exactly
this underlying composite. No flatness hypothesis is needed; zero rings, empty
schemes and all nonnegative degrees are included. -/
theorem unitCohomologyPullbackLinear_bijective
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (f' : X ⟶ Spec (.of R)) (d : X ⟶ Y) [IsIso d]
    (hd : d ≫ f = f') (M : Y.Modules) (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (n : ℕ) :
    Function.Bijective (unitCohomologyPullbackLinear f f' d hd M
      (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom) n) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
