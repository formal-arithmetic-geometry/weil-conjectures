/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
import Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation

/-! # Lifting a perfect stalk chain map

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-open-stalk-chain-map-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- An arbitrary chain map of perfect stalk complexes lifts on an affine neighbourhood.
Source: Stacks Project, Tag 09RE, affine proof's finite-presentation calculation;
Tag 0BC7 (2), chain representatives, and Tag 00CR.
(blueprint: lem-sc-perfect-open-stalk-chain-map-lift).

Proof: Take sections on the affine U. Each finite-free retract gives a finite
projective section module, and the tilde/Gamma adjunction identifies the original
terms with its associated sheaf. Stalks identify these modules with localization
at the prime of x. Sandwich the components of t between the given retract maps;
these become finite matrices of germs. Only degrees in the finite intersection
of the support intervals of P and Q contribute. Represent all entries by sections
on principal opens containing x, and intersect this finite family. Sandwich the
lifted matrices back between the restricted retract maps. Each chain equation
holds on the stalk; after sandwiching into the finite free modules, it is a finite
list of germ equalities. Shrink to principal opens where these equalities hold.
The resulting components form g. Cofinality of neighbourhoods inside V and the
open-immersion stalk-ring isomorphism give the natural isomorphism e for all
complexes, with the displayed equality on g. No inverse or quasi-isomorphism
condition is required. Empty support intersections and zero ranks give zero maps. -/
theorem exists_affine_perfect_open_stalk_chainMap_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (t : ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      ∃ (e : R ⋙ S ≅ T) (g : R.obj P ⟶ R.obj Q),
        S.map g = (e.app P).hom ≫ t ≫ (e.app Q).inv := by sorry

end
end AlgebraicGeometry.Scheme
