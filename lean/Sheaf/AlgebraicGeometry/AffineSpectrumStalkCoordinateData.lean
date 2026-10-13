/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology

/-! # Stalk coordinates for affine spectrum replacement

Source: Stacks Project, Tags 0098 and 0096.
(blueprint: lem-pc-affine-spectrum-stalk-coordinate-data).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Compatible ring and input-complex coordinates under affine spectrum replacement.

Proof: For each affine scheme Y, the inverse affine-spectrum isomorphism
induces an invertible stalk map. For D use this map at z0. For A use the
stalk map of X.isoSpec.inv at (Spec.map g'.appTop) z0, after identifying its
image with g'(X'.isoSpec.inv z0) by isoSpec_inv_naturality. For B use the
stalk map of S'.isoSpec.inv at (Spec.map f'.appTop) z0, and for R use the
stalk map of S.isoSpec.inv at the image under the two spectrum maps. Point
congruence isomorphisms identify their source stalks with the stated rings.
Naturality of stalkMap under composition proves compatibility with the R-to-A
and R-to-B homomorphisms, including the point congruence in rightAlgebra.
The two projection maps to D likewise commute with their spectrum versions.
The defining restrictions of tensorMap then give its displayed formula on
a tensor b: it is the product of the two projection images, and the ring
isomorphism preserves multiplication.
For q use tensorPullbackRestrictIso along X.isoSpec.inv, followed by the
restriction-stalk comparison in each degree. Represent a ring element and a
module element by germs on a common neighborhood. The restriction comparison
preserves these germs, and germ_smul proves semilinearity for eA. Thus the
additive stalk comparison lifts to a map into restriction of scalars along eA.
Its inverse uses the inverse stalk maps and inverse restriction comparison.
Naturality of the restriction-stalk comparison for every differential of P
proves the chain-map equations, yielding the stated complex isomorphism.
This construction needs no flatness, boundedness or nonzero-ring hypothesis;
the zero complex has the same maps, and an empty spectrum has no z0.
Source: Stacks Project, Tag 0098, lemma-stalk-pullback-modules; Tag 0096,
pullback adjunction; Mathlib isoSpec_inv_naturality and restrictStalkNatIso.
(blueprint: lem-pc-affine-spectrum-stalk-coordinate-data). -/
theorem exists_affineSpectrum_stalk_coordinate_data
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
