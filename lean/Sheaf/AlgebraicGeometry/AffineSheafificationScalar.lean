/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule

/-! # Scalars in the underived affine associated-sheaf functor

Source: Stacks Project, Tags 01I6 and 06Z0, associated-sheaf construction.
(blueprint: lem-sc-affine-sheafification-scalar).
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Affine sheafification takes multiplication by an affine section to multiplication
by its restrictions on the localized site. This is an underived statement about one module.
Source: Stacks Project, Tag 01I6, the associated-sheaf construction and its linearity;
Tag 06Z0, its termwise use in the derived affine equivalence.
(blueprint: lem-sc-affine-sheafification-scalar).

Proof: Write the affine sheafification as tilde followed by restriction along the affine
spectrum isomorphism and the inverse over-site equivalence. On tilde, multiplication by r
on a module sends a local fraction m/s to rm/s; this is multiplication by the image of r
in the local structure ring. Restriction along the spectrum isomorphism transports this
image by the structure-sheaf ring map. The defining affine spectrum isomorphism identifies
this transported section on each open V contained in U with the restriction of r from U
to V. The inverse over-site equivalence only reindexes V as an object of Over U and
transports the coefficient ring through the canonical restriction identification. Thus
every component of the mapped scalar identity is multiplication by the corresponding
component of overSections U r. The homModule action has precisely these components.
Extensionality of module-sheaf morphisms proves the equality. This fraction calculation
also holds for r = 0 and for the empty open, with the unique maps of zero rings. -/
theorem affine_perfect_sheafification_scalar (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (M : ModuleCat.{u} (X.presheaf.obj (op U)))
    (r : X.presheaf.obj (op U)) :
    let B := (Over.forget U).op ⋙ X.sheaf.obj
    letI : Linear (RingCat.sectionsSubring (B ⋙ forget₂ CommRingCat RingCat.{u}))
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
      SheafOfModules.homLinear B ((moduleRings X.toRingedSpace).over U).property
    (affinePerfectSheafification X U hU).map (r • 𝟙 M) =
      PresheafOfModules.overSections (R := X.sheaf.obj) U r •
        𝟙 ((affinePerfectSheafification X U hU).obj M) := by sorry

end AlgebraicGeometry.Scheme
