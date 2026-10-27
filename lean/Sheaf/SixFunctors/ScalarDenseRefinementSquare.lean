/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.SixFunctors.ScalarCompositeModelPasting
public import Sheaf.Paper.CompactificationCoherenceCocycle

/-! # Scalar comparison for a refinement with dense source

Source: blueprint latest, det-prop-scalar-six-compact-support.proof.md,
Independence, and det-prop-scalar-six-compact-support DAG steps 3--4.
(blueprint: lem-sfb-scalar-dense-refinement-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- Scalar comparison commutes with refinement from a dense model, even when the
receiving compactification has additional boundary components.

Source: blueprint det-prop-scalar-six-compact-support.proof.md, Independence;
parent DAG steps 3--4 (blueprint: lem-sfb-scalar-dense-refinement-square).

Proof: Let c0 be the schematic closure of X in c.Z. Its open is c.i.toImage,
its proper map is c.i.imageι followed by c.g. Finite type over k makes c.Z
Noetherian, and the open is quasi-compact. The dense source d maps canonically
to c0: the kernel of d.i followed by r is the kernel of r, since d.i is
scheme-theoretically dominant, while d.i followed by r is c.i. The universal
property of the closed immersion c.i.imageι therefore gives a map r0 with
r0 followed by c.i.imageι equal to r. Cancel this closed immersion to obtain
the open and proper triangles. A map from a dense compactification preserves
the distinguished open by denseCompactification_refinement_morphisms, so r0
is a boundary-preserving refinement. The closure inclusion is also boundary
preserving: the pullback of c.i.imageι along c.i is the identity, because
c.i factors through its image by the open immersion c.i.toImage.

Apply scalarRefinementClosureSquare first to the dense pair d and c0, and
then to the closure inclusion c0 to c. Its fourth clause gives the pushed
coefficient square in each case. Identify scalarRefinementPushforward with
compactificationRefinementComponent: both use Rp_* of the same adjunction
transpose; the derived right-adjoint compositor equals RootCoordinateFace.lowerComp
by its conjugate characterization, and deriving lowerStarCongr is equality
transport (by equality induction). The composite of the two refinements is r,
by cancellation of the closed inclusion. The transitivity equation
refinementComponent_comp identifies their pushed composite with the component
of r over each coefficient ring. Apply functoriality of scalar change to this
composite and paste the two squares, reassociating composition. This is the
displayed equality. No invertibility of r's coefficient square is used in
pasting. Empty X, empty ambient schemes, zero coefficients and identity
refinements obey the same image and adjunction universal properties.
-/
theorem scalarDenseRefinementSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification.BoundaryCompactification f.left)
    (d : Compactification.DenseBoundaryCompactification f.left) (r : d.obj ⟶ c)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (scalarSixChange a Y.left).map (compactificationRefinementComponent Λ.X r K.obj) ≫
        sfbScalarCompactComparison a d.obj.obj.obj.i d.obj.obj.obj.g K.obj =
      sfbScalarCompactComparison a c.obj.obj.i c.obj.obj.g K.obj ≫
        compactificationRefinementComponent Λ'.X r
          ((scalarSixChange a X.left).obj K.obj) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
