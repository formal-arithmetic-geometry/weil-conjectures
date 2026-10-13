/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.AffineFreeBasisGerms

/-! # Scalar action on the unit germ of affine sheafification

Source: Stacks Project, Tag 01HV, Lemma 26.5.4, functoriality, and Tag 0098.
(blueprint: lem-sc-affine-regular-stalk-scalar).
-/

@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme

/-- A scalar endomorphism acts on the explicit unit germ by the scalar's germ.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4, functoriality, and Tag 0098.
(blueprint: lem-sc-affine-regular-stalk-scalar).

Proof: Tilde sends multiplication by a in Gamma(X,U) to multiplication by the
corresponding structure-sheaf section on Spec Gamma(X,U). The affine chart pulls
this section back to a on U: its structure-ring map is the canonical sections map,
as follows from the construction of isoSpec and GammaSpecIso. The regular-module
isomorphism affineRegularSheafIso is tildeSelf, restrictUnitIso, and the unit
isomorphism of overEquiv, so it respects this multiplication. On the slice open
U times U the conjugated endomorphism therefore multiplies by the restriction of a
along the second projection. Under pushforwardOver this restriction is exactly the
scalar action of a on sections over U. Apply the germ map to its value on 1.
PresheafOfModules.germ_smul turns the product into germ(a) times the unit germ,
which is affineRegularStalkGerm by its explicit definition. This also applies
to a = 0 and a = 1; an empty U has no x satisfying hxU. -/
theorem affineRegularStalkGerm_scalar
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (a : Γ(X, U)) :
    (affineFreeStalkFunctor X x U hU).map (affineScalarEnd X U a)
        (affineRegularStalkGerm X x U hxU hU) =
      X.presheaf.germ U x hxU a • affineRegularStalkGerm X x U hxU hU := by sorry

end AlgebraicGeometry.Scheme
