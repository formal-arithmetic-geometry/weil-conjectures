/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso

/-! # Affine coordinates for the closed-immersion coefficient morphism

Source: Stacks Project, Tags 01I9 and 0BQZ. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On an affine chart the closed-immersion unit is the sheafified quotient map.
Source: Stacks Project, Tag 01I9, Lemma 26.7.3(2), and Tag 0BQZ,
Lemma 48.15.5, the coefficient map in its proof.
(blueprint: lem-sc-affine-closed-immersion-coefficient-square).

Proof: Put A = Gamma(Y,U) and I = ker(i)(U). The preimage of U is affine,
and the section map A -> Gamma(Z,i⁻¹U) is surjective with kernel I. Its
quotient isomorphism presents the restricted immersion as Spec(A/I) -> Spec A.
Use the affine quotient restricted isomorphism for the target coefficient
sheaf. For the source use tilde(A) = O_Spec(A), transport across isoSpec,
and the restriction isomorphism for O_Y. Choose the quotient identification
induced by the first isomorphism theorem, rather than an arbitrary object
isomorphism. On every basic open D(g), these identifications are the canonical
localization identifications: the restricted unit sends x/g^k to its image in
(A/I)_g. The pullback-unit isomorphism sends the tensor unit to 1, so the
adjunction formula in ha gives exactly this localized quotient map. Both
sides of the asserted equality therefore agree on every basic open. The
basis sheaf condition gives equality of the sheaf morphisms. The coefficient
map formula can also be read directly from
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`
and `SheafOfModules.unitToPushforwardObjUnit_val_app_apply`. For I = top,
the target sheaf is zero; for the zero ring or empty chart all sections and
maps are unique. No sequence, complex, or regularity condition is involved. -/
theorem affine_closedImmersion_coefficient_square
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let A := (Γ(Y, U.1) : Type u)
    let I := i.ker.ideal U
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let R := Scheme.Modules.restrictFunctor U.1.ι
    ∃ (eO : R.obj (SheafOfModules.unit Y.ringCatSheaf) ≅ T.obj (ModuleCat.of A A))
      (eB : R.obj ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ≅ T.obj (ModuleCat.of A (A ⧸ I))),
      R.map a ≫ eB.hom = eO.hom ≫ T.map (ModuleCat.ofHom I.mkQ) := by sorry

end AlgebraicGeometry
