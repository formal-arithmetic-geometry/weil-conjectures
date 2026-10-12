/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import Sheaf.RingTheory.IntegralOverHenselianPair
import Sheaf.Paper.StrictHenselizationLocalStructure
import Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

/-! # Local sections of an integral geometric fibre

Source: Stacks Project, Tag 0EYP, using Tags 03Q9, 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- Every section on the geometric fibre of an integral morphism is the restriction
of a section over some pointed etale neighbourhood of the geometric point.

Source: Stacks Project, Tag 0EYP, degree zero, via Tags 03Q9, 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-fibre-section-local-lift).

Proof: pass to an affine neighbourhood of the image of s and let A be its strict
henselization at s. The pullback of the integral morphism is affine Spec B, with B
integral over A. If m is the maximal ideal of A, (B,mB) is henselian by Tag 09XK.
Apply the degree-zero henselian comparison (Tag 09ZH, or the proper comparison for
the identity of Spec B) to lift sections from Spec(B/mB) to Spec B. The residue
field k of A is separably closed and maps into Omega. Tag 0A3I identifies sections
on Spec(B/mB) with sections on its base change to Omega, the prescribed fibre X'.
Thus the given section t has a lift to Spec B. The strict-henselization section
continuity formula in Tag 03Q9 represents that lift on an affine pointed etale
neighbourhood (V,v). Compatibility of inverse-image composition with units shows
that its restriction to X' is the unit for g' restricted along the lift whose
projections are (f' followed by v,g') and the identity. These are exactly the
projections defining geometricFibreSectionRestriction. Forgetting the module
structure commutes with these inverse images and section maps, so the argument
for sets applies to F. No algebraicity of Omega over k is required. If the fibre
is empty its section module is zero, and the zero section over the identity
neighbourhood provides the required lift. -/
theorem integralFibreSection_localLift
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 X')))) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
      (z : F.obj.obj (op (f.Etale.obj V))),
      (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z = t := by sorry

end AlgebraicGeometry.Etale
