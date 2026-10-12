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
import Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

/-! # Integral direct-image germs and sections on a geometric fibre

Source: Stacks Project, Tag 0EYP, via Tags 03Q9, 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

/-- For an integral morphism, restriction of direct-image germs to the geometric
fibre gives an invertible module map, characterized on every pointed neighbourhood.
There is no assertion about the exchange transformation in this statement.

Source: Stacks Project, Tag 0EYP; Tag 03Q9 for direct-image stalks, Tag 09XK for
integral algebras over a henselian pair, Tag 09ZH for henselian restriction of
sections, and Tag 0A3I for extension of separably closed fields.
(blueprint: lem-sbc-integral-geometric-fibre-sections).

Proof: restrict to an affine open of Y through the image of s. Integrality makes
the pullback over the strict henselization Spec A affine, say Spec B, with B
integral over A. The strict-henselization stalk formula identifies each germ
with its restriction to Spec B. Let m be the maximal ideal of A. The integral
henselian-pair theorem makes (B,mB) henselian. Apply the henselian degree-zero
comparison with base ring B and proper morphism the identity of Spec B to
identify sections on Spec B with sections on Spec(B/mB). The map to Omega
factors through the separably closed residue field kappa of A, and identifies
the geometric fibre with Spec(B/mB) base changed from kappa to Omega. Invariance
of etale sections under this field extension identifies these sections with
those on X'. All three maps preserve addition and Lambda scalar multiplication,
so their composite is a module homomorphism and its underlying function is
bijective. For a section represented on (V,v), the stalk formula sends it to
its unit pullback followed by restriction. Functoriality of inverse-image
units identifies the composite restriction with the unit for g' followed by
the lift whose first projection is (f' followed by v,g') and whose second
projection is the identity. This is geometricFibreSectionRestriction. The
formula holds on every representative, and hence on every germ. This proof
also covers the empty fibre: its section module is zero. It uses no finite
type, torsion, or algebraicity assumption on Omega/kappa. -/
theorem integralGeometricFibreSections
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ⟶
        ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      IsIso Θ ∧ ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
        (z : F.obj.obj (op (f.Etale.obj V))),
        Θ.hom ((pointSmallEtale s).toPresheafFiber V v
          ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z) =
        (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z := by
  sorry

end AlgebraicGeometry.Etale
