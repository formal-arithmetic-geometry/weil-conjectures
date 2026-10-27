/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.FibreStalkQuotient
public import Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
import Sheaf.RingTheory.FiberRegularSequenceNeighbourhood
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # A prescribed germ realized by a smooth Cartier cut

Source: Stacks Project, More on Morphisms, Tag 057C; Divisors, Tags 062Y and 056Q;
Algebra, Tag 00CT (blueprint: lem-trf-prescribed-germ-smooth-cartier-cut).

The helper constructions are the actual principal quotient and its base-change map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The spectrum of the quotient by a specified section.
Source: Stacks Project, Tag 057C (blueprint: lem-trf-prescribed-germ-smooth-cartier-cut). -/
abbrev prescribedGermCut {X : Scheme.{u}} {U : X.Opens} (a : Γ(X, U)) : Scheme.{u} :=
  Spec (CommRingCat.of (Γ(X, U) ⧸ Ideal.span {a}))

/-- The principal quotient's canonical closed immersion into the affine chart.
Source: Stacks Project, Tag 057C (blueprint: lem-trf-prescribed-germ-smooth-cartier-cut). -/
def prescribedGermCutι {X : Scheme.{u}} {U : X.Opens} (a : Γ(X, U)) :
    prescribedGermCut a ⟶ Spec Γ(X, U) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))

/-- Base change of a morphism into the source of `f` to the fibre over `s`.
This is the pullback map with identity maps on the base and its residue field.
Source: Stacks Project, Tags 057C and 056Q
(blueprint: lem-trf-prescribed-germ-smooth-cartier-cut). -/
def prescribedGermFiberMap {X S Y : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) (s : S) :
    (j ≫ f).fiber s ⟶ f.fiber s :=
  pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The canonical map on local rings at specified equal image points.
Source: Stacks Project, Tag 00CT
(blueprint: lem-trf-prescribed-germ-smooth-cartier-cut). -/
def prescribedGermStalkMap {X Y : Scheme.{u}} (j : Y ⟶ X) (x : X) (y : Y)
    (h : j y = x) : X.presheaf.stalk x ⟶ Y.presheaf.stalk y :=
  (X.presheaf.stalkCongr (.of_eq h)).inv ≫ j.stalkMap y

/-- A specified fibre-regular germ with nonzero residue differential can be represented
on an affine neighbourhood inside any prescribed neighbourhood by a smooth Cartier cut.
The quotient equivalence is induced by the actual fibre closed immersion: its equality
on every element of the fibre stalk includes the localization fraction formula on every
chart. The last equation identifies the induced residue map with the identity on κ(x).

Source: Stacks Project, Tag 057C, `lemma-slice-smooth-given-element`, with the fibre
Cartier assertion of Tag 056Q and the canonical localization quotient of Tag 00CT.
(blueprint: lem-trf-prescribed-germ-smooth-cartier-cut).

Proof plan, following the six steps of the node:
1. Smoothness supplies flat, finitely presented affine charts. Represent h by r/t in
   the local ring; shrink to a basic open inside W and invert t, preserving h exactly
   (affine-open-stalk-localization and spec-localization-away-basic-open).
2. Identify the fibre stalk with the localization of the fibre tensor ring. The
   singleton equation is regular there: multiplication is injective and the quotient
   is nonzero since h lies in the maximal ideal. Apply
   lem-pur-fiber-regular-sequence-neighbourhood to make the same equation regular on
   a principal ambient neighbourhood. Its quotient is an effective Cartier divisor.
3. Apply lem-zl-hypersurface-nonzero-relative-differential to the equation in the
   trivial invertible module. Lift the resulting smooth open of the closed subscheme
   to an ambient open and choose a smaller basic affine neighbourhood. Localization
   preserves injective multiplication, the germ, and smoothness.
4. The smooth quotient algebra is flat over the affine base. Tensor its principal
   short exact sequence with the residue field using flat-quotient-tensor-injective.
   Tensor-quotient-base-change identifies its fibre with the principal fibre quotient,
   proving that the actual fibre immersion is effective Cartier.
5. Open-fibre-product and affine-open-stalk-localization identify R with the fibre
   chart's localization. Localization-at-prime-of-quotient gives the equivalence,
   sending [c/u] to [(c mod a_s)/(u mod a_s)]. The stalk map of the actual closed
   immersion gives the same map on every chart. The immersion gives the unique point.
6. A quotient by an ideal inside the maximal ideal has the same residue field.
   Apply scheme-fibre-stalk-quotient to X and to the cut, then the local principal
   quotient description. Every residue is the residue of the same original germ,
   so the residue map is the identity. No closedness or separability is needed.
-/
theorem exists_prescribed_germ_smooth_cartier_cut
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (h : X.presheaf.stalk x)
    (hh : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hregular : Function.Injective
      (fun z : (f.fiber (f x)).presheaf.stalk (f.asFiber x) ↦
        (f.fiberStalkMap x).hom h * z))
    (hdiff : ∃ (V : X.Opens) (hxV : x ∈ V) (b : Γ(X, V)),
      X.presheaf.germ V x hxV b = h ∧ f.relativeDifferentialValue V x hxV b)
    (W : X.Opens) (hxW : x ∈ W) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U) (a : Γ(X, U)),
      U ≤ W ∧ X.presheaf.germ U x hxU a = h ∧
      IsEffectiveCartierCenter (prescribedGermCutι a) ∧
      Smooth (prescribedGermCutι a ≫ hU.fromSpec ≫ f) ∧
      (∃! xD : prescribedGermCut a, (prescribedGermCutι a ≫ hU.fromSpec) xD = x) ∧
      IsEffectiveCartierCenter
        (prescribedGermFiberMap (hU.fromSpec ≫ f) (prescribedGermCutι a) (f x)) ∧
      ∃ (y : ((prescribedGermCutι a ≫ hU.fromSpec) ≫ f).fiber (f x))
        (hy : prescribedGermFiberMap f (prescribedGermCutι a ≫ hU.fromSpec) (f x) y =
          f.asFiber x)
        (e : ((f.fiber (f x)).presheaf.stalk (f.asFiber x) ⧸
          Ideal.span {(f.fiberStalkMap x).hom h}) ≃+*
          (((prescribedGermCutι a ≫ hU.fromSpec) ≫ f).fiber (f x)).presheaf.stalk y),
        (∀ c : (f.fiber (f x)).presheaf.stalk (f.asFiber x),
          e (Ideal.Quotient.mk _ c) =
            prescribedGermStalkMap
              (prescribedGermFiberMap f (prescribedGermCutι a ≫ hU.fromSpec) (f x))
              (f.asFiber x) y hy c) ∧
        ∃ r : (((prescribedGermCutι a ≫ hU.fromSpec) ≫ f).fiber (f x)).residueField y ≃+*
            X.residueField x,
          ∀ b : X.presheaf.stalk x,
            r (((((prescribedGermCutι a ≫ hU.fromSpec) ≫ f).fiber (f x)).residue y)
              (e (Ideal.Quotient.mk _ ((f.fiberStalkMap x).hom b)))) = X.residue x b := by
  sorry

end AlgebraicGeometry
