/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
public import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel

/-! # Étale normal forms for a nodal family with étale markings

Source: Stacks Project, curves.tex, Tag 0CBY; Illusie--Laszlo--Orgogozo,
Exposé VI, Proposition 1.9 (blueprint: lem-trf-nodal-etale-chart).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The origin in the universal nodal chart: both coordinates vanish in the residue field.
Source: Stacks Project, curves.tex, Tag 0CBY (blueprint: lem-trf-nodal-etale-chart). -/
noncomputable def nodalOrigin {V : Scheme.{u}} (h : Γ(V, ⊤))
    (p : pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)) : Prop :=
  ∀ k : Fin 2,
    ((pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).presheaf.germ
      ⊤ p trivial)
      ((pullback.fst nodalModelBaseMap (nodalBaseMap h)).appTop
        ((Scheme.ΓSpecIso (.of nodalModelRing)).inv
          (Ideal.Quotient.mk _ (MvPolynomial.X k)))) ∈
      IsLocalRing.maximalIdeal
        ((pullback (C := Scheme.{u}) nodalModelBaseMap (nodalBaseMap h)).presheaf.stalk p)

/-- Étale normal forms for a nodal family with an étale Cartier marking.

Source: Stacks Project, curves.tex, Tag 0CBY; ILO Exposé VI, Proposition 1.9,
printed pp. 70--71 (blueprint: lem-trf-nodal-etale-chart).

Proof, following the four steps of the node:
1. At a smooth point outside the closed Cartier marking, shrink to the smooth locus
   and the marking's complement. Connected one-dimensional Noetherian nodal fibres
   are pure of dimension one: a zero-dimensional component would be a clopen point.
   This supplies the pure-dimension hypothesis of `lem-trf-nodal-family-fitting-singular`.
2. At a marked point, both the ambient relative curve and its etale marking are smooth.
   Apply `lem-pur-smooth-pair-local-coordinates` with relative dimensions one and zero,
   hence a = 0 and b = 1. Its cartesian square identifies the marking as the coordinate
   zero subscheme, including its scheme structure.
3. At a nonsmooth point use `lem-trf-nodal-family-etale-local-model` (Stacks 0CBY).
   The etale source neighbourhood admits a lift of the given geometric point since
   its residue extensions are finite separable. Etale invariance of smoothness and
   the Jacobian (v,u) of uv-h imply that this lift maps to u=v=0 in the residue field.
   Remove the marking, which lies in the smooth locus. The node locus of the model
   is V(h). Remove from the base the closed complement in V(h) of its intersection
   with the open image of the chart. Every remaining h=0 point has a node in that
   image. Smoothness away from the boundary then forces h to be invertible there.
4. Choose a fine saturated base chart using `def-trf-log-regular-pair`, refining the
   source neighbourhood over it in all three cases and retaining the geometric lift.
   In the nodal case, h is a divisorial section since it is invertible off the boundary.
   The stalk chart pushout writes its germ as a chart element times a unit. Spread
   this equality over a further pointed etale neighbourhood to obtain h = εα(a).
-/
theorem exists_nodal_etale_chart
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {U₀ : Scheme.{u}} (j : U₀ ⟶ Y) [IsOpenImmersion j] (hU : DenseRange j)
    (hlog : IsDivisorialFineSaturatedLogRegularPair Y U₀ j hU)
    [Flat f] [LocallyOfFinitePresentation f]
    (hNodal : HasNodalGeometricFibres f)
    (D : Scheme.{u}) (i : D ⟶ X) (hCartier : IsEffectiveCartierCenter i)
    [Etale (i ≫ f)]
    (hD : ∀ d : D, i d ∈ f.smoothLocus)
    (hSmooth : ∀ x : X, f x ∈ Set.range j → x ∈ f.smoothLocus) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      ∃ (V : Y.Etale) (W : Scheme.{u}) (v : W ⟶ X) (w : W ⟶ V.left)
        (xW : Spec (.of Ω) ⟶ W),
        Etale v ∧ v ≫ f = w ≫ V.hom ∧ xW ≫ v = x ∧
        ∃ hunit : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
            (t' : Spec (.of Ω') ⟶ Y),
            IsUnit.submonoid (strictLocalRing Y t') ≤ divisorialStalk j t',
          ∃ (P : Type u) (_ : CommMonoid P) (c : P →* divisorialSections j V),
            IsFineSaturatedMonoid P ∧
            (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
              (t' : Spec (.of Ω') ⟶ Y) (w' : (Scheme.pointSmallEtale t').fiber.obj V),
              IsDivisorialStalkChart (divisorialStalk j t') (hunit Ω' t')
                ((divisorialGerm j t' V w').comp c)) ∧
            (((Scheme.SpecToEquivOfField Ω X x).1 ∈ f.smoothLocus ∧
                (Scheme.SpecToEquivOfField Ω X x).1 ∉ Set.range i ∧
                Smooth w ∧
                ∀ z : W, z ∉ Set.range (pullback.snd (C := Scheme.{u}) i v)) ∨
              ((Scheme.SpecToEquivOfField Ω X x).1 ∈ Set.range i ∧
                ∃ e : W ⟶ AffineSpace (ULift (Fin 1)) V.left,
                  Etale e ∧
                  e ≫ (AffineSpace.over (ULift (Fin 1)) V.left).hom = w ∧
                  ∃ g : pullback (C := Scheme.{u}) i v ⟶
                      (AffineSpace (ULift (Fin 1)) V.left).zeroLocusSubscheme
                        {AffineSpace.coord V.left (ULift.up 0)},
                    IsPullback g (pullback.snd (C := Scheme.{u}) i v)
                      ((AffineSpace (ULift (Fin 1)) V.left).zeroLocusSubschemeι
                        {AffineSpace.coord V.left (ULift.up 0)}) e) ∨
              ((Scheme.SpecToEquivOfField Ω X x).1 ∉ f.smoothLocus ∧
                (∀ z : W, z ∉ Set.range (pullback.snd (C := Scheme.{u}) i v)) ∧
                ∃ (h : Γ(V.left, ⊤))
                  (m : W ⟶ pullback nodalModelBaseMap (nodalBaseMap h)),
                  Etale m ∧ m ≫ pullback.snd nodalModelBaseMap (nodalBaseMap h) = w ∧
                  nodalOrigin h (m (Scheme.SpecToEquivOfField Ω W xW).1) ∧
                  (∀ z : V.left,
                    z ∈ Set.range (pullback.snd (C := Scheme.{u}) j V.hom) →
                      IsUnit ((V.left.presheaf.germ ⊤ z trivial) h)) ∧
                  ∃ (ε : Γ(V.left, ⊤)ˣ) (a : P), h = ε.1 * (c a).1)) := by
  sorry

end AlgebraicGeometry
