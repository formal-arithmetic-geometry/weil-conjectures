/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import WeilConjectures.AlgebraicGeometry.GenericFibreAffineRingModels
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction

/-! # Extension of a trait line section from integral generic germs

Source: Stacks Project, divisors.tex, Tag 0E9I (`lemma-depth-2-hartog`),
algebra.tex (`lemma-criterion-reduced`, `lemma-apply-grothendieck`), and the
agent spreading argument in the DAG
(blueprint: lem-sfb-trait-line-section-generic-germs-extension).

The generic fibre is represented by its canonical open image `D(π)` in `Y`.
For a quasi-coherent module, the stalk of `j_*(M|D(π))` at `y` is canonically
`M_y[1/π]`: on affine neighbourhoods this is localization of sections at π,
and passage to the stalk commutes with localization. The restriction-adjunction
unit on stalks is precisely the localization map. This uses the existing
restriction, direct image, germ and stalk constructions without choosing maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Restrict `sU` to the generic fibre and regard it as a global section of its
canonical direct image to `Y`. The inverse `restrictAppIso` only identifies the
sections of a restricted module with sections on the image open.
Source: Stacks Project, sheaves.tex, Tag 006T, and schemes.tex, Tags 01HV and 01IA.
(blueprint: lem-sfb-trait-line-section-generic-germs-extension) -/
def traitLineGenericSection {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (π : R) (M : Y.Modules) (U : Y.Opens)
    (hU : (f ⁻¹ᵁ PrimeSpectrum.basicOpen π) ≤ U) (sU : Γ(M, U)) :
    Γ((Scheme.Modules.pushforward ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι).obj
      (M.restrict ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι), ⊤) :=
  (M.restrictAppIso ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι
      (((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι ⁻¹ᵁ ⊤)).inv
    (M.presheaf.map
      (homOfLE ((((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι_image_le _).trans hU)).op sU)

/-- The generic restriction of a line section extends uniquely when its germs at
all generic points of the reduced curve special fibre are integral. The last
conjunct gives the intermediate gluing open, its agreement with every integral
lift, and the two depth bounds on its complement.

Source: Stacks Project, divisors.tex, Tag 0E9I (`lemma-depth-2-hartog`),
algebra.tex (`lemma-criterion-reduced`, `lemma-apply-grothendieck`), and the
agent spreading and assembly argument
(blueprint: lem-sfb-trait-line-section-generic-germs-extension).

Proof plan (the six steps of the node):
1. Apply lem-sfb-flat-curve-line-depth with tensor powers one and zero. The
   scheme is Noetherian, π acts injectively on line stalks, and both depths
   are at least two at closed points of the special fibre.
2. On an affine open the generic part is D(π), by
   lem-sbc-generic-fibre-affine-ring-models. The vanishing clause of
   lem-weil-pbc-affine-module-basic-open-localization gives π^n t = 0
   for a section vanishing generically. Stalk injectivity gives zero germs;
   the sheaf axiom gives t = 0. An affine cover proves injectivity on every
   open, including non-quasi-compact opens.
3. At a special-fibre generic point write the generic section as a/π^n on
   an affine trivialization, using the other clause of that localization
   lemma. An integral lift b_eta satisfies π^n b_eta = a_eta: first in the
   localization, then in the stalk by π-injectivity. The germ representative
   and germ equality properties of def-weil-pbc-module-stalk spread b_eta
   to b on a neighbourhood with π^n b = a. Generically b equals sU.
4. Take W to be U union these neighbourhoods. Step 2 makes the sections
   agree on all overlaps, so the sheaf axiom glues sW. Stalk π-injectivity
   makes integral lifts unique, hence sW has every prescribed integral germ.
5. Outside W a point is in the special fibre and is not a component generic
   point. Pure dimension one implies it is closed: a further specialization
   would give a strict chain of irreducible closed subsets of length two.
   Schemes are T0. Step 1 gives both depth bounds there.
6. On affine trivializations apply lem-sbc-depth-two-hartogs-restriction
   to the structure sheaf and the open W. Its affine sections and stalks
   are finite of rank one, and Step 5 gives depth two on the boundary.
   Extend the coefficient of sW uniquely and multiply by the line basis.
   Step 2 makes these local extensions agree on overlaps, and then with
   sU on U. They glue globally, uniquely by Step 2. Empty schemes and
   empty special fibres have no missing germs or boundary and are included.
-/
theorem trait_line_section_generic_germs_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (π : R) (hπ : Irreducible π)
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
    (hpure : (f.fiber (IsLocalRing.closedPoint R)).IsPureDimension 1)
    (M : Y.Modules) [M.IsInvertible] (U : Y.Opens)
    (hU : (f ⁻¹ᵁ PrimeSpectrum.basicOpen π) ≤ U) (sU : Γ(M, U))
    (hintegral : ∀ (Z : Set (f.fiber (IsLocalRing.closedPoint R))),
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →
      ∀ η : f.fiber (IsLocalRing.closedPoint R), IsGenericPoint η Z →
        ((Scheme.Modules.pushforward ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι).obj
            (M.restrict ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι)).presheaf.germ ⊤
          (f.fiberι (IsLocalRing.closedPoint R) η) (Set.mem_univ _)
          (traitLineGenericSection f π M U hU sU) ∈
        Set.range (((TopCat.Presheaf.stalkFunctor Ab.{u}
          (f.fiberι (IsLocalRing.closedPoint R) η)).map
            (((Scheme.Modules.restrictAdjunction ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι).unit.app
              M).mapPresheaf)))) :
    (∃! s : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = sU) ∧
    (∀ V : Y.Opens, Function.Injective
      (M.presheaf.map (homOfLE (inf_le_left : V ⊓ (f ⁻¹ᵁ PrimeSpectrum.basicOpen π) ≤ V)).op)) ∧
    ∃ (W : Y.Opens) (hUW : U ≤ W) (sW : Γ(M, W)),
      M.presheaf.map (homOfLE hUW).op sW = sU ∧
      (∀ (Z : Set (f.fiber (IsLocalRing.closedPoint R))),
        Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →
        ∀ η : f.fiber (IsLocalRing.closedPoint R), IsGenericPoint η Z →
          ∃ hηW : f.fiberι (IsLocalRing.closedPoint R) η ∈ W,
            ∀ t : M.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint R) η),
              ((TopCat.Presheaf.stalkFunctor Ab.{u}
                  (f.fiberι (IsLocalRing.closedPoint R) η)).map
                (((Scheme.Modules.restrictAdjunction ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι).unit.app
                  M).mapPresheaf)) t =
                ((Scheme.Modules.pushforward ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι).obj
                  (M.restrict ((f ⁻¹ᵁ PrimeSpectrum.basicOpen π)).ι)).presheaf.germ ⊤
                    (f.fiberι (IsLocalRing.closedPoint R) η) (Set.mem_univ _)
                    (traitLineGenericSection f π M U hU sU) →
              M.presheaf.germ W (f.fiberι (IsLocalRing.closedPoint R) η) hηW sW = t) ∧
      (∀ y : Y, y ∉ W →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := Y.presheaf.stalk y) (Y.presheaf.stalk y) ∧
        ∃ hfinite : Module.Finite (Y.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y) M.val.presheaf y),
          (2 : ℕ∞) ≤ @IsLocalRing.depth (Y.presheaf.stalk y) _ _
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y) M.val.presheaf y) _ _ hfinite) := by
  sorry

end AlgebraicGeometry
