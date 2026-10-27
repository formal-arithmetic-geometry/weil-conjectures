/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.RingedModuleSkyscraper
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Length
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Coherent modules with finite closed support

Source: Stacks Project, Varieties, Tag 0C1R, proof of (2) and (4), in its general
finite-support coherent-module form; Sheaves, Tags 009A--009C; Algebra, Tag 00L5
(blueprint: lem-trf-coherent-finite-support-skyscrapers).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module with finite closed support is canonically the finite direct sum
of the skyscrapers of its stalks, and those nonzero stalk modules have finite length.
The bicone and its bilimit witness express the finite direct sum without fixing a
choice of biproduct. Its isomorphism from `F` is characterized by the germ in every
coordinate. The stalk identification is characterized by coordinate evaluation on germs.

Source: Stacks Project, Varieties, Tag 0C1R (2),(4), general coherent-module argument;
Sheaves, Tags 009A--009C; Algebra, Tag 00L5
(blueprint: lem-trf-coherent-finite-support-skyscrapers).

Proof:
1. At a supported point choose a Noetherian affine neighbourhood. Affine stalk
   localization and permanence of Noetherianness under localization make its stalk
   ring Noetherian (lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-localization-noetherian).
2. Coherence implies quasi-coherence and finite type on a locally Noetherian scheme
   (pqf-lem-coherent-ft-locnoeth). The stalk is finite by
   lem-weil-pbc-finite-type-module-stalk-finite and nonzero by the support hypothesis.
   Affine germ localization identifies it with the localization of affine sections
   (lem-sbc-affine-module-germ-localization).
3. A nonmaximal prime of this local ring contracts to a strictly smaller prime on
   the affine neighbourhood (lem-weil-pbc-localization-spectrum-embedding). Its point
   cannot be a supported closed point, so the corresponding stalk vanishes.
   Localization twice agrees with localization at the contracted prime: the maps
   send (n/s)/(a/t) to tn/(sa) and n/v to (n/1)/(v/1). The fraction relation of
   def-weil-pbc-module-localization proves these maps well defined and inverse.
4. Apply lem-sc-generic-stalk-finite-length. A chain of greatest length from zero
   to the whole module exists by the bounded-chain definition of length
   (def-weil-pbc-module-length). It has positive length. Every successive quotient
   is nonzero and simple, since a proper nonzero submodule would refine the chain.
5. Form the finite product of the ringed module skyscrapers. Coordinate inclusions
   and the sum of coordinate maps make it also a coproduct. The coordinate germ
   maps commute with restriction and scalar multiplication (def-weil-pbc-module-stalk),
   hence give a module morphism from F to this biproduct.
6. Near a supported point y, remove all the other finitely many closed support points.
   On the resulting neighbourhood the product is the constant skyscraper value F_y.
   Coordinate evaluation on germs is the canonical stalk identification and sends
   the germ morphism to the identity. Outside the support, its open complement
   gives zero stalks on both sides and the zero map.
7. Apply lem-weil-pbc-module-iso-on-stalks to the germ morphism. For empty support
   the finite sum is zero and the same argument gives that F is zero.
-/
theorem coherent_finite_support_skyscrapers
    (X : Scheme.{u}) [IsLocallyNoetherian X] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (S : Finset X)
    (hS : ∀ x : X, x ∈ S ↔ ¬ Subsingleton (F.presheaf.stalk x))
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    (∀ x ∈ S,
      Nontrivial (F.presheaf.stalk x) ∧
      Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) ∧
      (∀ p : PrimeSpectrum (X.presheaf.stalk x),
        p.asIdeal ≠ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
          Subsingleton (LocalizedModule p.asIdeal.primeCompl (F.presheaf.stalk x))) ∧
      ∃ c : CompositionSeries (Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)),
        0 < c.length ∧ c.head = ⊥ ∧ c.last = ⊤) ∧
    (∃ b : Bicone (C := X.Modules) (fun x : {x : X // x ∈ S} ↦
        SheafOfModules.ringedModuleSkyscraper X.toRingedSpace x.val
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x.val).obj F)),
      Nonempty b.IsBilimit ∧ ∃ e : F ≅ b.pt,
        (∀ (x : {x : X // x ∈ S}) (U : X.Opens) (hx : x.val ∈ U)
          (s : F.val.obj (op U)),
          ((e.hom ≫ b.π x).val.app (op U) s) ⟨hx⟩ =
            F.presheaf.germ U x.val hx s) ∧
        (∀ y : {x : X // x ∈ S},
          ∃ v : b.pt.presheaf.stalk y.val ≃ₗ[X.presheaf.stalk y.val] F.presheaf.stalk y.val,
            (∀ (U : X.Opens) (hy : y.val ∈ U) (t : b.pt.val.obj (op U)),
              v (b.pt.presheaf.germ U y.val hy t) = ((b.π y).val.app (op U) t) ⟨hy⟩) ∧
            ∀ m : F.presheaf.stalk y.val, v (e.hom.stalkLinearMap y.val m) = m) ∧
        (∀ y : X, y ∉ S →
          Subsingleton (F.presheaf.stalk y) ∧ Subsingleton (b.pt.presheaf.stalk y) ∧
            e.hom.stalkLinearMap y = 0)) ∧
    (S = ∅ → IsZero F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
