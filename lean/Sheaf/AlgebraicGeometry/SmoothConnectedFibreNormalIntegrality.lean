/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore

/-!
# Normal integral field extensions of smooth connected fibres

Source: Stacks Project, More on Morphisms, Tag 057J,
lemma-normal-morphism-irreducible (final geometric-fibre argument), specialized to
smooth morphisms using Varieties, Tag 056T, lemma-smooth-geometrically-normal,
and Properties, Tag 033M, lemma-normal-Noetherian.
(blueprint: lem-trf-smooth-connected-fibre-normal-integrality)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every field extension of every fibre of a smooth morphism with geometrically
connected fibres is integral, with integrally closed domain stalks.

Source: Stacks Project, More on Morphisms, Tag 057J,
lemma-normal-morphism-irreducible, final geometric-fibre argument; smooth
specialization by Varieties, Tag 056T, lemma-smooth-geometrically-normal, and
Properties, Tag 033M, lemma-normal-Noetherian.
(blueprint: lem-trf-smooth-connected-fibre-normal-integrality)

Proof following the node:
1. Fix `t` and `K`. Clause (2) of lem-pc-proper-base-change (Tag 01VB) applies
   twice, first to `v` along `B.fromSpecResidueField t`, then to the resulting
   fibre morphism along `Spec.map (CommRingCat.ofHom (algebraMap _ K))`.
   Thus the displayed pullback `C` is smooth over `S = Spec K`.
2. For every extension `L/K`, pullback pasting (def-pc-fibre-product) identifies
   `C` after extension to `L` with the extension of `v.fiber t` to `L`.
   The hypothesis `hconn t` makes this connected. Since `Spec K` has one point,
   the structure map `C → S` has geometrically connected fibres. Taking the
   identity extension shows `C` is nonempty, because ConnectedSpace includes
   nonemptiness (def-weil-connected-scheme).
3. `Spec K` is integral and its local rings are fields, hence integrally closed
   (def-weil-affine-spectrum, def-pc-integral-scheme). Form its actual generic
   fibre using def-pc-fibre-product. Apply lem-sbc-smooth-connected-generic-
   geometry-core over `S` to obtain integrality of `C` and integral closedness
   of all its stalks. Each stalk of an integral scheme is a localization of an
   affine domain and is therefore a domain. This proves both conclusions for
   the arbitrary choices `t` and `K`. No finiteness or normality of `B` or `V`
   is used.
-/
theorem smooth_connected_fibre_normal_integrality
    {V B : Scheme.{u}} (v : V ⟶ B) [Smooth v]
    (hconn : ∀ t : B, GeometricallyConnected (v.fiberToSpecResidueField t))
    (t : B) (K : Type u) [Field K] [Algebra (B.residueField t) K] :
    IsIntegral (pullback (C := Scheme.{u}) (v.fiberToSpecResidueField t)
      (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField t) K)))) ∧
      ∀ x : pullback (C := Scheme.{u}) (v.fiberToSpecResidueField t)
          (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField t) K))),
        IsDomain
          ((pullback (C := Scheme.{u}) (v.fiberToSpecResidueField t)
            (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField t) K)))).presheaf.stalk x) ∧
        IsIntegrallyClosed
          ((pullback (C := Scheme.{u}) (v.fiberToSpecResidueField t)
            (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField t) K)))).presheaf.stalk
            x) := by
  let f := v.fiberToSpecResidueField t
  let g := Spec.map (CommRingCat.ofHom (algebraMap (B.residueField t) K))
  let C := pullback f g
  let S := Spec (.of K)
  let c : C ⟶ S := pullback.snd f g
  let : GeometricallyConnected f := hconn t
  let : Smooth f :=
    inferInstanceAs (Smooth (pullback.snd v (B.fromSpecResidueField t)))
  let : Smooth c := inferInstanceAs (Smooth (pullback.snd f g))
  let : GeometricallyConnected c := inferInstance
  let : Subsingleton S := inferInstance
  let : Nonempty S := inferInstance
  let : ConnectedSpace C :=
    GeometricallyConnected.connectedSpace_of_subsingleton c
  let : Nonempty C := inferInstance
  have hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x) := by
    intro x
    exact Scheme.isIntegrallyClosed_stalk_Spec K x
  let a := S.fromSpecStalk (genericPoint S)
  obtain ⟨hC, hη, hnC, hnη⟩ :=
    Scheme.smooth_connected_generic_geometry_core hS c
      (pullback.fst a c) (pullback.snd a c) (IsPullback.of_hasPullback a c)
  let : IsIntegral C := hC
  change IsIntegral C ∧ ∀ x : C,
    IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x)
  refine ⟨hC, ?_⟩
  intro x
  exact ⟨inferInstance, hnC x⟩

end AlgebraicGeometry
