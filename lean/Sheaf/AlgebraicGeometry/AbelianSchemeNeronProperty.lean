module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreCoverDensity
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing

/-! # The Néron mapping property of an abelian scheme

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 1.2 Proposition 8, printed p. 15.
(blueprint: lem-sfb-abelian-scheme-neron-property)

The generic fibre is computed over `Spec D`: first compose the structure map with
`T.ι`, then pull back along `Spec (algebraMap D E)`. Since `T` is a nonempty open
of the integral scheme `Spec D`, this map factors uniquely through `T`. Pullback
pasting canonically identifies these fibres with the fibres over `T`; the functor
on morphisms is their canonical restriction map. No generic-point lift is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An abelian scheme on a nonempty open of a Dedekind spectrum has the Néron
mapping property for every smooth source, without any quasi-compactness hypothesis.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 1.2 Proposition 8, printed p. 15.
(blueprint: lem-sfb-abelian-scheme-neron-property)

Proof plan:
1. By lem-sbc-finite-etale-generic-fibre-cover-density, applied to the identity
   étale cover of any smooth T-scheme Z, Z is reduced and its generic fibre is
   dense. Properness of B implies separatedness (def-weil-proper-morphism), so
   lem-sfb-relative-separated-dominant-ext gives uniqueness of an extension.
2. Cover X by affine opens U_i (def-pc-scheme). Smoothness restricts to these
   opens (def-sbc-smooth-morphisms). Given a map on the generic fibre, apply
   lem-sfb-proper-generic-map-big-open to obtain a domain V_i in U_i containing
   the whole generic fibre and all points of local-ring dimension at most one,
   dense in each fibre, with a map extending the prescribed generic map.
3. Apply lem-sfb-relative-weil-codimension-extension to the smooth separated
   group scheme B, the source U_i and the domain V_i. This extends the map to
   all of U_i. Its generic restriction is the original map since V_i contains
   the whole generic fibre.
4. The extensions agree on every overlap by step 1. Glue them using
   lem-weil-pbc-scheme-morphism-gluing. Their structure maps and generic
   restrictions agree locally and hence globally. Uniqueness follows again
   from step 1. Infinite covers and the empty source are allowed. Thus the
   restriction map is both surjective and injective. -/
theorem abelianScheme_neron_mapping_property
    (D E : Type u) [CommRing D] [IsDedekindDomain D]
    (hD : ringKrullDim D = 1) [Field E] [Algebra D E] [IsFractionRing D E]
    (T : (Spec (CommRingCat.of D)).Opens) [Nonempty T]
    (B : Over T.toScheme) [GrpObj B] [IsCommMonObj B]
    [Smooth B.hom] [IsProper B.hom]
    (hB : ∀ t : T.toScheme, ConnectedSpace (B.hom.fiber t))
    (X : Over T.toScheme) [Smooth X.hom] :
    Function.Bijective (fun f : X ⟶ B ↦
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map
        ((Over.map T.ι).map f)) := by
  sorry

end AlgebraicGeometry
