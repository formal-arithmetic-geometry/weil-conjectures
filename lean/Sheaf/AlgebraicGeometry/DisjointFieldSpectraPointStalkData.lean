/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict

import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Points and stalks of a partition by field spectra

Source: Stacks Project, Morphisms, Tag 02G7 (lemma-unramified-over-field), part (1),
and Sheaves, Tag 0078 (section-stalks).
(blueprint: lem-trf-disjoint-field-spectra-point-stalk-data)

The scalar compatibility equations express that the canonical ring isomorphisms are
isomorphisms over the given base field. The scalar map to a stalk is obtained from the
structure morphism on global sections followed by the germ; its composite with the residue
quotient is the scalar map to the residue field.
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The unique point of an open field spectrum, regarded as a point of the open subscheme.
Source: Stacks Project, Morphisms, Tag 02G7, part (1), field-spectrum description.
(blueprint: lem-trf-disjoint-field-spectra-point-stalk-data) -/
def fieldSpectrumOpenPoint {Y : Scheme.{u}} {U : Y.Opens} {L : Type u} [Field L]
    (e : U.toScheme ≅ Spec (.of L)) : U :=
  e.inv (IsLocalRing.closedPoint L)

/-- The canonical coordinate-field identification with sections on the open subscheme.
Source: Stacks Project, Morphisms, Tag 02G7, part (1), and the definition of an open subscheme.
(blueprint: lem-trf-disjoint-field-spectra-point-stalk-data) -/
def fieldSpectrumOpenSections {Y : Scheme.{u}} {U : Y.Opens} {L : Type u} [Field L]
    (e : U.toScheme ≅ Spec (.of L)) : CommRingCat.of L ⟶ Y.presheaf.obj (op U) :=
  (Scheme.ΓSpecIso (.of L)).inv ≫ e.hom.appTop ≫ U.topIso.hom

/-- The coordinate-field map to the stalk is the actual germ after the section identification.
Source: Stacks Project, Morphisms, Tag 02G7, part (1); Sheaves, Tag 0078, section-stalks.
(blueprint: lem-trf-disjoint-field-spectra-point-stalk-data) -/
def fieldSpectrumOpenGerm {Y : Scheme.{u}} {U : Y.Opens} {L : Type u} [Field L]
    (e : U.toScheme ≅ Spec (.of L)) :
    CommRingCat.of L ⟶ Y.presheaf.stalk (fieldSpectrumOpenPoint e).val :=
  fieldSpectrumOpenSections e ≫
    Y.presheaf.germ U (fieldSpectrumOpenPoint e).val (fieldSpectrumOpenPoint e).property

/-- An arbitrary open partition by field spectra gives a bijection on points, closed points,
and canonical stalk and residue-field isomorphisms over the base field. In `CommRingCat`,
`IsIso` together with the displayed scalar equation is precisely a base-field algebra
isomorphism; the residue algebra structure is induced by the canonical quotient.
Source: Stacks Project, Morphisms, Tag 02G7 (lemma-unramified-over-field), part (1),
and Sheaves, Tag 0078 (section-stalks).
(blueprint: lem-trf-disjoint-field-spectra-point-stalk-data)

Proof:
1. Each field spectrum has one point (def-weil-affine-spectrum), so each open is the
   singleton of `fieldSpectrumOpenPoint`. The cover gives surjectivity, and disjointness
   gives injectivity, including the empty partition (def-pc-scheme).
2. The complement of each singleton is the union of all the other opens. It is open even
   for an infinite partition, so the point is closed (def-weil-closed-points).
3. Open restriction identifies the section rings (def-weil-open-immersion). Invert the
   germ by restricting a representative on a neighborhood to the singleton open. Every
   neighborhood contains that singleton. Equality of germs gives agreement on a smaller
   neighborhood, so the inverse is well defined and both composites are identities
   (def-weil-pbc-module-stalk). This proves invertibility of the specified germ map.
4. The isomorphism is over k, so sections and their germs preserve the structure scalars
   (def-weil-scheme-over-base, def-weil-locally-ringed-space-morphism,
   def-pc-field-extension). The stalk is therefore a field. Its maximal ideal is zero,
   since every nonzero element is a unit. Thus its canonical residue quotient is
   invertible (def-weil-residue-field), as is the composite from L. The quotient scalar
   map is induced by the stalk scalar map. No finiteness or separability is used. -/
theorem disjoint_field_spectra_point_stalk_data
    (k : Type u) [Field k] (Y : Scheme.{u}) (f : Y ⟶ Spec (.of k))
    (I : Type v) (U : I → Y.Opens) (L : I → Type u)
    [∀ i, Field (L i)] [∀ i, Algebra k (L i)]
    (e : ∀ i, (U i).toScheme ≅ Spec (.of (L i)))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : iSup U = ⊤)
    (hover : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (L i))) =
      (U i).ι ≫ f) :
    Function.Bijective (fun i ↦ (fieldSpectrumOpenPoint (e i)).val) ∧
      ∀ i, (fieldSpectrumOpenPoint (e i)).val ∈ closedPoints Y ∧
        IsIso (fieldSpectrumOpenGerm (e i)) ∧
        (CommRingCat.ofHom (algebraMap k (L i)) ≫ fieldSpectrumOpenGerm (e i) =
          (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            Y.presheaf.germ ⊤ (fieldSpectrumOpenPoint (e i)).val trivial) ∧
        IsIso (fieldSpectrumOpenGerm (e i) ≫ Y.residue (fieldSpectrumOpenPoint (e i)).val) ∧
        (CommRingCat.ofHom (algebraMap k (L i)) ≫ fieldSpectrumOpenGerm (e i) ≫
            Y.residue (fieldSpectrumOpenPoint (e i)).val =
          (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
            Y.presheaf.germ ⊤ (fieldSpectrumOpenPoint (e i)).val trivial ≫
              Y.residue (fieldSpectrumOpenPoint (e i)).val) ∧
        IsIso (Y.residue (fieldSpectrumOpenPoint (e i)).val) := by
  sorry

end

end AlgebraicGeometry
