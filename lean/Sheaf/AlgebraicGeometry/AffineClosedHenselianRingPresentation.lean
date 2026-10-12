/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.PairHenselization

/-! # A directed ring presentation of a closed affine henselian neighborhood

Source: Stacks Project, Tags 0A51, 0A02, and 0032.
(blueprint: lem-weil-pbc-affine-closed-henselian-ring-presentation)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A closed affine pair has a henselian neighborhood presented by a small directed
colimit of rings whose spectra are etale over the original scheme.

Source: Stacks Project, Tags 0A51 (affine proof), 0A02 (henselization of pairs),
and 0032 (directed presentation of a filtered category).
(blueprint: lem-weil-pbc-affine-closed-henselian-ring-presentation)

Proof: Write the affine X as Spec B. A closed immersion into an affine scheme has
an affine source, and its surjective map on global sections presents Z as Spec(B/L),
where L is the kernel. Apply pair_henselization to B and L. Its category of etale
B-algebras trivial modulo L is essentially small and filtered. Replace it by a
small skeleton and then by a cofinal directed preorder (Stacks, Tag 0032).
For the latter, first multiply the small category by the natural-number order;
projection is final. Consider finitely generated subcategories with a unique
terminal object, ordered by inclusion, and map each to its terminal object.
A finite collection of generators admits a cocone by filteredness. Increasing
its natural-number coordinate makes the apex new, so adjoining the cocone
produces such a subcategory. Applying this to the union of two finite sets of
generators proves directedness. Every object occurs in a subcategory; every
arrow can be added to the generators, which proves finality. The generators
form a finite subset of the small category's morphisms, so the resulting index
has universe u. Restrict the ring diagram to this preorder. Finality preserves
its colimit A and its structure map B to A. Put K = LA. Pair henselization gives
henselianness and the quotient isomorphism B/L to A/K. Composing its spectrum with
the affine presentation of Z gives e. The quotient map followed by the structure
map is the original immersion because the corresponding ring maps agree.
The stage structure maps v are etale, and their compatibility and the compatibility
of t with the colimit coprojections are the defining equations of the diagram
of B-algebras. These arguments allow L = 0 and L = B; in the latter case the
henselization is the zero ring and the closed fibre is empty. -/
theorem Etale.affine_closed_henselian_ring_presentation
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (_ : IsColimit c)
      (K : Ideal c.pt) (_ : HenselianRing c.pt K)
      (t : Spec c.pt ⟶ X) (e : Z ≅ Spec (.of (c.pt ⧸ K))),
      i = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ t ∧
      ∃ v : ∀ a : I, Spec (R.obj a) ⟶ X,
        (∀ (a b : I) (f : a ⟶ b), v b = Spec.map (R.map f) ≫ v a) ∧
        (∀ a : I, t = Spec.map (c.ι.app a) ≫ v a) ∧
        (∀ a : I, Etale (v a)) := by sorry

end AlgebraicGeometry
