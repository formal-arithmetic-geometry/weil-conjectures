module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Local rings and residue fields of a directed ring colimit

Source: Stacks Project, Tag 04GI, `lemma-colimit-henselian`, the omitted locality and
residue-field colimit argument (blueprint: lem-sfb-local-colimit-residue-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A directed colimit of local rings along local maps is local, its maximal ideal is the
union of the images of the stage maximal ideals, and its residue field is the ring colimit
of the stage residue fields. The maps are Mathlib's canonical `IsLocalRing.ResidueField.map`.

Source: Stacks Project, Tag 04GI, `lemma-colimit-henselian`, omitted argument
(blueprint: lem-sfb-local-colimit-residue-field).

Proof plan:
1. Use `lem-pc-filtered-colimit-commrings-elementwise` to represent every element at a
   stage and detect equality at a common later stage. Nonempty directedness makes the
   indexing category filtered (`def-weil-pbc-category-colimit`).
2. If an image belongs to the union of the maximal-ideal images, move the two
   representatives to a common stage. Locality of both transition maps gives membership
   in the original maximal ideal. The converse follows from the definition of the union.
3. Move finitely many representatives to a common stage to check that this union is an
   ideal. Contraction to any stage shows that it does not contain 1.
4. By `lem-weil-pbc-local-ring-unit-criterion`, every element outside the union is a unit:
   choose an inverse at a stage. Thus the union is the unique maximal ideal, the colimit
   is local, and every cocone leg is local.
5. The quotients by these maximal ideals are nonzero fields: an element represented
   outside the maximal ideal has the inverse constructed in step 4.
6. The canonical residue maps are well defined because the ring maps preserve maximal
   ideals. They commute with the quotient maps, respect composition, and form a cocone.
   Contraction of maximal ideals shows that the residue maps are injective.
7. Given compatible residue-field maps to any commutative ring B, compose with the
   stage quotient maps. The original colimit property gives a map to B. It kills the
   union, so factors through the colimit residue field with the required composites.
8. Any second factorization has the same composites with all original cocone legs,
   hence agrees before quotienting by the original colimit property. Surjectivity of
   the quotient map gives uniqueness. This includes B equal to the zero ring. -/
theorem local_colimit_residue_field
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [∀ i : I, IsLocalRing (F.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsLocalHom (F.map f).hom]
    (c : Cocone F) (hc : IsColimit c) :
    ∃ (_ : IsLocalRing c.pt) (_ : ∀ i : I, IsLocalHom (c.ι.app i).hom),
      (IsLocalRing.maximalIdeal c.pt : Set c.pt) =
        ⋃ i : I, (c.ι.app i).hom ''
          (IsLocalRing.maximalIdeal (F.obj i) : Set (F.obj i)) ∧
      (∀ i : I, (IsLocalRing.maximalIdeal c.pt).comap (c.ι.app i).hom =
        IsLocalRing.maximalIdeal (F.obj i)) ∧
      (∀ i : I, Function.Injective
        (IsLocalRing.ResidueField.map (R := F.obj i) (S := c.pt) (c.ι.app i).hom)) ∧
      (∀ (B : CommRingCat.{u})
          (h : ∀ i : I, IsLocalRing.ResidueField (F.obj i) →+* B),
        (∀ (i j : I) (f : i ⟶ j),
          (h j).comp (IsLocalRing.ResidueField.map (F.map f).hom) = h i) →
        ∃! g : IsLocalRing.ResidueField c.pt →+* B,
          ∀ i : I, g.comp
            (IsLocalRing.ResidueField.map (R := F.obj i) (S := c.pt) (c.ι.app i).hom) = h i) := by
  classical
  have hι {i j : I} (f : i ⟶ j) (x : F.obj i) :
      (c.ι.app j).hom ((F.map f).hom x) = (c.ι.app i).hom x :=
    congrArg (fun g : F.obj i ⟶ c.pt ↦ g.hom x) (c.w f)
  have hlocal (i : I) : IsLocalHom (c.ι.app i).hom := by
    constructor
    intro x hx
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc y
    obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
    have heq : c.ι.app k ((F.map f).hom x * (F.map g).hom y) = c.ι.app k 1 := by
      change (c.ι.app k).hom _ = (c.ι.app k).hom _
      rw [map_mul, hι f, hι g, map_one, hy]
    obtain ⟨l, a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ heq
    have hu : IsUnit ((F.map a).hom ((F.map f).hom x)) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨(F.map a).hom ((F.map g).hom y), ?_⟩
      simpa only [map_mul, map_one] using hab
    exact isUnit_of_map_unit (F.map f).hom x
      (isUnit_of_map_unit (F.map a).hom _ hu)
  let : ∀ i : I, IsLocalHom (c.ι.app i).hom := hlocal
  let i : I := Classical.choice inferInstance
  let : Nontrivial c.pt := nontrivial_of_ne (0 : c.pt) 1 (by
    intro h01
    have hu : IsUnit ((c.ι.app i).hom 0) := by
      rw [map_zero, h01]
      exact isUnit_one
    exact not_isUnit_zero (isUnit_of_map_unit (c.ι.app i).hom 0 hu))
  let : IsLocalRing c.pt := IsLocalRing.of_isUnit_or_isUnit_one_sub_self (by
    intro z
    obtain ⟨j, x, rfl⟩ := Concrete.isColimit_exists_rep F hc z
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hx | hx
    · exact Or.inl (hx.map (c.ι.app j).hom)
    · exact Or.inr (by simpa only [map_sub, map_one] using hx.map (c.ι.app j).hom))
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨j, x, rfl⟩ := Concrete.isColimit_exists_rep F hc z
      refine Set.mem_iUnion.mpr ⟨j, x, ?_, rfl⟩
      change x ∈ (IsLocalRing.maximalIdeal c.pt).comap (c.ι.app j).hom at hz
      rwa [IsLocalRing.maximalIdeal_comap (R := F.obj j) (S := c.pt)] at hz
    · intro hz
      obtain ⟨j, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
      exact map_nonunit (R := F.obj j) (S := c.pt) (c.ι.app j).hom x hx
  · intro j
    exact IsLocalRing.maximalIdeal_comap (R := F.obj j) (S := c.pt) (c.ι.app j).hom
  · intro j
    exact (IsLocalRing.ResidueField.map (R := F.obj j) (S := c.pt) (c.ι.app j).hom).injective
  · intro B h hh
    let s : Cocone F :=
      { pt := B
        ι :=
          { app := fun j ↦ ofHom ((h j).comp (IsLocalRing.residue (F.obj j)))
            naturality := by
              intro j k f
              ext x
              exact DFunLike.congr_fun (hh j k f) (IsLocalRing.residue (F.obj j) x) } }
    let t : c.pt →+* B := (hc.desc s).hom
    have ht (j : I) (x : F.obj j) :
        t ((c.ι.app j).hom x) = h j (IsLocalRing.residue (F.obj j) x) :=
      congrArg (fun g : F.obj j ⟶ B ↦ g.hom x) (hc.fac s j)
    have hkill (z : c.pt) (hz : z ∈ IsLocalRing.maximalIdeal c.pt) : t z = 0 := by
      obtain ⟨j, x, rfl⟩ := Concrete.isColimit_exists_rep F hc z
      have hx : x ∈ IsLocalRing.maximalIdeal (F.obj j) := by
        rw [← IsLocalRing.maximalIdeal_comap (R := F.obj j) (S := c.pt)
          (c.ι.app j).hom]
        exact hz
      rw [ht, (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    let g : IsLocalRing.ResidueField c.pt →+* B :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal c.pt) t hkill
    have hg (j : I) :
        g.comp (IsLocalRing.ResidueField.map (R := F.obj j) (S := c.pt)
          (c.ι.app j).hom) = h j := by
      ext z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      exact ht j x
    refine ⟨g, hg, ?_⟩
    intro g' hg'
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨j, x, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    exact (DFunLike.congr_fun (hg' j) (IsLocalRing.residue (F.obj j) x)).trans
      (ht j x).symm

end CommRingCat
