module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Topological spectrum of a directed colimit of rings

Source: Stacks Project, Tags 0CUE and 0CUF, with the final quasi-compactness
assertion from Algebra, Tag 00E8 (blueprint: lem-a1-filtered-spectrum-topological-limit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Source: Stacks Project, `limits.tex`, Tags 0CUE and 0CUF (affine-case proofs),
and `algebra.tex`, Tag 00E8 (blueprint: lem-a1-filtered-spectrum-topological-limit).

The index poset is small in the universe of the rings, so that the forgetful
functor preserves this filtered colimit. This relative smallness is essential.

1. A prime of the colimit contracts along each coprojection to a compatible
   family. Conversely, the elementwise description of a filtered ring colimit
   gives a prime from every compatible family: a common upper stage proves that
   the resulting ideal is proper and prime, and also proves both constructions
   are inverse.
2. The inverse image of a principal open under each coordinate map is the
   corresponding principal open defined by the image of its element. Every
   principal open of the colimit spectrum comes from a stage, so the Zariski
   topology is the coarsest topology making all coordinate projections
   continuous. This identifies the compatible-family topology with the
   topology used by the displayed `Homeomorph`.
3. Every morphism between affine schemes is affine and hence quasi-compact.
   Apply the compact-open preimage theorem from Mathlib directly. Its proof
   packages the finite-principal-open argument of Algebra, Tag 00E8.
4. The compatible-family bijection, the topology identification, and the
   quasi-compact inverse-image result give all clauses of the statement.
-/
theorem filteredSpectrumTopologicalLimit
    (I : Type u) [Small.{v} I] [PartialOrder I] [Nonempty I]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (F : I ⥤ CommRingCat.{v})
    (c : Cocone F) (hc : IsColimit c) :
    (∃ e : Homeomorph (Spec c.pt)
        {p : (i : I) → Spec (F.obj i) //
          ∀ (i j : I) (hij : i ≤ j),
            (Spec.map (F.map (homOfLE hij))) (p j) = p i},
      ∀ x : Spec c.pt,
        (e.1 x : (i : I) → Spec (F.obj i)) =
          (fun i => (Spec.map (c.ι.app i)) x)) ∧
      ∀ (i : I) (Q : Set (Spec (F.obj i))),
        IsOpen Q → IsCompact Q →
          IsCompact ((Spec.map (c.ι.app i)) ⁻¹' Q) := by
  classical
  have : IsDirectedOrder I := ⟨hdir⟩
  have : PreservesColimitsOfShape I (forget CommRingCat.{v}) := by
    let e := ((Shrink.equivalence.{v} I).trans (ShrinkHoms.equivalence.{v} _)).symm
    have := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e (forget CommRingCat.{v})
  have hw {i j : I} (g : i ⟶ j) (a : F.obj i) :
      c.ι.app j (F.map g a) = c.ι.app i a :=
    ConcreteCategory.congr_hom (c.w g) a
  let P := {p : (i : I) → Spec (F.obj i) //
    ∀ (i j : I) (hij : i ≤ j),
      (Spec.map (F.map (homOfLE hij))) (p j) = p i}
  let f : Spec c.pt → P := fun x => ⟨fun i => (Spec.map (c.ι.app i)) x, by
    intro i j hij
    change PrimeSpectrum.comap (F.map (homOfLE hij)).hom
      (PrimeSpectrum.comap (c.ι.app j).hom x) = _
    rw [← PrimeSpectrum.comap_comp_apply]
    exact congrArg (fun g : F.obj i ⟶ c.pt => PrimeSpectrum.comap g.hom x)
      (c.w (homOfLE hij))⟩
  have hsurj : Function.Surjective f := by
    intro p
    have hmem {i j : I} (g : i ⟶ j) (a : F.obj i) :
        F.map g a ∈ (p.val j).asIdeal ↔ a ∈ (p.val i).asIdeal := by
      have h := p.property i j (leOfHom g)
      change PrimeSpectrum.comap (F.map g).hom (p.val j) = p.val i at h
      rw [← h]
      rfl
    have heq {i j : I} (a : F.obj i) (b : F.obj j)
        (h : c.ι.app i a = c.ι.app j b) :
        a ∈ (p.val i).asIdeal ↔ b ∈ (p.val j).asIdeal := by
      obtain ⟨k, g, g', hgg⟩ := (Concrete.isColimit_rep_eq_iff_exists F hc a b).mp h
      rw [← hmem g a, ← hmem g' b, hgg]
    let J : Ideal c.pt :=
      { carrier := {x | ∃ i a, c.ι.app i a = x ∧ a ∈ (p.val i).asIdeal}
        zero_mem' := ⟨Nonempty.some ‹Nonempty I›, 0, map_zero _, zero_mem _⟩
        add_mem' := by
          rintro _ _ ⟨i, a, rfl, ha⟩ ⟨j, b, rfl, hb⟩
          obtain ⟨k, hik, hjk⟩ := hdir i j
          dsimp only [id_eq] at hik hjk
          refine ⟨k, F.map (homOfLE hik) a + F.map (homOfLE hjk) b, ?_,
            add_mem ((hmem _ _).mpr ha) ((hmem _ _).mpr hb)⟩
          rw [map_add]
          exact congrArg₂ (· + ·) (hw (homOfLE hik) a) (hw (homOfLE hjk) b)
        smul_mem' := by
          rintro a _ ⟨j, b, rfl, hb⟩
          obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc a
          obtain ⟨k, hik, hjk⟩ := hdir i j
          dsimp only [id_eq] at hik hjk
          refine ⟨k, F.map (homOfLE hik) a * F.map (homOfLE hjk) b, ?_,
            Ideal.mul_mem_left _ _ ((hmem _ _).mpr hb)⟩
          rw [map_mul, smul_eq_mul]
          exact congrArg₂ (· * ·) (hw (homOfLE hik) a) (hw (homOfLE hjk) b) }
    have hJ (i : I) (a : F.obj i) : c.ι.app i a ∈ J ↔ a ∈ (p.val i).asIdeal :=
      ⟨fun ⟨j, b, hba, hb⟩ => (heq b a hba).mp hb, fun ha => ⟨i, a, rfl, ha⟩⟩
    have hprime : J.IsPrime :=
      { ne_top' := by
          rw [Ne, Ideal.eq_top_iff_one]
          let i := Nonempty.some ‹Nonempty I›
          rw [← map_one (c.ι.app i).hom, hJ]
          exact (p.val i).isPrime.one_notMem
        mem_or_mem' := by
          intro a b hab
          obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc a
          obtain ⟨j, b, rfl⟩ := Concrete.isColimit_exists_rep F hc b
          obtain ⟨k, hik, hjk⟩ := hdir i j
          dsimp only [id_eq] at hik hjk
          have hmul := (map_mul (c.ι.app k).hom
            (F.map (homOfLE hik) a) (F.map (homOfLE hjk) b)).trans
              (congrArg₂ (fun x y : c.pt => x * y)
                (hw (homOfLE hik) a) (hw (homOfLE hjk) b))
          have hab' := (hJ k _).mp (hmul.symm ▸ hab)
          obtain ha | hb := (p.val k).isPrime.mem_or_mem hab'
          · exact Or.inl ((hJ i a).mpr ((hmem _ _).mp ha))
          · exact Or.inr ((hJ j b).mpr ((hmem _ _).mp hb)) }
    refine ⟨⟨J, hprime⟩, Subtype.ext (funext fun i => PrimeSpectrum.ext ?_)⟩
    exact Ideal.ext (hJ i)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc a
    have h := congrFun (congrArg Subtype.val hxy) i
    exact Iff.of_eq (congrArg (fun q : PrimeSpectrum (F.obj i) => a ∈ q.asIdeal) h)
  have hcont : Continuous f := by
    exact (continuous_pi fun i => (Spec.map (c.ι.app i)).continuous).subtype_mk _
  have hopen : IsOpenMap f := by
    apply PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff.mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc a
    have he : f '' (PrimeSpectrum.basicOpen (R := c.pt) ((c.ι.app i).hom a)).carrier =
        {p : P | p.val i ∈ PrimeSpectrum.basicOpen a} := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hp
        obtain ⟨x, rfl⟩ := hsurj p
        exact ⟨x, hp, rfl⟩
    change IsOpen (f '' (PrimeSpectrum.basicOpen
      ((c.ι.app i).hom a)).carrier)
    rw [he]
    exact (PrimeSpectrum.basicOpen a).isOpen.preimage
      ((continuous_apply i).comp continuous_subtype_val)
  constructor
  · exact ⟨(IsHomeomorph.homeomorph f ⟨hcont, hopen, hinj, hsurj⟩), fun _ => rfl⟩
  · intro i Q hQ hcQ
    exact QuasiCompact.isCompact_preimage (f := Spec.map (c.ι.app i)) Q hQ hcQ

end AlgebraicGeometry

end
