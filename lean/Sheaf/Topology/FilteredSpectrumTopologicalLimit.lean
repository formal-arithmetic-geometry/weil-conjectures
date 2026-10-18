module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

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
3. A quasi-compact open in a stage spectrum is covered by finitely many
   principal opens. Their inverse images are principal opens in the colimit;
   each is quasi-compact by the principal-localization open immersion and the
   quasi-compactness of affine spectra, and a finite union is quasi-compact.
4. The compatible-family bijection, the topology identification, and the
   quasi-compact inverse-image result give all clauses of the statement.
-/
theorem filteredSpectrumTopologicalLimit
    (I : Type u) [PartialOrder I] [Nonempty I]
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
  sorry

end AlgebraicGeometry

end
