module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.SiteSheafificationSectionsLocal

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A colimit section has representatives at one stage on a finite covering with
quasi-compact overlaps. No compatibility of these representatives is asserted.
Source: Stacks Project, Sites, Tag 0738, proof of (4), and Etale Cohomology, Tag 03Q4
(blueprint: lem-weil-pbc-etale-section-colimit-local-lifts).

Proof: Form the sectionwise presheaf colimit and identify its module sheafification
with the given sheaf colimit, respecting the coprojections. Local representability
of sheafification supplies a covering on which the section comes from that presheaf.
Etale cancellation views this as a covering of the underlying scheme U. Refine it
by a finite affine etale covering with quasi-compact pairwise fibre products, using
quasi-compactness and quasi-separatedness of U. Regard its objects and overlaps in
X's small etale site by composition. Restrict the presheaf representatives to this
refinement. The filtered module-colimit representative criterion gives a diagram
index for each of the finitely many sections. Choose a common index using filteredness
and transport these representatives to it; cocone naturality preserves their images.
Index the finite family by a finite type in universe u. For an empty covering,
filteredness still supplies an index and the family of sections is empty. -/
theorem etale_section_colimit_local_lifts
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) (t : c.pt.obj.obj (op U)) :
    ∃ (B : Type u) (_ : Finite B) (V : B → X.Etale) (f : ∀ b, V b ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      (∀ b b', CompactSpace (pullback (f b) (f b')).left) ∧
      ∃ (i : I) (s : ∀ b, (G.obj i).obj.obj (op (V b))),
        ∀ b, ((c.ι.app i).hom.app (op (V b))).hom (s b) =
          (c.pt.obj.map (f b).op).hom t := by
  sorry

end AlgebraicGeometry
