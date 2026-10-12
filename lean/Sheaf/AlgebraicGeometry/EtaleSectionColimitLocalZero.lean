/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Local vanishing before finite selection in etale sheaf colimits

Source: Stacks Project, Sites, Lemma Tag 0738, proof of part (2).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A zero colimit image gives local eventual vanishing on a covering sieve.
Source: Stacks Project, Sites, Lemma Tag 0738 (lemma-directed-colimits-sections),
proof of part (2), the local equality assertion before finite-cover selection.
(blueprint: lem-weil-pbc-etale-section-colimit-local-zero-sieve).

Proof: Form the presheaf P whose value on an etale object V is the filtered
colimit of the modules G_i(V). The cocone maps give P a map to the colimit
sheaf H. Identify this map with the sheafification unit, respecting each
coprojection, using the sheaf-colimit universal property. The image in P(U)
of s and the zero section have equal images in H(U). Local injectivity of
sheafification gives a covering sieve on which their restrictions agree in
P. On each arrow of that sieve, the filtered module-colimit equality criterion
puts the restricted section and zero at a common later index. Its transition
map from i is the required killing arrow. The resulting arrows are closed
under restriction by naturality, so they contain a covering sieve S as asserted.
Only local equality is used here: no finite subfamily and no global separatedness
conclusion is asserted. In the independent universes of this statement, the
identification must be established on an affine etale basis, with its finite
coverings; an arbitrary HasWeakSheafify instance alone does not supply local
injectivity. Quasi-compact etale objects admit finite affine refinements, so
these finite matching diagrams and the filtered sectionwise colimit stay in
the coefficient universe. -/
theorem etale_section_colimit_local_zero_sieve
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) (i : I)
    (s : (G.obj i).obj.obj (Opposite.op U))
    (hs : ((c.ι.app i).hom.app (Opposite.op U)).hom s = 0) :
    ∃ S : Sieve U, S ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (q : V ⟶ U), S q →
        ∃ (j : I) (f : i ⟶ j),
          ((G.map f).hom.app (Opposite.op V)).hom
            (((G.obj i).obj.map q.op).hom s) = 0 := by
  sorry

end AlgebraicGeometry
