/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Sections on a zero-dimensional scheme and geometric stalks

Source: Stacks Project, Étale Cohomology, Tag 03QO; Algebra, Tags 00KH and 06RS
(blueprint: lem-weil-pbc-zero-dimensional-sections-stalks).
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Sections are naturally the product of the geometric stalks on a zero-dimensional
separated finite-type scheme over an algebraically closed field.
Source: Stacks Project, Tags 03QO, 00KH, 06RS and 040R
(blueprint: lem-weil-pbc-zero-dimensional-sections-stalks).

Proof:
1. `lem-weil-pbc-zero-dimensional-base-change-points` gives a finite discrete set of
   closed points with residue field k. Each open singleton C_c is a basic affine open
   Spec A_c, with A_c local and having just one prime. These opens disjointly cover C.
2. The residue fields are separably closed. By
   `lem-weil-pbc-dimension-zero-local-strictly-henselian` (Tag 06RS), each A_c is strictly
   henselian.
3. The sheaf condition for the disjoint étale cover gives F(C) = product_c F(C_c):
   off-diagonal intersections are empty, whose sections are zero by the empty covering,
   and diagonal intersections impose only identity compatibility.
4. Factor each geometric point through C_c. Apply
   `lem-weil-pbc-strictly-henselian-sections-stalk` (Tag 03QO) to the restricted sheaf.
   `lem-weil-pbc-etale-inverse-image-restriction` identifies restriction with inverse image;
   `lem-weil-pbc-inverse-image-stalk-germ` identifies its stalk with the original stalk,
   compatibly with the germ of every section on C_c.
5. The colimit relation for germs identifies the global germ with the restricted germ
   on C_c. Thus the displayed product of germ maps is the composite of the isomorphisms
   of steps 3 and 4. Sheaf morphisms commute with the colimit coprojections, giving the
   displayed naturality equation. If C is empty, the empty covering gives the same result.
-/
theorem zeroDimensional_sections_stalks (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))] [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))] (hdim : topologicalKrullDim C ≤ 0)
    (Ω : C → Type u) [∀ c, Field (Ω c)] [∀ c, IsAlgClosed (Ω c)]
    (s : ∀ c, Spec (.of (Ω c)) ⟶ C) (hs : ∀ c, s c default = c) :
    Finite C ∧
      (∀ F : Sheaf C.smallEtaleTopology AddCommGrpCat.{(max u v) + 1},
        IsIso (Limits.Pi.lift (fun c : C =>
          (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
            (Over.homMk (s c) (Category.comp_id (s c))) F.obj))) ∧
      (∀ (F G : Sheaf C.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}) (φ : F ⟶ G),
        φ.hom.app (op (Etale.mk (𝟙 C))) ≫
          Limits.Pi.lift (fun c : C =>
            (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
              (Over.homMk (s c) (Category.comp_id (s c))) G.obj) =
        Limits.Pi.lift (fun c : C =>
          (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
            (Over.homMk (s c) (Category.comp_id (s c))) F.obj) ≫
          Limits.Pi.map (fun c : C => (pointSmallEtale (s c)).sheafFiber.map φ)) := by
  sorry

end AlgebraicGeometry.Scheme
