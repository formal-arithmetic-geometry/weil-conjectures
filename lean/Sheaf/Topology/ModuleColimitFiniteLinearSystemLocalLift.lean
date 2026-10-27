/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Local lifting of finite linear systems in module-sheaf colimits

Source: Stacks Project, Modules, Tag 0GMV, finite-relation argument, and Sheaves,
Tag 009F, local representatives and local equality before finite-cover extraction
(blueprint: lem-weil-pbc-module-colimit-finite-linear-system-local-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u r

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafOfModules

/-- A finite tuple satisfying finitely many homogeneous linear equations in a directed
colimit of module sheaves lifts, near each point, to a solution at one common stage.

Source: Stacks Project, Modules, Tag 0GMV, and Sheaves, Tag 009F, local part of the proof
(blueprint: lem-weil-pbc-module-colimit-finite-linear-system-local-lift).

Proof: (1) The underlying-set colimit theorem
`lem-weil-pbc-module-directed-colimit-underlying-sets` and the sheafified-presheaf
colimit theorem `lem-weil-pbc-sheaves-colimit-sheafification` identify the specified
colimit cocone with the sheafification of the sectionwise set colimit. The comparison
isomorphism respects every cocone leg by the colimit universal property
`def-weil-pbc-category-colimit`.
(2) Apply `lem-weil-pbc-site-sheafification-sections-local` to each of the finitely many
sections at the given point. Represent each resulting presheaf-colimit section at a
stage using clause (1) of `lem-weil-pbc-filtered-colimit-sets-elementwise`.
(3) Intersect these finitely many neighbourhoods and choose a common upper index,
starting at any index of the nonempty preorder. Restrict and advance the representatives.
Naturality and the cocone laws show that they still lift the given sections. Each
linear-relation error maps to zero by sectionwise linearity
`def-weil-sheaf-of-modules-category`.
(4) Local equality in sheafification, followed by clause (3) of
`lem-weil-pbc-filtered-colimit-sets-elementwise`, kills each relation error on a
neighbourhood at a later stage. This uses no compactness or injectivity.
(5) Intersect the finitely many new neighbourhoods and choose one upper index for all
of the later stages. Restriction, transition-map linearity, and the cocone laws give
both the requested lifts and all the equations. For no unknowns take the initial
neighbourhood to be W; for no equations no further shrinking is needed. An empty W
has no point to consider. -/
theorem colimit_finite_linear_system_local_lift
    {X : Type u} [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{max u r})
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat)).obj O))
    (c : Cocone F) (hc : IsColimit c)
    (W : Opens X) (m n : ℕ)
    (a : Fin m → Fin n → O.obj.obj (op W))
    (s : Fin n → c.pt.val.obj (op W))
    (hs : ∀ k : Fin m, ∑ r : Fin n, a k r • s r = 0) :
    ∀ x : X, x ∈ W →
      ∃ (V : Opens X) (hVW : V ≤ W) (i : I)
        (t : Fin n → (F.obj i).val.obj (op V)),
        x ∈ V ∧
        (∀ r : Fin n, (c.ι.app i).val.app (op V) (t r) =
          c.pt.val.map (homOfLE hVW).op (s r)) ∧
        (∀ k : Fin m, ∑ r : Fin n,
          O.obj.map (homOfLE hVW).op (a k r) • t r = 0) := by
  sorry

end SheafOfModules
