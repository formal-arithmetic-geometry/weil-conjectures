/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Ordinary Zariski module pushforward and filtered colimits

Source: Stacks Project, Coherent sheaves, Tag 07TB, `lemma-colimit-cohomology`,
the case `p = 0` with the natural structure-sheaf action
(blueprint: lem-sfb-zariski-pushforward-filtered-colimit).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Ordinary Zariski module pushforward along a quasi-compact quasi-separated scheme
morphism commutes with small filtered colimits, through the canonical comparison.

Source: Stacks Project, Coherent sheaves, Tag 07TB, `lemma-colimit-cohomology`, `p = 0`
(blueprint: lem-sfb-zariski-pushforward-filtered-colimit).

Proof:
1. Form the module-sheaf colimits `L = colimit M` and
   `C = colimit (M ⋙ pushforward f)`. By
   `lem-weil-pbc-module-sheaves-colimits-forgetful` (2),(3), their underlying abelian
   sheaves are the corresponding colimits. The cocone obtained by applying `f_*`
   to the coprojections into `L` induces `colimit.post M (pushforward f)`.
2. For an affine open `V` of `Y`, set `W = f⁻¹ V`. By
   `lem-weil-pbc-affine-scheme-qcqs` and `lem-weil-pbc-qcqs-morphism-permanence`,
   both `V` and `W` are qcqs. By `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings`,
   every covering of either has a finite affine refinement with quasi-compact
   pairwise intersections. These are also coverings in the ambient opens sites.
3. Apply `lem-sfb-site-quasi-compact-section-colimit` to the underlying abelian
   diagrams at `V` and `W`. It identifies the colimits of sections with the sections
   of `C` and `L` respectively; no global quasi-separatedness of `X` or `Y` is used.
4. By the ordinary pushforward definition, `(f_* M_j)(V) = M_j(W)` and
   `(f_* L)(V) = L(W)`. After each coprojection, the comparison on `V` composed
   with the first sections isomorphism equals the second sections isomorphism:
   both are the coprojection `M_j(W) → L(W)`, by `colimit.ι_post`.
   Thus the comparison is bijective on every affine open. The affine basis theorem
   `lem-weil-pbc-affine-opens-basis` and
   `lem-weil-pbc-sheaf-morphism-on-basis` (b) make it an abelian-sheaf isomorphism.
   Its inverse is linear by cancellation against the bijective linear comparison,
   and commutes with restriction by the same cancellation. Hence it is an inverse
   in the module-sheaf category of `def-weil-sheaf-of-modules-category`. -/
theorem isIso_colimitPost_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type u} [SmallCategory I] [IsFiltered I] (M : I ⥤ X.Modules) :
    IsIso (colimit.post M (pushforward f)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
