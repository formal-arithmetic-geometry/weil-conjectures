/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-! # A flat module on a fixed affine-limit model descends to a later stage

Source: Stacks Project, Tags 01ZR and 05LY.
(blueprint: lem-pc-flat-module-on-later-stage).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- On the limit base change of a fixed finitely presented scheme, a finitely presented
relatively flat module descends to a finitely presented relatively flat module at a
later stage. The source model is fixed; no scheme approximation or properness is asserted.

Source: Stacks Project, limits.tex, Tag 01ZR (lemma-descend-modules-finite-presentation)
and Tag 05LY (lemma-descend-module-flat-finite-presentation).
(blueprint: lem-pc-flat-module-on-later-stage).

Proof: Work on the directed tail of indices above i; it is cofinal, so the limit
is unchanged. The base changes of Zi on this tail are quasi-compact and quasi-separated,
since fi is so and every base is affine. Their transition maps are affine, as base
changes of morphisms between affine schemes. Base change preserves the limit.
Finite presentation of M implies quasi-coherence. Apply Tag 01ZR to obtain j above i,
a finitely presented module N on the base change of the fixed source to Spec R_j,
and an isomorphism of its limit tensor pullback with M. Transport relative flatness
of M through this isomorphism, by restriction of scalars of the sectionwise linear
isomorphisms on affine opens. Apply Tag 05LY to N, starting at j, to obtain a stage k
above j at which its pullback is flat over Spec R_k. Take M_k to be this pullback;
finite presentation is preserved by tensor pullback. Cartesian pasting identifies the
iterated source base change with the direct base change from i to k. The canonical
composition isomorphism for tensor pullback, followed by the initial comparison with M,
gives the displayed comparison. This does not require proper support or derived objects.
The starting index excludes an empty index set. Empty sources, zero modules and zero
rings cause no exception; no transition map is assumed flat. -/
theorem exists_flat_module_on_later_stage
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Zi : Scheme.{u}} (fi : Zi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (M : (pullback fi (c.π.app (Opposite.op i))).Modules) [M.IsFinitePresentation]
    (hM : M.IsFlatOver (pullback.snd fi (c.π.app (Opposite.op i)))) :
    ∃ (j : I) (hij : i ≤ j)
      (Mj : (pullback fi (Spec.map (R.map (homOfLE hij)))).Modules),
      Mj.IsFinitePresentation ∧
      Mj.IsFlatOver (pullback.snd fi (Spec.map (R.map (homOfLE hij)))) ∧
      Nonempty ((Scheme.Modules.moduleBaseChange fi
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (Opposite.op i)))
        (Over.homMk (c.π.app (Opposite.op j)) (c.w (homOfLE hij).op))).obj Mj ≅ M) := by sorry

end AlgebraicGeometry
