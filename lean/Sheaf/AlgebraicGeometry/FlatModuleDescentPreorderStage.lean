/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.TensorPullback

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Flatness at the limit descends to one canonical stage of a directed preorder.

Source: Stacks Project, limits.tex, Tag 05LY; categories.tex, Tag 0032.
(blueprint: lem-pc-flat-module-descent-preorder-stage).

Proof: i makes the directed thin category nonempty and filtered. By Tag 0032 choose
a nonempty directed partial order J and a final functor F : J -> I. Finality supplies
t in J and a morphism i -> F(t). Pull M back to the canonical base change at F(t).
Finite presentation of the morphism and module is preserved by base change, and
finite presentation supplies quasi-coherence. Restrict R and c along F and F.op;
initiality of F.op preserves the limiting cone with the same affine vertex.
Cartesian pasting, tensor-pullback composition and the comparison of cartesian
models identify its limit module with the original one, hence it is relatively flat.
Apply partial-order flat-module descent (Tag 05LY) to obtain s >= t at which this
module is flat. Put j = F(s). Functoriality gives i <= j. Pasting and tensor-pullback
composition identify the stage module with the canonical pullback of M from i to j;
cartesian-model comparison transfers its relative flatness. This concludes existence
at one stage; propagation to later original stages is not part of this lemma.
Empty source schemes and the zero module remain flat. The object i rules out an
empty index category; antisymmetry of I and flat transition maps are not needed. -/
theorem exists_isFlatOver_of_isPullback_limit_preorder_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation]
    (hflat : ((Scheme.Modules.tensorPullback
      (pullback.fst f (c.π.app (op i)))).obj M).IsFlatOver
      (pullback.snd f (c.π.app (op i)))) :
    ∃ (j : I) (hij : i ≤ j),
      ((Scheme.Modules.tensorPullback
        (pullback.fst f (Spec.map (R.map (homOfLE hij))))).obj M).IsFlatOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij)))) := by
  sorry

end AlgebraicGeometry
