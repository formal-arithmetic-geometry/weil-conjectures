/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase

/-!
# Descent of proper module support

Source: Stacks Project, Limits of Schemes, Lemma 32.13.5 (Tag 081G), together with
Cohomology of Schemes, Lemma 30.26.7 (Tag 0CYS)
(blueprint: lem-pc-proper-support-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Proper support of a finitely presented module descends to a later Noetherian stage.
The functor `R` specifies the affine bases `S_k = Spec (R.obj k)` and their affine
transition maps. These bases are qcqs. The cone `c` with `hc` is their inverse limit,
and `IsAffine c.pt` expresses that the limit is `Spec R` for a ring `R`.
The scheme and module at the limit and at a later stage are their indicated pullbacks.

Source: Stacks Project, Tag 081G and Tag 0CYS
(blueprint: lem-pc-proper-support-descent).

Proof:
1. Finite presentation implies quasi-coherence and finite type. By
   lem-weil-pbc-scheme-theoretic-support, form the closed scheme-theoretic support
   Z_i in X_i. Its base changes to X and X_j have underlying sets equal to the
   preimages of Supp(F_i) (Stacks 01JT). These are precisely the supports of the
   pulled-back modules by lem-weil-pbc-support-pullback-finite-type(3).
   The map Z_i to S_i is locally of finite type, and both schemes are qcqs:
   S_i is affine and Z_i is closed in the finitely presented S_i-scheme X_i.
2. The limit support is proper by hypothesis. The closed base change Z of Z_i
   has this underlying support, so Z to S is proper by
   lem-weil-pbc-closed-subset-proper-over-base-properties(1), Stacks 0CYL.
3. Apply lem-weil-pbc-eventually-proper, Stacks 081F, to Z_i to S_i and the
   directed tail of the base system. Some j >= i has Z_j to S_j proper.
4. The underlying set of Z_j is the support of the pullback of F_i by step 1.
   Since X_j to S_j is locally of finite type, properness of Z_j gives proper
   support by lem-weil-pbc-closed-subset-proper-over-base-properties(1). -/
theorem exists_hasSupportProperOver_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Fi : Xi.Modules) [Fi.IsFinitePresentation]
    (hF : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj Fi)) :
    ∃ (j : I) (hij : i ≤ j),
      Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij))))
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE hij))))).obj Fi) := by
  sorry

end AlgebraicGeometry
