/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Equivalence of the affine and big fppf sites

Source: Stacks Project, Tag 021V, Topologies Lemma 34.7.11
(blueprint: lem-pc-fppf-affine-site-topos-equivalence).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The affine fppf site is a dense subsite of the big fppf site, and restriction
along its inclusion is an equivalence for sets and abelian groups.
Source: Stacks Project, Tag 021V, Topologies Lemma 34.7.11
(blueprint: lem-pc-fppf-affine-site-topos-equivalence).

Here `CostructuredArrow Scheme.Spec S` presents all affine schemes over `S`, with
arbitrary structure morphisms. Its coverings are the families whose underlying scheme
morphisms form an fppf covering, as specified by `fppfPrecoverage.comap`.

Proof:
1. The inclusion is fully faithful: morphisms are exactly morphisms of affine
   `S`-schemes (`def-pc-fppf-site`, `def-pc-scheme`).
2. Every scheme over `S` has an affine open covering. Open immersions are flat
   and locally of finite presentation, so this is an fppf covering
   (`lem-pc-fppf-affine-open-cover`).
3. Every fppf covering of an affine scheme has a finite refinement by affine
   opens of its members; the composites remain fppf and jointly surjective
   (`lem-pc-fppf-affine-refinement`). Thus the affine covering topology is the
   topology induced from the big site.
4. These facts give a dense subsite. Apply the dense-subsite comparison theorem
   (`lem-pc-fppf-dense-sheaf-equivalence`) to sets and abelian groups. The
   equivalence functor is restriction, and its quasi-inverse is sheaf transport
   along the inclusion. -/
theorem fppf_affine_site_topos_equivalence (S : Scheme.{u}) :
    (fun (G : CostructuredArrow Scheme.Spec S ⥤ Over S)
      (K : GrothendieckTopology (Over S))
      (J : GrothendieckTopology (CostructuredArrow Scheme.Spec S)) ↦
      G.IsDenseSubsite J K ∧
        ∀ [h : G.IsDenseSubsite J K],
          (G.sheafPushforwardContinuous (Type (max u v)) J K).IsEquivalence ∧
            (G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).IsEquivalence)
      (CostructuredArrow.toOver Scheme.Spec S)
      (fppfTopology.over S)
      ((fppfPrecoverage.comap
        (CostructuredArrow.toOver Scheme.Spec S ⋙ Over.forget S)).toGrothendieck) := sorry

end AlgebraicGeometry.Scheme
