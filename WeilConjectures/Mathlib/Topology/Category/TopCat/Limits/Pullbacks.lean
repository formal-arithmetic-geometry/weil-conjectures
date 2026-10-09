/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import WeilConjectures.Mathlib.Topology.Separation.Hausdorff

/-!
# Pullbacks

Ported from the `proetale` package (`Proetale.Mathlib.Topology.Category.TopCat.Limits.Pullbacks`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

lemma TopCat.prodFst_apply {X Y : TopCat.{u}} (x : X × Y) : TopCat.prodFst x = x.1 := by
  rfl

lemma TopCat.prodSnd_apply {X Y : TopCat.{u}} (x : X × Y) : TopCat.prodSnd x = x.2 := by
  rfl

-- use the following lemma: `t2Space_iff_diagonal_closed`
-- after `TopCat.isEmbedding_pullback_to_prod`
