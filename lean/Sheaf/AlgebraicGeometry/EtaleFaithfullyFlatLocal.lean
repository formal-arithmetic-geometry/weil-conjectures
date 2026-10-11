/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Pointwise étaleness descends along a field extension

Source: Stacks Project, Varieties, Tag 0C4Y and Descent, Tag 02VN
(blueprint: lem-sc-etale-faithfully-flat-local).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Étaleness at a point descends along a faithfully flat field extension.
Source: Stacks Project, Varieties, Tag 0C4Y and Descent, Tag 02VN
(blueprint: lem-sc-etale-faithfully-flat-local).

Proof:
1. Choose affine open neighbourhoods `Spec B` of `x` in `X` and `Spec A` of
   `f x` in `Y`, with `f` restricting to `Spec B ⟶ Spec A`; let `q` be the
   prime of `B` corresponding to `x` (def-pc-scheme, def-pc-morphism-conventions).
   The point `xK` determines a prime `qK` of `B ⊗[k] K` over `q` (def-pc-base-change).
   Étaleness on an open neighbourhood of `xK` gives local finite presentation
   there (def-weil-etale-morphism, def-sbc-locally-finite-presentation).
   Pointwise descent of finite presentation (lem-sc-lfp-field-extension-pointwise-descent)
   lets us shrink so that `B` is finitely presented over `A`. The affine criterion
   for étaleness then gives `Algebra.IsEtaleAt (A ⊗[k] K) qK`.
2. By Tag 0C4Y, `B_q ⟶ (B ⊗[k] K)_qK` is faithfully flat. The hypotheses of
   lem-sc-etale-local-ring-faithfully-flat-descent are supplied by Step 1:
   `B` is finitely presented over the `k`-algebra `A`, `qK` contracts to `q`,
   and the base-changed algebra is étale at `qK`. Applying this lemma descends
   `Algebra.IsEtaleAt` to `q`; the affine criterion (def-weil-etale-morphism)
   supplies an étale open neighbourhood of `x`, which is the conclusion. -/
theorem etale_of_faithfullyFlat_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y)
    (x : X.left)
    (xK : (pullback X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme))
    (hx : (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) xK = x) :
    (let fK := ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map f).left
     ∃ U : (pullback X.hom
       (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
       xK ∈ U ∧ Etale (U.ι ≫ fK)) →
      ∃ U : X.left.Opens, x ∈ U ∧ Etale (U.ι ≫ f.left) := by
  sorry

end AlgebraicGeometry
