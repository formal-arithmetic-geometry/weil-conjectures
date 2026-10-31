/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QuasiAffineTargetLocality
import WeilConjectures.AlgebraicGeometry.QuasiAffineBaseChange

/-! # Finite affine enlargement of a quasi-compact pullback open

Source: Stacks Project, More on Morphisms, Tag 0AP7, affine-base reduction, and
lemma-ind-quasi-affine-composition; Morphisms, Tag 01SO
(blueprint: lem-a1-qc-open-pullback-quasi-affine-enlargement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A quasi-compact pullback open lies over a finite union of affine opens and embeds in
its quasi-affine base change. The two projection equations characterize the induced map.

Source: Stacks Project, More on Morphisms, Tag 0AP7, affine-base reduction, and
lemma-ind-quasi-affine-composition; Morphisms, Tag 01SO
(blueprint: lem-a1-qc-open-pullback-quasi-affine-enlargement).

Proof plan:
1. The affine opens cover X by lem-weil-pbc-affine-opens-basis. Pull their cover back
   to L and use its quasi-compactness to choose finitely many Wj covering its image in X.
   Each Wj is quasi-compact by lem-weil-pbc-affine-scheme-qcqs. Restrict an open cover of
   their union W to each Wj and combine the resulting finitely many finite subcovers.
   Thus W is quasi-compact and the hypothesis makes W quasi-affine. For empty L use n = 0.
2. The universal property def-pc-fibre-product identifies W times_A B with W times_X Z,
   an open subscheme of Z by lem-weil-pbc-open-immersion-base-change, with image p inverse W.
   Since L is contained in this open, restriction of the structure sheaf gives its induced
   open immersion into W times_A B (def-weil-open-immersion), with the projection equations.
3. Apply lem-a1-quasi-affine-target-locality to W -> A and the singleton affine cover of A.
   The resulting quasi-affine morphism stays quasi-affine after base change to B by
   lem-trf-quasi-affine-base-change. Since B is affine, def-nagata-quasi-affine-morphism
   makes W times_A B itself quasi-affine.
4. Embed W times_A B as a quasi-compact open of an affine scheme. By step 2, L is an
   open subscheme of that affine scheme, with the same restricted structure sheaf.
   Its given quasi-compactness makes L quasi-affine as well. -/
theorem qc_open_pullback_quasi_affine_enlargement
    {X A B : Scheme.{u}} (a : X ⟶ A) (b : B ⟶ A) [IsAffine A] [IsAffine B]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → U.toScheme.IsQuasiAffine)
    (L : (pullback a b).Opens) (hL : IsCompact (L : Set (pullback a b : Scheme.{u}))) :
    ∃ (n : ℕ) (Wj : Fin n → X.Opens) (W : X.Opens),
      (∀ j : Fin n, IsAffineOpen (Wj j)) ∧ W = iSup Wj ∧
      IsCompact (W : Set X) ∧
      Set.MapsTo (pullback.fst a b) (L : Set (pullback a b : Scheme.{u})) (W : Set X) ∧
      (pullback (W.ι ≫ a) b).IsQuasiAffine ∧ L.toScheme.IsQuasiAffine ∧
      IsQuasiAffineHom (pullback.snd (W.ι ≫ a) b) ∧
      ∃ i : L.toScheme ⟶ pullback (W.ι ≫ a) b,
        IsOpenImmersion i ∧
        i ≫ pullback.fst (W.ι ≫ a) b ≫ W.ι = L.ι ≫ pullback.fst a b ∧
        i ≫ pullback.snd (W.ι ≫ a) b = L.ι ≫ pullback.snd a b := by
  sorry

end AlgebraicGeometry
