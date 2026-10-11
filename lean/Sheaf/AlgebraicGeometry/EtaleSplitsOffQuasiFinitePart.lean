/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Étale splitting of the quasi-finite part

Source: Stacks Project, More on Morphisms, Lemma 37.41.6, Tag 02LP
(blueprint: lem-weil-pbc-etale-splits-off-quasi-finite-part).
-/

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stacks Project, Tag 02LP
(blueprint: lem-weil-pbc-etale-splits-off-quasi-finite-part).
A separated locally finite type morphism whose fibre has finitely many isolated points
admits an elementary étale neighbourhood on which a finite clopen part splits off and the
remaining fibre has no isolated points. If the original fibre is finite, the remaining
fibre is empty.

Proof outline from the DAG:
1. List all isolated points of `f.fiber s`, and their images in `X`
   (def-pc-scheme-fibre).
2. Apply lem-weil-pbc-etale-splits-off-isolated-points-technical (Stacks 02LN) to obtain
   an elementary étale neighbourhood and disjoint finite clopen pieces around those points,
   with a complementary open `W` whose fibre avoids them.
3. Take `V` to be the union of those pieces. It is finite over `U` by
   lem-weil-pbc-finite-coproduct and def-weil-finite-integral-morphism; the empty union is
   the empty finite scheme.
4. Identify the fibre of the base change at `u` with `f.fiber s`, using
   lem-weil-pbc-fibre-of-base-change, def-pc-fibre-product and def-weil-affine-spectrum:
   the induced residue-field map is an isomorphism.
5. The fibre of `W` is an open subscheme of that base-changed fibre by
   lem-weil-pbc-open-preimage-fibre-product and def-pc-fibre-product, and none of its points
   corresponds to an isolated point of `f.fiber s`.
6. An isolated point of this open subscheme would be isolated in the whole fibre,
   contradicting step 5.
7. If the original set-theoretic fibre is finite, the scheme fibre is finite and locally
   of finite type over its residue field (lem-weil-pbc-lft-base-change). On each affine
   chart its finite type algebra is Jacobson by
   lem-weil-pbc-finite-type-over-field-prime-intersection-maximal. Finitely many primes then
   are all maximal, so the chart, and hence the fibre, is discrete (Stacks 02NG).
8. Step 5 excludes every point of `W`'s fibre in this case; hence it is empty.
-/
theorem exists_etale_splits_off_quasiFinitePart
    {X S : Scheme.{v}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f] (s : S)
    (hfinite : Set.Finite {x : f.fiber s | IsOpen ({x} : Set (f.fiber s))}) :
    ∃ (U : Scheme.{v}) (φ : U ⟶ S) (u : U),
      Etale φ ∧ φ u = s ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (W V : (pullback φ f).Opens),
        IsCompl W V ∧ IsFinite (V.ι ≫ pullback.fst φ f) ∧
        (∀ w : (W.ι ≫ pullback.fst φ f).fiber u,
          ¬ IsOpen ({w} : Set ((W.ι ≫ pullback.fst φ f).fiber u))) ∧
        ((f ⁻¹' ({s} : Set S)).Finite → IsEmpty ((W.ι ≫ pullback.fst φ f).fiber u)) := by
  sorry

end AlgebraicGeometry
