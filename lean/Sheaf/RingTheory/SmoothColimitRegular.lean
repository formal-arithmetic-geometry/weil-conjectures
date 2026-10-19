/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Sheaf.RingTheory.GRing
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat
import Sheaf.RingTheory.FilteredColimitAlgebrasTensorElementwise
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.NoetherianLocalColimitRegular

/-!
# Smooth filtered colimits with Noetherian fibres are regular

Source: Stacks Project, More on Algebra, Tag 07EP, lemma-colimit-smooth-regular;
the small filtered-category formulation of its directed-system statement
(blueprint: lem-per-smooth-colimit-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- A filtered colimit of smooth algebras is regular over its base if every fibre is
Noetherian. The fibre is Mathlib's `p.Fiber`, with the residue-field tensor factor first;
tensor symmetry identifies it with the tensor order in Stacks.

Source: Stacks Project, More on Algebra, Tag 07EP, lemma-colimit-smooth-regular
(blueprint: lem-per-smooth-colimit-regular).

Proof:
1. Each stage is flat by `lem-weil-pbc-smooth-ring-map-flat`. By
   `lem-weil-pbc-filtered-colimit-algebras-underlying-module`, the underlying module is
   the filtered colimit of these flat modules. Apply
   `lem-weil-pbc-filtered-colimit-flat-modules` to obtain flatness of the colimit.
2. Fix a prime p, put k = kappa(p), and let K/k be any finite purely inseparable
   extension (`def-weil-pbc-finite-purely-inseparable-extension`). The fibre F is
   Noetherian by hypothesis. Tensor cancellation
   (`lem-weil-pbc-tensor-cancel-base-change`) and symmetry identify K tensor_k F with
   C = K tensor_R B. A finite k-basis of K generates this tensor product over F, so
   `lem-weil-pbc-finite-algebra-noetherian` implies that C is Noetherian.
3. By `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` and symmetry, C is
   the colimit of C_j = K tensor_R A_j: every element and every finite family lifts
   to a common stage. The module-colimit factorization of a compatible ring cocone
   respects multiplication and one by computing at such a stage; it is the unique
   ring factorization (`def-weil-pbc-category-colimit`).
4. Each C_j is smooth over K by `lem-weil-pbc-smooth-ring-map-base-change-composition`.
   Its prime localizations are regular local rings by
   `lem-weil-pbc-smooth-over-field-regular-local`. At a prime q of C, apply
   `lem-weil-pbc-filtered-colimit-localization-at-prime`. The localized transition
   maps are local, since membership in each maximal ideal is membership of the
   numerator in the contracted prime. The apex C_q is Noetherian by
   `lem-weil-pbc-localization-noetherian`.
5. Use `lem-weil-pbc-filtered-category-directed-cofinal` to reindex by a nonempty
   directed set. Apply `lem-per-noetherian-local-colimit-regular` to conclude that
   C_q is regular local. Thus C is regular (`def-weil-regular-scheme`).
6. This holds for every finite purely inseparable K/k, so F is geometrically regular
   by `def-weil-pbc-g-ring`. For every p this gives the required geometric regularity;
   together with step 1 it is regularity of the algebra map. A zero fibre is
   Noetherian and has no prime localizations to check.
-/
theorem smooth_colimit_regular
    (R : Type u) [CommRing R] {J : Type v} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{v, u} R) [HasColimit A]
    (hsmooth : ∀ j : J, Algebra.Smooth R (A.obj j))
    (hfibre : ∀ (p : Ideal R) [p.IsPrime],
      IsNoetherianRing (p.Fiber (colimit A : CommAlgCat.{v, u} R))) :
    RingHom.IsRegular (algebraMap R (colimit A : CommAlgCat.{v, u} R)) := by
  sorry

end CommAlgCat
