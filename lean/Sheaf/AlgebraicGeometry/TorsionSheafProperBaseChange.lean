/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# Proper base change for torsion abelian sheaves

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
Detailed form of prop-weil-proet-finite-proper-base-change; Stacks Project, Tag 0DDE,
specialized to a sheaf in degree zero (blueprint: prop-weil-proet-finite-proper-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper base change for a torsion abelian sheaf, placed in degree zero.
Source: blueprint sec-proper-base-change/sk-thm-properbasechange, Detailed form;
Stacks Project, Tag 0DDE (blueprint: prop-weil-proet-finite-proper-base-change).

Proof plan: Put `K = F[0]` using `DerivedCategory.Plus.singleFunctor`.
Its degree-zero cohomology is `F`, and its other cohomology sheaves are zero,
so it is bounded below with lower bound zero and has torsion cohomology:
`F` is torsion by hypothesis, and every section of the zero sheaf is killed by one
(def-weil-pbc-derived-categories, def-weil-pbc-etale-sheaves).
The chosen pullback identification makes the square Cartesian, and `f` is proper.
Apply thm-weil-pbc-bounded-below, namely `Etale.isIso_baseChange_of_isProper`,
to this square and `K`, with no restriction on `g`.
The morphism denoted by the exchange at `F` is by definition the component at `F[0]`
of `derivedBaseChangeMapPlus` (def-weil-pbc-derived-exchange); this is the same
canonical transformation as `Etale.baseChange`. Thus the resulting isomorphism is
precisely the asserted exchange morphism, not merely an isomorphism of its endpoints. -/
theorem isIso_derivedBaseChangeMapPlus_app_torsionSheaf_of_isProper
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsProper f] (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) := by
  have hs : IsPullback g' f' f g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  rw [← baseChange_eq_derivedBaseChangeMapPlus]
  refine isIso_baseChange_of_isProper hs _ fun n ↦ ?_
  by_cases hn : n = 0
  · subst n
    have : Scheme.IsTorsionSheaf ((𝟭 _).obj F) :=
      (Scheme.isTorsionSheaf_iff_isTorsion F).2 hF
    exact Scheme.IsTorsionSheaf.of_iso
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app F).symm
  · have hz : Limits.IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n hn
      · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 n hn
    apply (Scheme.isTorsionSheaf_iff_isTorsion _).2
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro U x
    have hx := Functor.map_isZero
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ AddCommGrpCat.{u + 1}).obj U) hz
    have hs : Subsingleton _ := AddCommGrpCat.isZero_iff_subsingleton.mp hx
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨1, Nat.one_pos, ?_⟩
    simpa using hs.elim x 0

end AlgebraicGeometry.Etale
