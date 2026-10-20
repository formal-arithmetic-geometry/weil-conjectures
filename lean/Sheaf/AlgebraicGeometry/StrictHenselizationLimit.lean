/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.PointCount

/-! # Strict henselization as a limit of smaller-dimensional models

Source: Stacks Project, Tag 0F0U, and the blueprint node `lem-kun-0f0u`
(blueprint: lem-kun-0f0u).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem residue_tower_trdeg
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y U : Scheme.{u}} (f : Y ⟶ U) (g : U ⟶ Spec (.of K))
    (p : Y ⟶ Spec (.of L))
    (h : f ≫ g = p ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (v : Y)
    (ha : @Algebra.IsAlgebraic (U.residueField (f v)) (Y.residueField v) _ _
      ((f.residueFieldMap v).hom.toAlgebra)) :
    let := (p.residueFieldAlgebraMap v).toAlgebra
    let := (g.residueFieldAlgebraMap (f v)).toAlgebra
    Algebra.trdeg K L + Algebra.trdeg L (Y.residueField v) =
      Algebra.trdeg K (U.residueField (f v)) := by
  let := (p.residueFieldAlgebraMap v).toAlgebra
  let := (g.residueFieldAlgebraMap (f v)).toAlgebra
  let := ((f ≫ g).residueFieldAlgebraMap v).toAlgebra
  let := (f.residueFieldMap v).hom.toAlgebra
  have : IsScalarTower K (U.residueField (f v)) (Y.residueField v) :=
    IsScalarTower.of_algebraMap_eq' (Hom.residueFieldAlgebraMap_comp f g v)
  have : IsScalarTower K L (Y.residueField v) := by
    apply IsScalarTower.of_algebraMap_eq'
    change (f ≫ g).residueFieldAlgebraMap v =
      (p.residueFieldAlgebraMap v).comp (algebraMap K L)
    apply CommRingCat.hom_ext_iff.mp
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom ((f ≫ g).residueFieldAlgebraMap v)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L) ≫
        CommRingCat.ofHom (p.residueFieldAlgebraMap v))
    rw [Spec.map_comp, Hom.specMap_residueFieldAlgebraMap,
      Hom.specMap_residueFieldAlgebraMap, Category.assoc, h]
  have := ha
  have ht := trdeg_add_eq K (U.residueField (f v)) (A := Y.residueField v)
  rw [@trdeg_eq_zero (U.residueField (f v)) (Y.residueField v), add_zero] at ht
  exact (trdeg_add_eq K L (A := Y.residueField v)).trans ht.symm

private theorem model_dimension_lt
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X Y U : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [U.Over (Spec (.of K))]
    [LocallyOfFiniteType (U ↘ Spec (.of K))] [QuasiCompact (U ↘ Spec (.of K))]
    (p : Y ⟶ Spec (.of L)) [LocallyOfFiniteType p] [QuasiCompact p]
    (f : Y ⟶ U)
    (h : f ≫ (U ↘ Spec (.of K)) =
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (ha : ∀ v : Y, @Algebra.IsAlgebraic (U.residueField (f v)) (Y.residueField v) _ _
      ((f.residueFieldMap v).hom.toAlgebra))
    (hU : topologicalKrullDim U ≤ topologicalKrullDim X)
    (hL : 0 < Algebra.trdeg K L) (x : X) :
    topologicalKrullDim Y < topologicalKrullDim X := by
  classical
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact ne_bot_of_le_ne_bot (by simp) (Order.krullDim_nonneg (α :=
      TopologicalSpace.IrreducibleCloseds X))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of K))
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hbot
  obtain ⟨N, rfl⟩ := ENat.ne_top_iff_exists.mp
    (show n ≠ ⊤ from fun he ↦ topologicalKrullDim_ne_top_of_compactSpace
      (X ↘ Spec (.of K)) (hn.symm.trans (by rw [he]; rfl)))
  have hN : topologicalKrullDim X = (N : WithBot ℕ∞) := hn.symm
  by_contra hnot
  have hge : (N : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
    rw [← hN]
    exact le_of_not_gt hnot
  obtain ⟨v, hv⟩ := exists_le_topologicalKrullDim_closure_singleton hge
  let : Y.Over (Spec (.of L)) := ⟨p⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of L)) := inferInstanceAs (LocallyOfFiniteType p)
  have : QuasiCompact (Y ↘ Spec (.of L)) := inferInstanceAs (QuasiCompact p)
  obtain ⟨d, hd, htd⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg
    (K := L) (closure ({v} : Set Y)) isClosed_closure isIrreducible_singleton.closure
    v (subset_closure (by simp)) rfl
  obtain ⟨e, he, hte⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg
    (K := K) (closure ({f v} : Set U)) isClosed_closure isIrreducible_singleton.closure
    (f v) (subset_closure (by simp)) rfl
  have ht := residue_tower_trdeg f (U ↘ Spec (.of K)) p h v (ha v)
  change Algebra.trdeg K L + _ = _ at ht
  rw [htd, hte] at ht
  have hde : d + 1 ≤ e := by
    have hh : (d : Cardinal) + 1 ≤ (e : Cardinal) := by
      calc
        _ ≤ (d : Cardinal) + Algebra.trdeg K L :=
          add_le_add le_rfl (Cardinal.one_le_iff_pos.mpr hL)
        _ = _ := (add_comm _ _).trans ht
    exact_mod_cast hh
  have hdN : N ≤ d := by rw [hd] at hv; exact_mod_cast hv
  have heN : e ≤ N := by
    have hh := (topologicalKrullDim_subspace_le U (closure ({f v} : Set U))).trans hU
    rw [he, hN] at hh
    exact_mod_cast hh
  omega

/-- At a point of positive residue transcendence degree, the strict henselization is a
cofiltered inverse limit of affine finite-type schemes over a separably closed extension of
the base field, each of strictly smaller Krull dimension. The point `x` of the informal
statement is `s (IsLocalRing.closedPoint Ω)`; `s` specifies the geometric point needed to
define its strict henselization. The unused abbreviation `d = dim_x X` is omitted.

Source: Stacks Project, Tag 0F0U, positive-transcendence-degree consequence
(blueprint: lem-kun-0f0u).

Proof:
1. Apply `lem-kun-strict-local-algebraic-residue-models`. Its compatible maps to `Spec L`
   define the diagram over `L`. The forgetful functor from the slice over the affine
   neighbourhood preserves this limit, since the indexing category is cofiltered.
2. For a model point `v`, the residue-field map to its image in the neighbourhood and
   the two structural maps define compatible field towers. Algebraicity and
   `lem-kun-transcendence-degree-tower` give
   `trdeg_K L + trdeg_L κ(v) = trdeg_K κ(f(v))`.
   By `lem-sc-closed-irreducible-dimension-trdeg`, the last two degrees are the natural
   dimensions `d` and `e` of the respective point closures. Since `trdeg_K L > 0`,
   cardinal arithmetic gives `d + 1 ≤ e`; subspace monotonicity gives `e ≤ dim X`.
3. The point underlying `s` makes `dim X` nonnegative, and
   `lem-kun-dimension-finite-type` makes it a natural number `N`.
   If a model had dimension at least `N`, a chain of length `N` would have a generic
   end `v` whose closure has dimension `d ≥ N`. Step 2 gives `d + 1 ≤ e ≤ N`, a
   contradiction. Combine these bounds with the limit from step 1.
-/
theorem exists_strictHenselization_limit_smaller_dimension
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hpos : 0 < @Algebra.trdeg K (X.residueField (s (IsLocalRing.closedPoint Ω))) _ _
      (((X ↘ Spec (.of K)).residueFieldAlgebraMap
        (s (IsLocalRing.closedPoint Ω))).toAlgebra)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L),
      ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
        (D : I ⥤ Over (Spec (.of L))) (c : Cone (D ⋙ Over.forget (Spec (.of L)))),
        Nonempty (IsLimit c) ∧ Nonempty (strictHenselizationScheme s ≅ c.pt) ∧
        (∀ i : I, IsAffine (D.obj i).left ∧ LocallyOfFiniteType (D.obj i).hom ∧
          QuasiCompact (D.obj i).hom ∧
          topologicalKrullDim (D.obj i).left < topologicalKrullDim X) ∧
        (∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f).left) := by
  classical
  obtain ⟨U, hsU, hU, L, instL, instKL, instSep, htr,
    I, instI, instCo, D, p, c, e, hc, he, hmodels, hmaps, hres, hpcompat⟩ :=
    exists_strictLocal_algebraicResidue_models (K := K) X s
  let E : I ⥤ Over (Spec (.of L)) :=
    { obj i := Over.mk (p i)
      map a := Over.homMk (D.map a).left (hpcompat _ _ a)
      map_id i := by
        apply Over.OverMorphism.ext
        change (D.map (𝟙 i)).left = 𝟙 _
        exact congrArg (fun t : D.obj i ⟶ D.obj i ↦ t.left) (D.map_id i)
      map_comp {i j k} a b := by
        apply Over.OverMorphism.ext
        change (D.map (a ≫ b)).left = (D.map a).left ≫ (D.map b).left
        exact congrArg (fun t : D.obj i ⟶ D.obj k ↦ t.left) (D.map_comp a b) }
  let c' := (Over.forget U.toScheme).mapCone c
  have : IsConnected I := IsCofiltered.isConnected I
  have hc' : IsLimit c' := isLimitOfPreserves (Over.forget U.toScheme) hc.some
  refine ⟨L, instL, instKL, instSep, I, instI, instCo, E, c',
    ⟨hc'⟩, ⟨e⟩, ?_, hmaps⟩
  intro i
  obtain ⟨hne, haff, hft, hqc, hcomm⟩ := hmodels i
  refine ⟨haff, hft, hqc, ?_⟩
  have : IsAffine U.toScheme := hU
  have : LocallyOfFiniteType (p i) := hft
  have : QuasiCompact (p i) := hqc
  refine model_dimension_lt (K := K) (X := X) (U := U.toScheme) (p i)
    (D.obj i).hom ?_ (hres i) (topologicalKrullDim_subspace_le X U) ?_
    (s (IsLocalRing.closedPoint Ω))
  · simpa only [Scheme.Opens.ι_comp_over, Category.assoc] using hcomm
  · rwa [htr]

end AlgebraicGeometry.Scheme
