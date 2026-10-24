/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ClosedPieceTriangle
public import WeilConjectures.TraceFormula.OpenPieceTriangle
public import WeilConjectures.TraceFormula.PieceVanishing
public import WeilConjectures.TraceFormula.TraceClassTriangle

/-!

# Additivity of trace classes along the pieces of a fixed point

Let `h : X ⟶ X` be an endomorphism, `x` a rational point fixed by `h` and `j : U ⟶ X` the open
complement of `x`. A coefficient map `v : Lh^* K ⟶ K` of the graph correspondence `(𝟙, h)`
induces coefficient maps `u^U` on `K^U = j_! Lj^* K` and `u^Z` on `K^Z = Rx_* Lx^* K` which form,
with `v`, a morphism of the open–closed triangle `K^U ⟶ K ⟶ K^Z ⟶`, and the trace classes are
additive (blueprint `prop-trf-trace-class-additivity`, `lem-trf-trace-triangle-compatibility`):
```
Tr_{(𝟙, h)}(v) = Tr_{(𝟙, h)}(u^Z) + Tr_{(𝟙, h)}(u^U).
```
This is `Correspondence.traceClass_eq_add_of_distTriang` for the open–closed triangle; the corner
morphism groups vanish by `WeilConjectures.TraceFormula.PieceVanishing` since `x` is fixed by
`h`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.traceClass_ofGraph_eq_add`: item 1 of
  `prop-trf-trace-class-additivity` for the graph of `h` and `Z = {x}`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.traceClass_graph_eq_add`: item 2, the curve
  pieces of a Weil object.
- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_add`: the local
  terms.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace Correspondence

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

/-- **Additivity of trace classes along the pieces of a fixed point** (blueprint
`prop-trf-trace-class-additivity`, item 1, and `lem-trf-trace-triangle-compatibility`, for the
graph correspondence `(𝟙, h)` and the `c`-invariant closed subscheme `Z = {x}` of a rational
point fixed by `h`; Varshavsky, Prop. 1.5.10 after SGA 5, III 4.13): the trace class of
`v : Lh^* K ⟶ K` is the sum of the trace classes of the induced coefficient maps
`u^Z = [x, x]_! v_x` on `K^Z = Rx_* Lx^* K` and `u^U = [j]_! (v|_U)` on `K^U = j_! Lj^* K`.
No invertibility of `v` is required. -/
theorem traceClass_ofGraph_eq_add (F : (ofGraph K h v).FixedLocus) :
    (ofGraph K h v).traceClass F =
      F.traceClassWithCoeff _ (graphClosedPieceCoeff K v hx) +
        F.traceClassWithCoeff _ (graphOpenPieceCoeff K v hx ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _) := by
  have hjx := (isCompl_range_pointComplι x).disjoint
  obtain ⟨δ, hT⟩ := exists_distTriang_pointComplι_rationalPoint x K
  rw [add_comm]
  refine (ofGraph K h v).traceClass_eq_add_of_distTriang F hT _ _ ?_ ?_
    (eq_zero_of_lowerShriek_graph (pointComplι x) x hjx _ _ h hx)
    (eq_zero_of_externalProduct_openPiece (pointComplι x) x hjx _ _ K _)
    (eq_zero_of_externalProduct_closedPiece (pointComplι x) x hjx _ _ K _)
    (eq_zero_of_externalProduct_shift_to_diag (pointComplι x) x hjx _ _)
  · change _ ≫ v ≫ _ = (_ ≫ _) ≫ _
    rw [← (boundedConstructibleUpperShriekId ℓ X).inv.naturality, ← Category.assoc,
      ← graphOpenPieceCoeff_comp_counit, Category.assoc, Category.assoc]
    rfl
  · change _ = (v ≫ _) ≫ _
    rw [upperStar_map_unit_comp_graphClosedPieceCoeff, Category.assoc,
      ← (boundedConstructibleUpperShriekId ℓ X).inv.naturality]
    rfl

end Correspondence

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) {U : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
  [IsOpenImmersion j.left]

/-- **Additivity of trace classes along the curve pieces** (blueprint
`prop-trf-trace-class-additivity`, item 2; `lem-trf-trace-triangle-compatibility` for the
Frobenius graph; `sk-i-additivity`): for a rational point `x` fixed by `Φ_m`, `m ≥ 1`, with
open complement `j : U ⟶ X` such that `Φ_{m,U} ≫ j = j ≫ Φ_m` is cartesian, the trace class of
the graph correspondence `(𝟙, Φ_m)` with coefficient `φ_m` is the sum of the trace classes with
the coefficients `u^Z` of `K^Z` and `u^U` of `K^U`. -/
theorem traceClass_graph_eq_add (m : ℕ) (hm : 1 ≤ m) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m))
    (hcompl : IsCompl (Set.range j.left.base) (Set.range x.left.base))
    (F : (K.graph m).FixedLocus) :
    (K.graph m).traceClass F =
      F.traceClassWithCoeff _ (K.closedPieceCoeff m x hx) +
        F.traceClassWithCoeff _ (K.openPieceCoeff j m sq ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_openImmersionLowerShriek_lowerStar j x hcompl K.carrier
  rw [add_comm]
  refine (K.graph m).traceClass_eq_add_of_distTriang F hT _ _ ?_ ?_
    (eq_zero_of_lowerShriek_graph j x hcompl.disjoint _ _ _ hx)
    (eq_zero_of_externalProduct_openPiece j x hcompl.disjoint _ _ K.carrier _)
    (eq_zero_of_externalProduct_closedPiece j x hcompl.disjoint _ _ K.carrier _)
    (eq_zero_of_externalProduct_shift_to_diag j x hcompl.disjoint _ _)
  · change _ ≫ (K.iterateStr m).hom ≫ _ = (_ ≫ _) ≫ _
    rw [← (boundedConstructibleUpperShriekId ℓ X).inv.naturality, ← Category.assoc,
      ← openPieceCoeff_comp_counit, Category.assoc, Category.assoc]
    rfl
  · change _ = ((K.iterateStr m).hom ≫ _) ≫ _
    rw [upperStar_map_unit_comp_closedPieceCoeff, Category.assoc,
      ← (boundedConstructibleUpperShriekId ℓ X).inv.naturality]
    rfl

/-- **Additivity of local terms along the curve pieces** (blueprint
`prop-trf-trace-class-additivity`, item 2): for every open and closed subscheme `B` of the fixed
locus, proper over `s`, `LT_B(φ_m) = LT_B(u^Z) + LT_B(u^U)`. -/
theorem localTerm_traceClass_graph_eq_add (m : ℕ) (hm : 1 ≤ m) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m))
    (hcompl : IsCompl (Set.range j.left.base) (Set.range x.left.base))
    (F : (K.graph m).FixedLocus) {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (jB : B ⟶ F.F) [IsOpenImmersion jB.left] [IsClosedImmersion jB.left] :
    ((K.graph m).traceClass F).localTerm jB =
      (F.traceClassWithCoeff _ (K.closedPieceCoeff m x hx)).localTerm jB +
        (F.traceClassWithCoeff _ (K.openPieceCoeff j m sq ≫
          (boundedConstructibleUpperShriekId ℓ X).inv.app _)).localTerm jB := by
  exact (congrArg (fun α ↦ BorelMooreSection.localTerm jB α)
    (K.traceClass_graph_eq_add j m hm x hx sq hcompl F)).trans
    (BorelMooreSection.localTerm_add jB _ _)

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
