/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurvePieces
public import WeilConjectures.TraceFormula.TraceClass

/-!

# Additivity of trace classes along the curve pieces

Let `(K, φ)` be a Weil object on `X` for `Φ`, `m ≥ 1`, `x` a rational point fixed by `Φ_m` and
`j : U ⟶ X` the open complement of `x`. The open–closed triangle
`K^U = j_! Lj^* K ⟶ K ⟶ K^Z = Rx_* Lx^* K ⟶` carries the coefficient maps `u^U`, `φ_m`, `u^Z` of
the graph correspondence `c_m = (𝟙, Φ_m)` (blueprint `d-curve-pieces`), and the trace classes are
additive (blueprint `prop-trf-trace-class-additivity`, item 2, the Frobenius case of
`lem-trf-trace-triangle-compatibility`):
```
Tr_{c_m}(φ_m) = Tr_{c_m}(u^Z) + Tr_{c_m}(u^U),
```
and so are the local terms. The proof in the blueprint is Varshavsky's filtered argument
(Prop. 1.5.10, after SGA 5, III 4.13): the trace map lifts to the filtered derived category, and
the trace of a filtered coefficient map is the sum of the traces of its graded pieces; it is not
a consequence of the three squares of the triangle commuting.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.withCoeff`: the correspondence with the same support and
  another coefficient object and map.

## Main statements

- `ProEtale.CondensedRing.WeilBoundedConstructible.traceClass_graph_eq_add`: additivity of the
  trace classes along the curve pieces.
- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_add`:
  additivity of the local terms.

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

namespace BorelMooreSection

variable {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom]

/-- The restriction of Borel–Moore sections along an open immersion is additive. -/
lemma restrict_add (j : U ⟶ X) [IsOpenImmersion j.left] (α β : BorelMooreSection ℓ X) :
    (α + β).restrict j = α.restrict j + β.restrict j := by
  simp only [restrict, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

omit [LocallyOfFiniteType U.hom] [IsSeparated U.hom] in
/-- Local terms are additive (blueprint `lem-trf-integration-linear`). -/
lemma localTerm_add (j : U ⟶ X) [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    [IsProper U.hom] (α β : BorelMooreSection ℓ X) :
    (α + β).localTerm j = α.localTerm j + β.localTerm j := by
  rw [localTerm, localTerm, localTerm, restrict_add, integral_add]

end BorelMooreSection

namespace Correspondence

variable {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The correspondence with the support `(c₁, c₂)` of `c` and another coefficient object `K'`
and coefficient map `u' : Lc₂^* K' ⟶ Rc₁^! K'` (blueprint `def-trf-correspondence`). -/
noncomputable def withCoeff (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K') :
    Correspondence ℓ K' where
  C := c.C
  c₁ := c.c₁
  c₂ := c.c₂
  u := u'

variable {c}

/-- A fixed locus of `c` is a fixed locus of every correspondence with the same support. -/
noncomputable def FixedLocus.withCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K') :
    (c.withCoeff K' u').FixedLocus where
  F := F.F
  ι := F.ι
  w := F.w
  isLimit := F.isLimit

/-- The trace class of the correspondence with the support of `c` and the coefficient map `u'`,
as a Borel–Moore section of the fixed locus `F` of `c`. -/
noncomputable def FixedLocus.traceClassWithCoeff (F : c.FixedLocus)
    (K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u' : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.c₂).obj K' ⟶
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.c₁).obj K') :
    BorelMooreSection ℓ F.F :=
  (c.withCoeff K' u').traceClass (F.withCoeff K' u')

end Correspondence

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) {U : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] (j : U ⟶ X)
  [IsOpenImmersion j.left]

/-- The graph correspondence `(𝟙, Φ_m)` with the closed curve piece `K^Z = Rx_* Lx^* K` and its
coefficient map `u^Z` (blueprint `d-curve-pieces`). -/
noncomputable abbrev closedPieceGraph (m : ℕ) (x : RationalPoint X)
    (hx : x ≫ frobeniusIterate Φ m = x) : Correspondence ℓ (K.closedPiece x) :=
  (K.graph m).withCoeff (K.closedPiece x) (K.closedPieceCoeff m x hx)

/-- The graph correspondence `(𝟙, Φ_m)` with the open curve piece `K^U = j_! Lj^* K` and its
coefficient map `u^U` (blueprint `d-curve-pieces`). -/
noncomputable abbrev openPieceGraph (m : ℕ) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m)) : Correspondence ℓ (K.openPiece j) :=
  (K.graph m).withCoeff (K.openPiece j)
    (K.openPieceCoeff j m sq ≫ (boundedConstructibleUpperShriekId ℓ X).inv.app _)

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
          (boundedConstructibleUpperShriekId ℓ X).inv.app _) :=
  sorry

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
