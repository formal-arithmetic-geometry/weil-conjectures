/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.TraceFormula.Fibration
public import WeilConjectures.TraceFormula.ModelDecomposition
public import WeilConjectures.TraceFormula.OpenSquare
public import WeilConjectures.TraceFormula.TraceClass

/-!

# The trace formula for proper smooth curves and for the affine line

This file proves the trace formula for the affine line `𝔸¹_{k₀}` as in the blueprint
(`sk-thm-trace-formula`, second paragraph of the proof): the trace formula holds on the proper
smooth curve `ℙ¹_{k₀}` by the Lefschetz–Verdier formula, and it passes to the open subscheme
`𝔸¹_{k₀}` through the extension by zero.

## The trace formula on proper smooth curves

For a model `X` of a proper smooth curve `X₀` over `k₀`, the Lefschetz–Verdier formula for the
graph correspondence `c_m = (𝟙, Φ_m)` (`Correspondence.trace_globalOperator_eq_sum_localTerm`)
writes the trace of the global operator as the sum of the local terms over the clopen pieces of
the fixed locus, and each local term at a fixed point is the trace of the local Frobenius
(`WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`)
(`ProEtale.CondensedRing.WeilBoundedConstructible.traceFormula_of_isProper`). This uses the
decomposition of the fixed locus of `Φ_m` into its reduced rational points
(`ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_fixedPointDecomposition`).

## Sorried input

- `ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_fixedPointDecomposition`: the fixed
  scheme of the iterate `Φ_m` of the model Frobenius of a proper `X` is the finite disjoint union
  of its rational points, each a reduced open and closed point (it is étale over `k`, the graph
  of a Frobenius being transversal to the diagonal).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace WeilBoundedConstructible

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

/-- A decomposition of the fixed locus of the graph correspondence `c_m = (𝟙, Φ_m)` into its
rational points: a fixed locus `F` proper over `s` with finitely many pairwise disjoint open and
closed pieces `B_x ⟶ F` covering `F`, indexed by the fixed points `x` of `Φ_m`, the piece `B_x`
having underlying set the point `x`. -/
structure FixedPointDecomposition (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [Fintype (FixedPoint Φ m)] where
  /-- The fixed locus. -/
  F : (K.graph m).FixedLocus
  [isProper : IsProper F.F.hom]
  /-- The piece at a fixed point. -/
  B : FixedPoint Φ m → Over (Spec (.of k))
  [quasiCompact : ∀ x, QuasiCompact (B x).hom]
  [isProper_B : ∀ x, IsProper (B x).hom]
  /-- The inclusion of the piece at a fixed point. -/
  j : ∀ x, B x ⟶ F.F
  [isOpenImmersion : ∀ x, IsOpenImmersion (j x).left]
  [isClosedImmersion : ∀ x, IsClosedImmersion (j x).left]
  disjoint : Pairwise fun x x' ↦ Disjoint (Set.range (j x).left.base)
    (Set.range (j x').left.base)
  cover : ⋃ x, Set.range (j x).left.base = Set.univ
  range_eq (x : FixedPoint Φ m) : Set.range (j x).left.base =
    {(K.fixedLocusPoint m F x.1 x.2).left.base (default : Spec (.of k))}

attribute [instance] FixedPointDecomposition.isProper FixedPointDecomposition.quasiCompact
  FixedPointDecomposition.isProper_B FixedPointDecomposition.isOpenImmersion
  FixedPointDecomposition.isClosedImmersion

set_option linter.overlappingInstances false in
/-- **The fixed locus of a Frobenius is the disjoint union of its rational points**: for the model
Frobenius `Φ` of a proper `X = X₀ ×_{k₀} k` and `m ≥ 1`, the fixed scheme of `Φ_m` (the
equalizer of `𝟙` and `Φ_m`) is étale over `k`, the graph of a Frobenius being transversal to the
diagonal; it is therefore the finite disjoint union of the reduced points `Spec k` given by the
fixed rational points. This is a geometric input of the trace formula (Lang), stated here and
not proved. -/
theorem nonempty_fixedPointDecomposition [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p) [IsProper X.hom] (K : WeilBoundedConstructible ℓ Φ) {m : ℕ}
    (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)] : Nonempty (K.FixedPointDecomposition m) :=
  sorry

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper smooth curve** (blueprint `sk-thm-trace-formula`, through
`sk-p-frob` and `sk-p-local`): for the model Frobenius `Φ` of a proper curve `X = X₀ ×_{k₀} k`
smooth over `k`, the trace of the global operator is the sum of the local terms of the graph
correspondence `c_m` along the fixed points (Lefschetz–Verdier), and each local term is the trace
of the local Frobenius. -/
theorem traceFormula_of_isProper [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p) (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m) :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    K.TraceFormula m := by
  have := hΦ.isFinite m
  have := hΦ.isUniversalHomeomorphism m
  intro _ _ _
  obtain ⟨D⟩ := nonempty_fixedPointDecomposition hΦ K hm
  rw [globalOperator_eq_correspondenceGlobalOperator,
    Correspondence.trace_globalOperator_eq_sum_localTerm _ D.F D.B D.j D.disjoint D.cover]
  exact Finset.sum_congr rfl fun x _ ↦
    localTerm_traceClass_graph_eq_trace hΦ K hm D.F x.1 x.2 (D.j x) (D.range_eq x)

variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {j : U ⟶ X} {i : Z ⟶ X}

/-- **The trace formula passes to an open subscheme** (blueprint `sk-thm-trace-formula`): for an
open subscheme `j : U ⟶ X` with closed complement `i : Z ⟶ X`, both stable under the Frobenius,
the trace formulas for `K` and for the restriction `K|_Z` in degree `m` give the trace formula
for the restriction `K|_U`, by additivity of the compactly supported Frobenius and of the sums
over the fixed points. -/
theorem traceFormula_open_of_isCompl [IsSepClosed k] {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z}
    [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base)) (hj : ΦU ≫ j = j ≫ Φ)
    (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [IsFinite (frobeniusIterate Φ m).left] [IsUniversalHomeomorphism (frobeniusIterate Φ m).left]
    [IsFinite (frobeniusIterate ΦU m).left]
    [IsUniversalHomeomorphism (frobeniusIterate ΦU m).left]
    [IsFinite (frobeniusIterate ΦZ m).left]
    [IsUniversalHomeomorphism (frobeniusIterate ΦZ m).left] [Finite (FixedPoint ΦZ m)]
    (hX : K.TraceFormula m) (hZ : ((weilUpperStar ℓ ΦZ Φ i hi).obj K).TraceFormula m) :
    ((weilUpperStar ℓ ΦU Φ j hj).obj K).TraceFormula m := by
  intro _ dKU _
  let e := fixedPointSumEquiv hcompl hj hi m
  let _ : Fintype (FixedPoint ΦZ m) := Fintype.ofFinite _
  let _ : Fintype (FixedPoint Φ m) := Fintype.ofEquiv _ e
  let dK := (nonempty_hasRightDual_compactCohomology K.carrier).some
  let dKZ := (nonempty_hasRightDual_compactCohomology
    ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier).some
  let dKUm := (nonempty_hasRightDual_compactCohomology
    (((weilUpperStar ℓ ΦU Φ j hj).obj K).iterate m).carrier).some
  let dKZm := (nonempty_hasRightDual_compactCohomology
    (((weilUpperStar ℓ ΦZ Φ i hi).obj K).iterate m).carrier).some
  let dKm := (nonempty_hasRightDual_compactCohomology (K.iterate m).carrier).some
  let dTU := (nonempty_hasRightDual_compactCohomology
    ((weilUpperStar ℓ (frobeniusIterate ΦU m) (frobeniusIterate Φ m) j
      (frobeniusIterate_comp_of_comp hj m)).obj (K.iterate m)).carrier).some
  let dTZ := (nonempty_hasRightDual_compactCohomology
    ((weilUpperStar ℓ (frobeniusIterate ΦZ m) (frobeniusIterate Φ m) i
      (frobeniusIterate_comp_of_comp hi m)).obj (K.iterate m)).carrier).some
  let _ : ∀ x : RationalPoint X, HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier) :=
    fun x ↦ (nonempty_hasRightDual_stalk _ x).some
  let _ : ∀ z : RationalPoint Z, HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj
        ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier) :=
    fun z ↦ (nonempty_hasRightDual_stalk _ z).some
  have hXeq : trace (K.globalOperator m) =
      ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2) :=
    hX
  have hZeq : trace (((weilUpperStar ℓ ΦZ Φ i hi).obj K).globalOperator m) =
      ∑ z : FixedPoint ΦZ m,
        trace (((weilUpperStar ℓ ΦZ Φ i hi).obj K).stalkFrobenius m z.1 z.2) :=
    hZ
  rw [trace_globalOperator_eq K m (hK := dK) (hKm := dKm),
    trace_compactFrobenius_eq_add hcompl (frobeniusIterate_comp_of_comp hj m)
      (frobeniusIterate_comp_of_comp hi m) (K.iterate m),
    ← trace_globalOperator_weilUpperStar hj K m (hKU := dKU) (hKUm := dKUm) (hT := dTU),
    ← trace_globalOperator_weilUpperStar hi K m (hKU := dKZ) (hKUm := dKZm) (hT := dTZ),
    ← e.sum_comp, Fintype.sum_sum_type, hZeq] at hXeq
  have hU' := Finset.sum_congr rfl fun (y : FixedPoint ΦU m) (_ : y ∈ Finset.univ) ↦
    trace_stalkFrobenius_weilUpperStar hj K m y.1 y.2
  have hZ' := Finset.sum_congr rfl fun (z : FixedPoint ΦZ m) (_ : z ∈ Finset.univ) ↦
    trace_stalkFrobenius_weilUpperStar hi K m z.1 z.2
  rw [hZ'] at hXeq
  rw [hU']
  exact add_right_cancel hXeq

end WeilBoundedConstructible

/-! ### The restriction of the extension by zero -/

section Restriction

/-- The abstract shape of the restriction of the Weil extension by zero: for `j_! ⊣ j^*` with
invertible unit, an exchange `b : j_! ⋙ Φ_Y^* ≅ Φ_U^* ⋙ j_!` whose restriction is the comparison
`c : j^* ⋙ Φ_U^* ≅ Φ_Y^* ⋙ j^*`, the inverse of the unit intertwines the structure maps. -/
lemma restrict_extendByZero_aux {CU CX : Type*} [Category CU] [Category CX] {jS : CU ⥤ CX}
    {jU : CX ⥤ CU} (adj : jS ⊣ jU) [IsIso adj.unit] {ΦU : CU ⥤ CU} {ΦY : CX ⥤ CX}
    (b : jS ⋙ ΦY ≅ ΦU ⋙ jS) (c : jU ⋙ ΦU ≅ ΦY ⋙ jU) (K : CU)
    (hL : adj.unit.app (ΦU.obj K) ≫ jU.map (b.inv.app K) =
      ΦU.map (adj.unit.app K) ≫ c.hom.app (jS.obj K)) (φ : ΦU.obj K ⟶ K) :
    ΦU.map (inv (adj.unit.app K)) ≫ φ =
      (c.hom.app (jS.obj K) ≫ jU.map (b.hom.app K ≫ jS.map φ)) ≫ inv (adj.unit.app K) := by
  have hn := (asIso adj.unit).inv.naturality φ
  simp only [Functor.comp_map, Functor.id_map, asIso_inv, NatIso.isIso_inv_app] at hn
  have h2 : c.hom.app (jS.obj K) ≫ jU.map (b.hom.app K) ≫ inv (adj.unit.app (ΦU.obj K)) =
      ΦU.map (inv (adj.unit.app K)) := by
    rw [← cancel_epi (ΦU.map (adj.unit.app K)), ← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, ← reassoc_of% hL, ← jU.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [Functor.map_comp, Category.assoc, Category.assoc, hn, ← reassoc_of% h2]

/-- **The restriction of an extension, abstractly**: for `j_! ⊣ j^*` with invertible unit and
commutation isomorphisms `b : j_! ⋙ F_Y ≅ F_U ⋙ j_!`, `c : j^* ⋙ F_U ≅ F_Y ⋙ j^*` such that the
restriction of `b⁻¹` is `c` up to the units, the unit is an isomorphism of algebras
`j^* (j_! K) ≅ K` for every algebra `K` with invertible structure morphism. -/
noncomputable def IsoAlgebra.mapOfNatIsoObjMapOfNatIsoObjIso {CU CX : Type*} {_ : Category CU}
    {_ : Category CX} {jS : CU ⥤ CX} {jU : CX ⥤ CU} {ΦU : CU ⥤ CU} {ΦY : CX ⥤ CX}
    (b : jS ⋙ ΦY ≅ ΦU ⋙ jS) (c : jU ⋙ ΦU ≅ ΦY ⋙ jU) (K : IsoAlgebra ΦU) {adj : jS ⊣ jU}
    (hL : adj.unit.app (ΦU.obj K.carrier) ≫ jU.map (b.inv.app K.carrier) =
      ΦU.map (adj.unit.app K.carrier) ≫ c.hom.app (jS.obj K.carrier)) [IsIso adj.unit] :
    (IsoAlgebra.mapOfNatIso c).obj ((IsoAlgebra.mapOfNatIso b).obj K) ≅ K :=
  IsoAlgebra.isoMk (asIso (adj.unit.app K.carrier)).symm (by
    rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom, IsoAlgebra.mapOfNatIso_obj_str,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, IsoAlgebra.mapOfNatIso_obj_str,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    exact restrict_extendByZero_aux adj b c K.carrier hL K.str.hom)

variable {U Y : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {ΦU : U ⟶ U} {ΦY : Y ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j.left]

/-- The inverse of `a⁻¹ ≫ eqToHom h ≫ b` is `b⁻¹ ≫ eqToHom h' ≫ a`. -/
lemma Iso.symm_trans_eqToIso_trans_symm {C : Type*} [Category C] {S T P P' : C} (a : P ≅ S)
    (h : P = P') (b : P' ≅ T) (h' : P' = P) :
    (a.symm ≪≫ eqToIso h ≪≫ b).symm = b.symm ≪≫ eqToIso h' ≪≫ a := by
  ext
  simp

omit [IsOpenImmersion j.left] in
/-- The Frobenius comparison of the pullback along `j` is the pullback comparison of the flipped
cartesian square. -/
lemma weilUpperStarComparison_eq_flip (sq : IsPullback ΦU j j ΦY) (hw : ΦU ≫ j = j ≫ ΦY) :
    weilUpperStarComparison ℓ ΦU ΦY j hw =
      boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq.flip :=
  Iso.symm_trans_eqToIso_trans_symm _ _ _ _

/-- The restriction of the inverse of the open-square exchange `b_g` is any isomorphism `θ` equal
to the pullback comparison of the flipped square, up to the units. -/
lemma unit_comp_map_baseChangeIso_inv_of_eq {U' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} {_ : MonObj Λ} {_ : IsCommMonObj Λ}
    {g : Y' ⟶ Y} {j' : U' ⟶ Y'} {gU : U' ⟶ U} [IsOpenImmersion j'.left]
    {sq : IsPullback gU j' j g}
    (θ : boundedConstructibleUpperStar Λ ℓ j ⋙ boundedConstructibleUpperStar Λ ℓ gU ≅
      boundedConstructibleUpperStar Λ ℓ g ⋙ boundedConstructibleUpperStar Λ ℓ j')
    (hθ : θ = boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip)
    (M : Dᵇc(U.left)⟦Λ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').unit.app
        ((boundedConstructibleUpperStar Λ ℓ gU).obj M) ≫
      (boundedConstructibleUpperStar Λ ℓ j').map
        ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).inv.app M) =
    (boundedConstructibleUpperStar Λ ℓ gU).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app M) ≫
      θ.hom.app ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj M) := by
  subst hθ
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_inv]
  exact Adjunction.unit_comp_map_exchangeLeft_app _ _ _ M

omit [IsOpenImmersion j.left] in
/-- The derived pullback of Weil objects is the functor on algebras of the Frobenius comparison. -/
lemma weilUpperStar_eq_mapOfNatIso (hw : ΦU ≫ j = j ≫ ΦY) :
    weilUpperStar ℓ ΦU ΦY j hw = IsoAlgebra.mapOfNatIso (weilUpperStarComparison ℓ ΦU ΦY j hw) :=
  rfl

/-- The Weil extension by zero is the functor on algebras of the open-square exchange. -/
lemma weilOpenLowerShriek_eq_mapOfNatIso (sq : IsPullback ΦU j j ΦY) :
    weilOpenLowerShriek ℓ sq = IsoAlgebra.mapOfNatIso (openSquareExchange ℓ sq) :=
  rfl

/-- **The degree one trace formula passes along the restriction of the Weil extension by zero**
(blueprint `def-trf-weil-extension-zero`): the unit of `j_! ⊣ Lj^*` is an isomorphism of Weil
objects `j^* (j_! K) ≅ K` (`IsoAlgebra.mapOfNatIsoObjMapOfNatIsoObjIso` applied to
`unit_comp_map_baseChangeIso_inv_of_eq` and `weilUpperStarComparison_eq_flip`), so the degree one
trace formula for `j^* (j_! K)` gives the one for `K`.

UNFINISHED gap of this subsection: the isomorphism of Weil objects is mathematically assembled
above, but identifying its source with `(weilUpperStar …).obj ((weilOpenLowerShriek …).obj K)`
times out (in elaboration and in the kernel) on the instance arguments of the two descriptions of
the categories of Weil objects, which differ by abstracted proofs. -/
theorem traceFormulaOne_of_weilUpperStar_weilOpenLowerShriek (sq : IsPullback ΦU j j ΦY)
    (hw : ΦU ≫ j = j ≫ ΦY) [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
    (K : WeilBoundedConstructible ℓ ΦU)
    (h : ((weilUpperStar ℓ ΦU ΦY j hw).obj ((weilOpenLowerShriek ℓ sq).obj K)).TraceFormulaOne) :
    K.TraceFormulaOne :=
  sorry

end Restriction

/-! ### Open subschemes -/

namespace WeilBoundedConstructible

/-- The trace of an endomorphism of a zero object vanishes: `X ⊗ Xᘁ` is a zero object, since
maps into it correspond to maps into `X`. -/
lemma _root_.CategoryTheory.MonoidalCategory.trace_eq_zero_of_isZero {C : Type*} [Category C]
    [HasZeroMorphisms C] [MonoidalCategory C] [BraidedCategory C] {X : C} [HasRightDual X]
    (hX : IsZero X) (f : X ⟶ X) : trace f = 0 := by
  have h : IsZero (X ⊗ Xᘁ) := (IsZero.iff_id_eq_zero _).2
    ((tensorRightHomEquiv (X ⊗ Xᘁ) X Xᘁ X).symm.injective (hX.eq_of_tgt _ _))
  rw [trace, h.eq_of_tgt (η_ X Xᘁ) 0, zero_comp]

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The degree one trace formula holds for a Weil object with zero underlying complex: both
sides vanish. -/
theorem traceFormulaOne_of_isZero {Φ : X ⟶ X} [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
    (K : WeilBoundedConstructible ℓ Φ) (hK : IsZero K.carrier) : K.TraceFormulaOne := by
  intro _ _ _
  rw [trace_eq_zero_of_isZero (Functor.map_isZero _ hK), Finset.sum_eq_zero fun x _ ↦
    trace_eq_zero_of_isZero (Functor.map_isZero _ hK) _]

/-- The stalk Frobenius of the restriction of a Weil object along `j : U ⟶ X` at a point `u`
fixed by `Φ_U` has the trace of the stalk Frobenius of the Weil object at `u ≫ j`. -/
lemma trace_weilStalkFrobenius_weilUpperStar {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] {Φ : X ⟶ X}
    {ΦU : U ⟶ U} {j : U ⟶ X} (hj : ΦU ≫ j = j ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    (u : RationalPoint U) (hu : u ≫ ΦU = u)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ u).obj
      ((weilUpperStar ℓ ΦU Φ j hj).obj K).carrier)]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (u ≫ j)).obj
      K.carrier)] :
    trace (((weilUpperStar ℓ ΦU Φ j hj).obj K).weilStalkFrobenius u hu) =
      trace (K.weilStalkFrobenius (u ≫ j)
        (by rw [Category.assoc, ← hj, ← Category.assoc, hu])) := by
  have hu1 : u ≫ frobeniusIterate ΦU 1 = u := by
    rw [frobeniusIterate_one]
    exact hu
  rw [← trace_stalkFrobenius_one _ u hu1 hu, trace_stalkFrobenius_weilUpperStar,
    trace_stalkFrobenius_one]

variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left]
  [IsClosedImmersion i.left]

/-- **Additivity read backwards, for the open piece**: for an open subscheme `j : U ⟶ X` with
closed complement `i : Z ⟶ X`, both stable under the Frobenius, the degree one trace formula for
a Weil object on `X` and for its restriction to `Z` gives the degree one trace formula for its
restriction to `U`. -/
theorem traceFormulaOne_of_isCompl_right [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ) (K : WeilBoundedConstructible ℓ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left]
    [IsUniversalHomeomorphism ΦU.left] [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
    [Finite {z : RationalPoint Z // z ≫ ΦZ = z}] (hX : K.TraceFormulaOne)
    (hZ : ((weilUpperStar ℓ ΦZ Φ i hi).obj K).TraceFormulaOne) :
    ((weilUpperStar ℓ ΦU Φ j hj).obj K).TraceFormulaOne := by
  classical
  intro _ _ _
  let eU : {u : RationalPoint U // u ≫ ΦU = u} ≃ FixedPoint ΦU 1 :=
    Equiv.subtypeEquivRight fun u ↦ by rw [frobeniusIterate_one]
  let eZ : {z : RationalPoint Z // z ≫ ΦZ = z} ≃ FixedPoint ΦZ 1 :=
    Equiv.subtypeEquivRight fun z ↦ by rw [frobeniusIterate_one]
  let eX : FixedPoint Φ 1 ≃ {x : RationalPoint X // x ≫ Φ = x} :=
    Equiv.subtypeEquivRight fun x ↦ by rw [frobeniusIterate_one]
  let e : {u : RationalPoint U // u ≫ ΦU = u} ⊕ {z : RationalPoint Z // z ≫ ΦZ = z} ≃
      {x : RationalPoint X // x ≫ Φ = x} :=
    (Equiv.sumCongr eU eZ).trans ((fixedPointSumEquiv hcompl hj hi 1).trans eX)
  let _ := Fintype.ofFinite {z : RationalPoint Z // z ≫ ΦZ = z}
  let _ : Fintype {x : RationalPoint X // x ≫ Φ = x} := Fintype.ofEquiv _ e
  let _ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier) := (nonempty_hasRightDual_compactCohomology _).some
  let _ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Z)).obj
        ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier) :=
    (nonempty_hasRightDual_compactCohomology _).some
  let _ (x : RationalPoint X) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier) :=
    (nonempty_hasRightDual_stalk _ x).some
  let _ (z : RationalPoint Z) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj
        ((weilUpperStar ℓ ΦZ Φ i hi).obj K).carrier) :=
    (nonempty_hasRightDual_stalk _ z).some
  have hXeq : trace K.compactFrobenius = ∑ x : {x : RationalPoint X // x ≫ Φ = x},
      trace (K.weilStalkFrobenius x.1 x.2) := hX
  have hZeq : trace ((weilUpperStar ℓ ΦZ Φ i hi).obj K).compactFrobenius =
      ∑ z : {z : RationalPoint Z // z ≫ ΦZ = z},
        trace (((weilUpperStar ℓ ΦZ Φ i hi).obj K).weilStalkFrobenius z.1 z.2) := hZ
  have hadd := trace_compactFrobenius_eq_add hcompl hj hi K
  rw [hXeq, hZeq, ← e.sum_comp, Fintype.sum_sum_type] at hadd
  refine add_right_cancel (hadd.symm.trans ?_)
  congr 1
  · exact Finset.sum_congr rfl fun u _ ↦
      (trace_weilStalkFrobenius_weilUpperStar hj K u.1 u.2).symm
  · exact Finset.sum_congr rfl fun z _ ↦
      (trace_weilStalkFrobenius_weilUpperStar hi K z.1 z.2).symm

/-- **The degree one trace formula on an open subscheme** (blueprint `sk-thm-trace-formula`,
second paragraph of the proof): for an open subscheme `j : U ⟶ X` with a cartesian Frobenius
square and closed complement `i : Z ⟶ X`, if the degree one trace formula holds for all Weil
objects on `X`, it holds for all Weil objects `K` on `U`: it holds for the extension by zero
`j_! K` on `X` and for its restriction to `Z`, which vanishes, hence for its restriction to `U`,
which is `K`. -/
theorem traceFormulaOne_of_isOpenImmersion [IsSepClosed k]
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (sq : IsPullback ΦU j j Φ) (hj : ΦU ≫ j = j ≫ Φ) (hi : ΦZ ≫ i = i ≫ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left]
    [IsUniversalHomeomorphism ΦU.left] [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
    [Finite {z : RationalPoint Z // z ≫ ΦZ = z}]
    (hX : ∀ L : WeilBoundedConstructible ℓ Φ, L.TraceFormulaOne)
    (K : WeilBoundedConstructible ℓ ΦU) : K.TraceFormulaOne := by
  refine traceFormulaOne_of_weilUpperStar_weilOpenLowerShriek sq hj K
    (traceFormulaOne_of_isCompl_right hcompl hj hi _ (hX _) (traceFormulaOne_of_isZero _ ?_))
  rw [weilUpperStar_obj_carrier, weilOpenLowerShriek_obj_carrier]
  exact isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek _ ℓ j i
    hcompl.disjoint K.carrier

end WeilBoundedConstructible

section Model

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

variable (ℓ) in
/-- **The trace formula for proper smooth curves** (blueprint `sk-thm-trace-formula`): for a
model `X₀` proper and smooth of relative dimension one over `k₀`. -/
theorem modelTraceFormula_of_isProper [IsAlgClosed k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k₀)) [IsProper f₀] [SmoothOfRelativeDimension 1 f₀] :
    ModelTraceFormula ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K m hm
  have : IsProper X.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hΦ.isPullback ‹_›
  have : SmoothOfRelativeDimension 1 X.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hΦ.isPullback ‹_›
  have := hΦ.isFinite m
  have := hΦ.isUniversalHomeomorphism m
  intro _ _ _
  exact WeilBoundedConstructible.traceFormula_of_isProper hΦ K hm

variable (ℓ) in
/-- **The degree one trace formula on an open subscheme of a model** (blueprint
`sk-thm-trace-formula`, second paragraph of the proof): for an open immersion `j₀ : U₀ ⟶ X₀` with
closed complement `i₀ : Z₀ ⟶ X₀`, the degree one trace formula over `X₀` gives the one over
`U₀`. A model `U` of `U₀` is the open subscheme `U₀ ×_{X₀} X` of the standard model
`X = X₀ ×_{k₀} k`, stable under the model Frobenius with a cartesian square, and
`WeilBoundedConstructible.traceFormulaOne_of_isOpenImmersion` applies. -/
theorem modelTraceFormulaOne_of_isOpenImmersion [IsAlgClosed k] {X₀ U₀ Z₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k₀)) [LocallyOfFiniteType f₀] [QuasiCompact f₀] [IsSeparated f₀]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀] [IsClosedImmersion i₀]
    (hcompl : IsCompl (Set.range j₀.base) (Set.range i₀.base))
    (h : ModelTraceFormulaOne ℓ (k := k) f₀) : ModelTraceFormulaOne ℓ (k := k) (j₀ ≫ f₀) := by
  intro U _ _ _ ΦU pU hΦU K
  obtain ⟨F₀, hF₀⟩ := Scheme.Hom.exists_isFrobenius f₀
  obtain ⟨FU, hFU, hpU⟩ := hΦU.exists_isFrobenius
  obtain ⟨FZ, hFZ⟩ := Scheme.Hom.exists_isFrobenius (i₀ ≫ f₀)
  have hFUc : FU ≫ j₀ = j₀ ≫ F₀ := (hFU.comp_eq_comp (j₀ ≫ f₀) hF₀ j₀).symm
  have hFZc : FZ ≫ i₀ = i₀ ≫ F₀ := (hFZ.comp_eq_comp (i₀ ≫ f₀) hF₀ i₀).symm
  let Φ : stdModel k f₀ ⟶ stdModel k f₀ := stdModelFrobenius f₀ (hF₀.comp_eq f₀)
  have hΦ : IsModelFrobenius Φ f₀ (pullback.fst _ _) := isModelFrobenius_stdModel f₀ hF₀
  have hpX : Φ.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F₀ := by
    simp [Φ, stdModelFrobenius]
  let j : U ⟶ stdModel k f₀ := Over.homMk (pullback.lift (pU ≫ j₀) U.hom (by
    rw [Category.assoc]
    exact hΦU.isPullback.w)) (pullback.lift_snd _ _ _)
  have hjs : j.left ≫ pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) =
      U.hom :=
    pullback.lift_snd _ _ _
  have hq : IsPullback pU j.left j₀
      (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
    rw [hjs]
    exact hΦU.isPullback
  have : IsOpenImmersion j.left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq ‹_›
  have hw : ΦU ≫ j = j ≫ Φ := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · simp [j, Φ, stdModelFrobenius, reassoc_of% hpU, hFUc]
    · simp [j, Φ, stdModelFrobenius]
  have sq : IsPullback ΦU j j Φ := by
    have := isPullback_frobeniusIterate_of_isOpenImmersion hΦ j₀ j hq hw 1
    rwa [frobeniusIterate_one, frobeniusIterate_one] at this
  have : LocallyOfFiniteType (modelBaseChange (X := stdModel k f₀) (pullback.fst _ _) i₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _ ≫ (stdModel k f₀).hom))
  have : QuasiCompact (modelBaseChange (X := stdModel k f₀) (pullback.fst _ _) i₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _ ≫ (stdModel k f₀).hom))
  have : IsSeparated (modelBaseChange (X := stdModel k f₀) (pullback.fst _ _) i₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _ ≫ (stdModel k f₀).hom))
  have : IsClosedImmersion
      (modelBaseChangeHom (X := stdModel k f₀) (pullback.fst _ _) i₀).left :=
    inferInstanceAs (IsClosedImmersion (pullback.snd _ _))
  have hΦZ := IsModelFrobenius.baseChange (X := stdModel k f₀) (Φ := Φ) _ i₀ hΦ hpX hFZc hFZ
  have := hΦ.isFinite_self
  have := hΦ.isUniversalHomeomorphism_self
  have := hΦU.isFinite_self
  have := hΦU.isUniversalHomeomorphism_self
  have := hΦZ.isFinite_self
  have := hΦZ.isUniversalHomeomorphism_self
  have := hΦZ.finite_fixedPoint (m := 1) one_ne_zero
  have : Finite {z : RationalPoint (modelBaseChange (X := stdModel k f₀) (pullback.fst _ _) i₀) //
      z ≫ modelBaseChangeEndo _ _ hpX hFZc = z} :=
    Finite.of_equiv (FixedPoint (modelBaseChangeEndo _ _ hpX hFZc) 1)
      (Equiv.subtypeEquivRight fun z ↦ by rw [frobeniusIterate_one])
  have hrange : Set.range j.left.base =
      (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))).base ⁻¹'
        Set.range j₀.base := by
    rw [← hq.flip.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (Scheme.Hom.surjective hq.flip.isoPullback.hom), Set.image_univ,
      Scheme.Pullback.range_fst]
    rfl
  have hrangeZ : Set.range
      (modelBaseChangeHom (X := stdModel k f₀) (pullback.fst _ _) i₀).left.base =
      (pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))).base ⁻¹'
        Set.range i₀.base :=
    Scheme.Pullback.range_snd _ _
  have hcomplX : IsCompl (Set.range j.left.base)
      (Set.range (modelBaseChangeHom (X := stdModel k f₀) (pullback.fst _ _) i₀).left.base) := by
    rw [hrange, hrangeZ]
    exact hcompl.preimage _
  intro _ _ _
  exact WeilBoundedConstructible.traceFormulaOne_of_isOpenImmersion hcomplX sq hw
    (modelBaseChangeEndo_comp _ _ hpX hFZc) (fun L ↦ h _ Φ _ hΦ L) K

variable (ℓ k₀) in
/-- **The degree one trace formula over the projective line** `ℙ¹_{k₀}`, a proper smooth curve
(`modelTraceFormula_of_isProper`). -/
theorem modelTraceFormulaOne_projectiveLine [IsAlgClosed k] :
    ModelTraceFormulaOne ℓ (k := k) (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)) :=
  ModelTraceFormulaOne.of_modelTraceFormula (modelTraceFormula_of_isProper ℓ _)

omit [Finite k₀] [Algebra k₀ k] in
/-- The affine chart of `ℙ¹_{k₀}` and the point at infinity are complementary. -/
lemma isCompl_range_affineChart_infinity :
    IsCompl (Set.range (ProjectiveLine.affineChart (Spec (.of k₀))).base)
      (Set.range (ProjectiveLine.infinity (Spec (.of k₀))).base) := by
  have h : Set.range (ProjectiveLine.infinity (Spec (.of k₀))).base =
      (Set.range (ProjectiveLine.affineChart (Spec (.of k₀))).base)ᶜ := by
    simpa using ProjectiveLine.range_infinity (Spec (.of k₀))
  rw [h]
  exact isCompl_compl

omit [Finite k₀] [Algebra k₀ k] in
/-- The point at infinity of `ℙ¹_{k₀}`, a section, is a closed immersion. -/
instance : IsClosedImmersion (ProjectiveLine.infinity (Spec (.of k₀))) :=
  isClosedImmersion_of_comp_eq_id _ _ ProjectiveLine.infinity_over

omit [Finite k₀] [Algebra k₀ k] in
/-- The affine line `Spec k₀[x]` is the affine chart `𝔸(PUnit; k₀)` of `ℙ¹_{k₀}`. -/
lemma specMvPolynomialFinOneIso_hom_comp :
    ((specIsoOfAlgEquiv (MvPolynomial.renameEquiv k₀ (Equiv.equivPUnit.{1, u + 1} (Fin 1)).symm))
      ≪≫ (AffineSpace.SpecIso PUnit.{u + 1} (.of k₀)).symm).hom ≫
        ProjectiveLine.affineChart (Spec (.of k₀)) ≫
          ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ProjectiveLine.affineChart_over,
    AffineSpace.SpecIso_inv_over]
  rw [← MvPolynomial.algebraMap_eq]
  exact specIsoOfAlgEquiv_hom_comp _

variable (ℓ k₀) in
/-- **The degree one trace formula over the affine line** `𝔸¹_{k₀} = Spec k₀[x]` (blueprint
`sk-thm-trace-formula`, second paragraph of the proof): the affine line is the complement of the
point at infinity in `ℙ¹_{k₀}` (`modelTraceFormulaOne_of_isOpenImmersion`,
`modelTraceFormulaOne_projectiveLine`). -/
theorem modelTraceFormulaOne_affineLine [IsAlgClosed k] :
    haveI : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    ModelTraceFormulaOne ℓ (k := k)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact ModelTraceFormulaOne.of_iso
    (modelTraceFormulaOne_of_isOpenImmersion ℓ _ _ _ isCompl_range_affineChart_infinity
      (modelTraceFormulaOne_projectiveLine ℓ k₀))
    _ specMvPolynomialFinOneIso_hom_comp

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
