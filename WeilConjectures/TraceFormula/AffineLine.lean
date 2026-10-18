/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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
    {_ : Category CX} {jS : CU ⥤ CX} {jU : CX ⥤ CU} (adj : jS ⊣ jU) [IsIso adj.unit] {ΦU : CU ⥤ CU}
    {ΦY : CX ⥤ CX} (b : jS ⋙ ΦY ≅ ΦU ⋙ jS) (c : jU ⋙ ΦU ≅ ΦY ⋙ jU) (K : IsoAlgebra ΦU)
    (hL : adj.unit.app (ΦU.obj K.carrier) ≫ jU.map (b.inv.app K.carrier) =
      ΦU.map (adj.unit.app K.carrier) ≫ c.hom.app (jS.obj K.carrier)) :
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
        ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).inv.app M) =
    (boundedConstructibleUpperStar Λ ℓ gU).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app M) ≫
      θ.hom.app ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj M) := by
  subst hθ
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_inv]
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

variable (ℓ) in
/-- **The restriction of the Weil extension by zero** (blueprint `def-trf-weil-extension-zero`):
`j^* (j_! K, j_! φ ∘ b) ≅ (K, φ)` as Weil objects, through the unit of `j_! ⊣ Lj^*`. -/
noncomputable def weilUpperStarWeilOpenLowerShriekIso (sq : IsPullback ΦU j j ΦY)
    (hw : ΦU ≫ j = j ≫ ΦY) (K : WeilBoundedConstructible ℓ ΦU) :
    (weilUpperStar ℓ ΦU ΦY j hw).obj ((weilOpenLowerShriek ℓ sq).obj K) ≅ K :=
  -- UNFINISHED: `IsoAlgebra.mapOfNatIsoObjMapOfNatIsoObjIso` applied to
  -- `unit_comp_map_baseChangeIso_inv_of_eq`; the kernel check currently times out
  sorry

end Restriction

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

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
