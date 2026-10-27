/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.TraceFormula.AmpleSchemeTestLinePreparationDefs
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.TraceFormula.AmpleSchemeTestCharts
import Sheaf.TraceFormula.AmpleTestNormalizedLineDescent
import Sheaf.TraceFormula.SchemeChartQCSeparatedPresheaf
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion

/-!
# Line-module preparation on an arbitrary scheme test

Source: Stacks Project, Spaces Descent, Tag 0D3C, quasi-compact/separated preparation;
Morphisms, Tag 0893; Descent, Tags 03DX, 05VG and 03LC; Spaces Descent, Tags 04W8
and 060X (blueprint: lem-trf-ample-scheme-test-line-preparation).

`AmpleSchemeTestLinePreparation` bundles precisely the output on one scheme test.
The section equations fix the original restriction comparisons and the pulled-back
transitions, rather than allowing arbitrary isomorphisms of line modules.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The complete output for one arbitrary scheme test. All fibre products are specified
by their actual cartesian squares. The ordinary modules on the new charts are the
literal tensor pullbacks of the Zariski restrictions of `M`.
Source: Stacks, Spaces Descent, Tag 0D3C, preparation paragraph; Tags 04W8, 060X;
Morphisms, Tag 0893; Descent, Tags 03DX, 05VG and 03LC
(blueprint: lem-trf-ample-scheme-test-line-preparation). -/
structure AmpleSchemeTestLinePreparation {S : Scheme.{u}} {F Y : AlgebraicSpace S}
    (f : F ⟶ Y) (M : F.Modules) {I : Type v}
    (Yᵢ : I → Y.EtaleSite) (Fᵢ : I → F.EtaleSite)
    (pᵢ : ∀ i : I, (Fᵢ i).obj.left ⟶ (Yᵢ i).obj.left)
    (T : Over S) (h : yoneda.obj T ⟶ Y.obj.obj) where
  /-- The algebraic space `F ×_Y T`. -/
  X : AlgebraicSpace S
  /-- Its projection to `F`. -/
  toF : X ⟶ F
  /-- Its projection to the scheme test. -/
  toT : X.obj.obj ⟶ yoneda.obj T
  /-- The defining fibre-product square. -/
  cartesian : IsPullback toF.hom.hom toT f.hom.hom h
  /-- Scheme charts `Y_i ×_Y T` of `T`. -/
  Tᵢ : I → Over S
  /-- Their projections to the old charts. -/
  tY : ∀ i : I, Tᵢ i ⟶ (Yᵢ i).obj.left
  /-- Their projections to the test scheme. -/
  tT : ∀ i : I, Tᵢ i ⟶ T
  /-- The base-change squares of the base cover. -/
  baseCartesian : ∀ i : I, IsPullback (yoneda.map (tY i)) (yoneda.map (tT i))
    (Yᵢ i).obj.hom h
  /-- The new base cover is etale. -/
  baseEtale : ∀ i : I, Etale (tT i).left
  /-- Joint surjectivity on point classes, allowing field extension. -/
  baseSurjective : IsJointlySurjective (fun i : I ↦ yoneda.map (tT i))
  /-- Scheme charts `X ×_T T_i` of the new algebraic space. -/
  Xᵢ : I → X.EtaleSite
  /-- Their projections to the old source charts. -/
  xF : ∀ i : I, (Xᵢ i).obj.left ⟶ (Fᵢ i).obj.left
  /-- Their projections to the new base charts. -/
  xT : ∀ i : I, (Xᵢ i).obj.left ⟶ Tᵢ i
  /-- The square expressing `X_i = X ×_T T_i`. -/
  sourceCartesian : ∀ i : I, IsPullback (Xᵢ i).obj.hom (yoneda.map (xT i))
    toT (yoneda.map (tT i))
  /-- Compatibility of the projection to the original space. -/
  sourceToF : ∀ i : I, (Xᵢ i).obj.hom ≫ toF.hom.hom =
    yoneda.map (xF i) ≫ (Fᵢ i).obj.hom
  /-- The alternative scheme fibre product `F_i ×_{Y_i} T_i`. -/
  schemeCartesian : ∀ i : I, IsPullback (xF i) (xT i) (pᵢ i) (tY i)
  /-- The new source charts jointly cover `X`; etaleness is in `Xᵢ`. -/
  sourceSurjective : IsJointlySurjective (fun i : I ↦ (Xᵢ i).obj.hom)
  /-- Invertibility of the ordinary tensor pullbacks `N_i`. -/
  invertible : ∀ i : I,
    ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M)).IsInvertible
  /-- Ampleness on every inverse image of an affine open of the new base chart. -/
  ample : ∀ (i : I) (V : (Tᵢ i).left.Opens), IsAffineOpen V →
    ∃ hL : ((tensorPullback ((xT i).left ⁻¹ᵁ V).ι).obj
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))).IsInvertible,
      @IsAmple ((xT i).left ⁻¹ᵁ V).toScheme
        ((tensorPullback ((xT i).left ⁻¹ᵁ V).ι).obj
          ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))) hL
  /-- The original Zariski restrictions are ordinary invertible modules. -/
  original_invertible : ∀ i : I, ((F.schemeRestriction (Fᵢ i)).obj M).IsInvertible
  /-- Original ordinary/etale restriction identifications. -/
  original : ∀ i : I, OrdinaryEtaleIdentification F (Fᵢ i) M
    ((F.schemeRestriction (Fᵢ i)).obj M)
  /-- They are the canonical restriction identifications, normalized on all opens. -/
  original_normalized : ∀ i : I, AmpleTestRestrictionNormalized F (Fᵢ i) M (original i)
  /-- Represented original double overlaps. -/
  R : I → I → Over S
  /-- First overlap projection. -/
  r₁ : ∀ i j : I, R i j ⟶ (Fᵢ i).obj.left
  /-- Second overlap projection. -/
  r₂ : ∀ i j : I, R i j ⟶ (Fᵢ j).obj.left
  /-- The original overlap square. -/
  overlapCartesian : ∀ i j : I, IsPullback (yoneda.map (r₁ i j))
    (yoneda.map (r₂ i j)) (Fᵢ i).obj.hom (Fᵢ j).obj.hom
  /-- Original restriction transitions. -/
  α : ∀ i j : I,
    (tensorPullback (r₂ i j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M) ≅
      (tensorPullback (r₁ i j).left).obj ((F.schemeRestriction (Fᵢ i)).obj M)
  /-- The transitions are induced by restriction of the same `M`. -/
  original_transitions : AmpleTestInducesTransitions F Fᵢ R r₁ r₂
    (fun i ↦ (F.schemeRestriction (Fᵢ i)).obj M) α M original
  /-- Represented new double overlaps. -/
  D : I → I → Over S
  /-- First new overlap projection. -/
  d₁ : ∀ i j : I, D i j ⟶ (Xᵢ i).obj.left
  /-- Second new overlap projection. -/
  d₂ : ∀ i j : I, D i j ⟶ (Xᵢ j).obj.left
  /-- The new overlap square. -/
  newOverlapCartesian : ∀ i j : I, IsPullback (yoneda.map (d₁ i j))
    (yoneda.map (d₂ i j)) (Xᵢ i).obj.hom (Xᵢ j).obj.hom
  /-- The map of overlaps induced by the projections to the old charts. -/
  overlapMap : ∀ i j : I, D i j ⟶ R i j
  /-- Its first defining equation. -/
  overlapMap_fst : ∀ i j : I, overlapMap i j ≫ r₁ i j = d₁ i j ≫ xF i
  /-- Its second defining equation. -/
  overlapMap_snd : ∀ i j : I, overlapMap i j ≫ r₂ i j = d₂ i j ≫ xF j
  /-- Transitions of the literal tensor pullbacks `N_i`. -/
  β : ∀ i j : I,
    (tensorPullback (d₂ i j).left).obj
        ((tensorPullback (xF j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M)) ≅
      (tensorPullback (d₁ i j).left).obj
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
  /-- They are precisely pullbacks of the original restriction transitions. -/
  transition_eq : ∀ i j : I, β i j = ampleTestPulledTransition
    ((F.schemeRestriction (Fᵢ i)).obj M) ((F.schemeRestriction (Fᵢ j)).obj M)
    (r₁ i j) (r₂ i j) (α i j) (xF i) (xF j) (d₁ i j) (d₂ i j) (overlapMap i j)
    (overlapMap_fst i j) (overlapMap_snd i j)
  /-- The diagonal identity, including nontrivial self-overlaps. -/
  diagonal : ∀ (i : I) (d : (Xᵢ i).obj.left ⟶ D i i)
    (h₁ : d ≫ d₁ i i = 𝟙 _) (h₂ : d ≫ d₂ i i = 𝟙 _),
    atlasTransitionOver
      ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
      ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
      (d₁ i i) (d₂ i i) (β i i) d (𝟙 _) (𝟙 _) h₁ h₂ = Iso.refl _
  /-- The triple-overlap cocycle on every scheme test. -/
  cocycle : ∀ (i j k : I) (U : Over S)
    (a : U ⟶ (Xᵢ i).obj.left) (b : U ⟶ (Xᵢ j).obj.left) (c : U ⟶ (Xᵢ k).obj.left)
    (q₁₂ : U ⟶ D i j) (q₂₃ : U ⟶ D j k) (q₁₃ : U ⟶ D i k)
    (h₁₂₁ : q₁₂ ≫ d₁ i j = a) (h₁₂₂ : q₁₂ ≫ d₂ i j = b)
    (h₂₃₁ : q₂₃ ≫ d₁ j k = b) (h₂₃₂ : q₂₃ ≫ d₂ j k = c)
    (h₁₃₁ : q₁₃ ≫ d₁ i k = a) (h₁₃₂ : q₁₃ ≫ d₂ i k = c),
    atlasTransitionOver
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
        ((tensorPullback (xF k).left).obj ((F.schemeRestriction (Fᵢ k)).obj M))
        (d₁ i k) (d₂ i k) (β i k) q₁₃ a c h₁₃₁ h₁₃₂ =
      atlasTransitionOver
        ((tensorPullback (xF j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M))
        ((tensorPullback (xF k).left).obj ((F.schemeRestriction (Fᵢ k)).obj M))
        (d₁ j k) (d₂ j k) (β j k) q₂₃ b c h₂₃₁ h₂₃₂ ≪≫
      atlasTransitionOver
        ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
        ((tensorPullback (xF j).left).obj ((F.schemeRestriction (Fᵢ j)).obj M))
        (d₁ i j) (d₂ i j) (β i j) q₁₂ a b h₁₂₁ h₁₂₂
  /-- The descended small-etale module. -/
  N : X.Modules
  /-- It is a line module. -/
  isLine : X.IsLineModule N
  /-- The local identifications with the ordinary tensor pullbacks. -/
  identification : ∀ i : I, OrdinaryEtaleIdentification X (Xᵢ i) N
    ((tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
  /-- These identifications induce exactly the pulled-back transitions. -/
  induces : AmpleTestInducesTransitions X Xᵢ D d₁ d₂
    (fun i ↦ (tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
    β N identification
  /-- Uniqueness up to the unique isomorphism preserving all local identifications. -/
  unique : AmpleTestUniqueRealization X Xᵢ D d₁ d₂
    (fun i ↦ (tensorPullback (xF i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))
    β N identification
  /-- Quasi-compactness in the stipulated algebraic-space terminology. -/
  quasiCompact : IsQuasiCompactPresheafMap toT
  /-- Separatedness in the stipulated algebraic-space terminology. -/
  separated : IsSeparatedPresheafMap toT
  /-- For an etale test the projection to `F` is etale. -/
  etale_toF : IsEtale h → IsEtale toF.hom.hom

private theorem qcSeparated_of_relativeAmple {A B : Scheme.{u}}
    (g : A ⟶ B) (L : A.Modules) [L.IsInvertible]
    (hL : ∀ V : B.Opens, IsAffineOpen V →
      ∃ h : ((tensorPullback (g ⁻¹ᵁ V).ι).obj L).IsInvertible,
        @IsAmple (g ⁻¹ᵁ V).toScheme ((tensorPullback (g ⁻¹ᵁ V).ι).obj L) h) :
    QuasiCompact g ∧ IsSeparated g := by
  have hq : QuasiCompact g := quasiCompact_iff_forall_isAffineOpen.mpr (by
    intro V hV
    obtain ⟨_, ha⟩ := hL V hV
    exact isCompact_iff_compactSpace.mpr ha.1)
  have := hq
  exact ⟨hq, (isAmple_iff_canonical_section_proj_openImmersion g L).2.2 hL⟩

/-- Line-module preparation on every scheme test, without etaleness or flatness of the
map to `Y`. The result type retains all base-change squares, the actual tensor pullbacks,
the normalized restriction transitions, their diagonal and cocycle equations, effective
descent with uniqueness, quasi-compactness/separation, and the etale-test comparison.

Source: Stacks, Spaces Descent, Tag 0D3C, preparation paragraph; Morphisms, Tag 0893;
Descent, Tags 03DX, 05VG and 03LC; Spaces Descent, Tags 04W8 and 060X
(blueprint: lem-trf-ample-scheme-test-line-preparation).

Proof:
1. By lem-trf-space-fibre-products-etale-covers, form `X`, the scheme charts `T_i`,
   their etale covers, and the scheme charts `X_i`. The fibre-product universal
   property identifies `X_i` with `F_i ×_{Y_i} T_i` and represents all overlaps.
2. By lem-weil-pbc-invertible-pullback-tensor, the literal tensor pullbacks `N_i`
   are invertible. Apply lem-trf-scheme-relative-ample-base-change to obtain
   ampleness over every affine open of `T_i`; the test map is arbitrary.
3. By lem-trf-scheme-etale-invertible-comparison and
   lem-trf-etale-line-sections-normalized-comparisons, restrictions of `M` give
   the normalized ordinary identifications and transitions on `F_i ×_F F_j`.
   Full faithfulness gives their identities and cocycle. Use
   lem-sc-etale-qcoherent-presheaf-functorial for the identity and composition
   laws of tensor section restrictions, making the local identifications natural.
   On opens use
   lem-weil-pbc-open-immersion-module-pullback-restriction, exactly schemeRestriction.
4. Pull these transitions back to `X_i ×_X X_j`, with the existing normalized
   tensor composition maps. Both bracketings send a triple tensor to the same
   scalar product; functoriality preserves the diagonal identity and cocycle.
5. By lem-trf-algebraic-space-invertible-descent, descend to `N` with precisely
   these transitions. Full faithfulness gives the unique comparison preserving
   the identifications; its inverse glues the local inverses.
6. Absolute ampleness makes every inverse image of an affine open quasi-compact,
   so each `X_i → T_i` is quasi-compact (def-weil-finite-type-morphism).
   The final assertion of lem-trf-scheme-ample-canonical-proj-criterion gives separation.
7. Use lem-pc-quasi-compact-base-change and lem-weil-pbc-closed-immersion-base-change
   to interpret these scheme properties by the space definitions. Then descend them
   along the cover by lem-trf-space-qc-separated-etale-local, obtaining the two
   properties of `X → T` in the conclusion.
8. If `T → Y` is etale, so are `X → F` and `X_i → F_i`. Etale pullback compatibility
   in lem-trf-scheme-etale-invertible-comparison identifies the restriction of `M`
   with the same `N_i` and transitions. Full faithfulness of invertible descent
   glues exactly these comparisons and their inverses, uniquely. -/
theorem exists_ampleSchemeTestLinePreparation
    {S : Scheme.{u}} {F Y : AlgebraicSpace S} (f : F ⟶ Y)
    (M : F.Modules) (hM : F.IsLineModule M)
    (I : Type v) (Yᵢ : I → Y.EtaleSite) (Fᵢ : I → F.EtaleSite)
    (pᵢ : ∀ i : I, (Fᵢ i).obj.left ⟶ (Yᵢ i).obj.left)
    (hcover : IsJointlySurjective (fun i : I ↦ (Yᵢ i).obj.hom))
    (hpb : ∀ i : I, IsPullback (Fᵢ i).obj.hom (yoneda.map (pᵢ i))
      f.hom.hom (Yᵢ i).obj.hom)
    (hample : ∀ (i : I) (V : (Y.etaleForget.obj (Yᵢ i)).Opens), IsAffineOpen V →
      ∃ hL : ((tensorPullback ((pᵢ i).left ⁻¹ᵁ V).ι).obj
          ((F.schemeRestriction (Fᵢ i)).obj M)).IsInvertible,
        @IsAmple ((pᵢ i).left ⁻¹ᵁ V).toScheme
          ((tensorPullback ((pᵢ i).left ⁻¹ᵁ V).ι).obj
            ((F.schemeRestriction (Fᵢ i)).obj M)) hL)
    (T : Over S) (h : yoneda.obj T ⟶ Y.obj.obj) :
    ∃ P : AmpleSchemeTestLinePreparation f M Yᵢ Fᵢ pᵢ T h,
      IsEtale h → AmpleTestEtaleComparison F P.X P.toF M P.N Fᵢ P.Xᵢ P.xF
        P.original P.identification := by
  obtain ⟨C⟩ := exists_ampleSchemeTestCharts f I Yᵢ Fᵢ pᵢ hcover hpb T h
  let V : I → C.X.EtaleSite := fun i ↦
    ⟨CostructuredArrow.mk (C.source i), C.sourceEtale i⟩
  let a : ∀ i : I, (V i).obj.left ⟶ (Fᵢ i).obj.left :=
    fun i ↦ ampleTestChartFst (pᵢ i) (C.tY i)
  let b : ∀ i : I, (V i).obj.left ⟶ C.Tᵢ i :=
    fun i ↦ ampleTestChartSnd (pᵢ i) (C.tY i)
  obtain ⟨D⟩ := exists_ampleTestNormalizedLineData F C.X C.toF M hM Fᵢ V a
    C.sourceToF C.sourceSurjective
  have hinv : ∀ i : I,
      ((tensorPullback (a i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M)).IsInvertible := by
    intro i
    have := D.original_invertible i
    exact ((invertible_pullback_tensor (a i).left).1 _).2
  have hamp : ∀ (i : I) (W : (C.Tᵢ i).left.Opens), IsAffineOpen W →
      ∃ hL : ((tensorPullback ((b i).left ⁻¹ᵁ W).ι).obj
          ((tensorPullback (a i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))).IsInvertible,
        @IsAmple ((b i).left ⁻¹ᵁ W).toScheme
          ((tensorPullback ((b i).left ⁻¹ᵁ W).ι).obj
            ((tensorPullback (a i).left).obj ((F.schemeRestriction (Fᵢ i)).obj M))) hL := by
    intro i
    have := D.original_invertible i
    exact isAmple_on_affineOpens_tensorPullback_baseChange
      (pᵢ i).left (C.tY i).left ((F.schemeRestriction (Fᵢ i)).obj M) (hample i)
  have hlocal : ∀ i : I, QuasiCompact (b i).left ∧ IsSeparated (b i).left := by
    intro i
    have := hinv i
    exact qcSeparated_of_relativeAmple (b i).left _ (hamp i)
  obtain ⟨hq, hsep⟩ := qcSeparatedPresheafMap_of_schemeCharts C.X T C.toT I C.Tᵢ C.tT
    C.baseEtale C.baseSurjective V b C.sourceCartesian
    (fun i ↦ (hlocal i).1) (fun i ↦ (hlocal i).2)
  let P : AmpleSchemeTestLinePreparation f M Yᵢ Fᵢ pᵢ T h := {
    X := C.X
    toF := C.toF
    toT := C.toT
    cartesian := C.cartesian
    Tᵢ := C.Tᵢ
    tY := C.tY
    tT := C.tT
    baseCartesian := C.baseCartesian
    baseEtale := C.baseEtale
    baseSurjective := C.baseSurjective
    Xᵢ := V
    xF := a
    xT := b
    sourceCartesian := C.sourceCartesian
    sourceToF := C.sourceToF
    schemeCartesian := fun i ↦ IsPullback.of_map (Over.forget S)
      (Over.OverMorphism.ext Limits.pullback.condition)
      (IsPullback.of_hasPullback (pᵢ i).left (C.tY i).left)
    sourceSurjective := C.sourceSurjective
    invertible := hinv
    ample := hamp
    original_invertible := D.original_invertible
    original := D.original
    original_normalized := D.original_normalized
    R := D.R
    r₁ := D.r₁
    r₂ := D.r₂
    overlapCartesian := D.overlapCartesian
    α := D.α
    original_transitions := D.original_transitions
    D := D.D
    d₁ := D.d₁
    d₂ := D.d₂
    newOverlapCartesian := D.newOverlapCartesian
    overlapMap := D.overlapMap
    overlapMap_fst := D.overlapMap_fst
    overlapMap_snd := D.overlapMap_snd
    β := D.β
    transition_eq := D.transition_eq
    diagonal := D.diagonal
    cocycle := D.cocycle
    N := D.N
    isLine := D.isLine
    identification := D.identification
    induces := D.induces
    unique := D.unique
    quasiCompact := hq
    separated := hsep
    etale_toF := C.etale_toF }
  exact ⟨P, fun _ ↦ D.etaleComparison⟩

end AlgebraicGeometry.AlgebraicSpace
