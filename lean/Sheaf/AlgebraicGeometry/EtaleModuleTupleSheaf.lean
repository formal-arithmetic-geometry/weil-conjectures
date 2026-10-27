/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-!
# Compatible module tuples on an algebraic-space étale site

Source: Stacks Project, Sites, Tags 04TR (lemma-glue-sheaves) and 00W2
(lemma-limit-sheaf); Modules on Sites, Tags 03CT and 03CW
(blueprint: lem-trf-space-etale-module-tuple-sheaf).

The local sites are `Over T` for scheme objects `T` of the small étale site.
Products in that site represent fibre products over the algebraic space; a final
scheme object is never needed. The transition maps are arbitrary module morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre products of two étale scheme objects are again étale scheme objects.
Source: Stacks, Properties of Spaces, Tags 03EC and 03ED
(blueprint: lem-trf-space-etale-module-tuple-sheaf).
Proof: apply the scheme-source representability clause of
lem-trf-space-representable-etale-scheme-tests to the two charts. Its scheme pullback
has étale projections by base change, and its map to the space is étale by composition.
The representing pullback square gives exactly the binary-product universal property
in the small étale site. This is the existence of the fibre products displayed in the node. -/
theorem etaleSite_hasBinaryProducts {S : Scheme.{u}} (F : AlgebraicSpace S) :
    HasBinaryProducts F.EtaleSite := by
  have hp : ∀ (U V : F.EtaleSite), HasLimit (pair U V) := by
    intro U V
    obtain ⟨P, p, q, h, he⟩ := U.property V.obj.left V.obj.hom
    let r : P ⟶ U.obj.left := yoneda.preimage q
    have hr : yoneda.map r = q := yoneda.map_preimage q
    have hy : IsEtale (yoneda.map p) :=
      (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ p).2 he
    let W : F.EtaleSite := ⟨CostructuredArrow.mk (yoneda.map p ≫ V.obj.hom),
      isEtale_comp _ _ hy V.property⟩
    let p' : W ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk p rfl)
    let q' : W ⟶ U := ObjectProperty.homMk
      (CostructuredArrow.homMk r (by change yoneda.map r ≫ U.obj.hom = _; rw [hr]; exact h.w))
    let lift (Z : F.EtaleSite) (a : Z ⟶ U) (b : Z ⟶ V) : Z ⟶ W :=
      ObjectProperty.homMk (CostructuredArrow.homMk
        (yoneda.preimage (h.lift (yoneda.map a.hom.left) (yoneda.map b.hom.left)
          (by simp only [CostructuredArrow.w]))) (by
            dsimp [W]
            rw [yoneda.map_preimage, ← Category.assoc, h.lift_snd]
            exact CostructuredArrow.w b.hom))
    have hl (Z : F.EtaleSite) (a : Z ⟶ U) (b : Z ⟶ V) :
        yoneda.map (lift Z a b).hom.left =
          h.lift (yoneda.map a.hom.left) (yoneda.map b.hom.left)
            (by simp only [CostructuredArrow.w]) := yoneda.map_preimage _
    have hq (Z : F.EtaleSite) (a : Z ⟶ U) (b : Z ⟶ V) : lift Z a b ≫ q' = a := by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply yoneda.map_injective
      change yoneda.map ((lift Z a b).hom.left ≫ r) = _
      rw [Functor.map_comp, hl, hr, h.lift_fst]
    have hp' (Z : F.EtaleSite) (a : Z ⟶ U) (b : Z ⟶ V) : lift Z a b ≫ p' = b := by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply yoneda.map_injective
      change yoneda.map ((lift Z a b).hom.left ≫ p) = _
      rw [Functor.map_comp, hl, h.lift_snd]
    refine HasLimit.mk ⟨BinaryFan.mk q' p', BinaryFan.IsLimit.mk _
      (fun a b ↦ lift _ a b) (fun a b ↦ hq _ a b) (fun a b ↦ hp' _ a b) ?_⟩
    intro Z a b m hm₁ hm₂
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply yoneda.map_injective
    apply h.hom_ext
    · rw [← hr, ← Functor.map_comp]
      exact congrArg (fun k ↦ yoneda.map k.hom.left) (hm₁.trans (hq _ a b).symm)
    · rw [← Functor.map_comp]
      exact congrArg (fun k ↦ yoneda.map k.hom.left) (hm₂.trans (hp' _ a b).symm)
  have : ∀ {U V : F.EtaleSite}, HasLimit (pair U V) := fun {U V} ↦ hp U V
  exact hasBinaryProducts_of_hasLimit_pair F.EtaleSite

/-- The binary products supplied by the representable diagonal, chosen only through
 their universal property. Source: Stacks, Tags 03EC and 03ED
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable instance etaleSiteBinaryProducts {S : Scheme.{u}} (F : AlgebraicSpace S) :
    HasBinaryProducts F.EtaleSite := etaleSite_hasBinaryProducts F

/-- The sheaf `W ↦ L(T ×_F W)`, with scalars pulled back along the projection to `W`.
Its underlying sets are the node's sheaf `H_T`.
Source: Stacks, Sites, Tag 04TR, compatible-tuples formula; Tag 00WW
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleChartSheaf {S : Scheme.{u}} (F : AlgebraicSpace S)
    (T : F.EtaleSite)
    (L : ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over T)) :
    ringedSiteModules.{max (u + 1) v} F.structureSheaf :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver T)).obj L

/-- The sheaf `W ↦ L(T ×_F U ×_F W)`, viewed over the first chart `T`.
Its underlying sets are the node's sheaf `K_TU`.
Source: Stacks, Sites, Tags 04TR and 00WW
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleOverlapSheaf {S : Scheme.{u}} (F : AlgebraicSpace S)
    (T U : F.EtaleSite)
    (L : ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over T)) :
    ringedSiteModules.{max (u + 1) v} F.structureSheaf :=
  tupleChartSheaf F (T ⨯ U) ((F.etalePullbackMap prod.fst).obj L)

/-- The canonical arrow `(U ×_F W → T) → (T ×_F W → T)` induced by `p : U → T`.
The over-category adjunction constructs its commuting triangle, with underlying map
`(u,w) ↦ (p(u),w)`. Source: Stacks, Sites, Tag 04TR, section restrictions
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleRestriction {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T U : F.EtaleSite} (p : U ⟶ T) (W : F.EtaleSite) :
    (Over.map p).obj ((Over.star U).obj W) ⟶ (Over.star T).obj W :=
  (Over.forgetAdjStar T).homEquiv _ W prod.snd

/-- The product of the chart sheaves, with its canonical projections.
Source: Stacks, Sites, Tag 00W2, discrete diagrams
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleProduct {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i))) :=
  ∏ᶜ (fun i : I ↦ tupleChartSheaf F (V i) (L i))

/-- The product of the overlap sheaves, indexed by all ordered pairs, including diagonals.
Source: Stacks, Sites, Tag 00W2, discrete diagrams
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleOverlapProduct {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i))) :=
  ∏ᶜ (fun ij : I × I ↦ tupleOverlapSheaf F (V ij.1) (V ij.2) (L ij.1))

/-- The left coordinate `s_i` restricted to the triple fibre product.
Source: Stacks, Sites, Tag 04TR, compatible-tuples formula
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleLeftSection {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (W : F.EtaleSite)
    (s : ∀ i : I, (tupleChartSheaf F (V i) (L i)).val.obj (op W)) (i j : I) :
    (tupleOverlapSheaf F (V i) (V j) (L i)).val.obj (op W) :=
  (L i).val.map (tupleRestriction F (prod.fst : V i ⨯ V j ⟶ V i) W).op (s i)

/-- The right coordinate `a_ij(s_j restricted)` on the triple fibre product.
Source: Stacks, Sites, Tag 04TR, compatible-tuples formula, extended to module morphisms
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleRightSection {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (a : ∀ i j : I,
      (F.etalePullbackMap (prod.snd : V i ⨯ V j ⟶ V j)).obj (L j) ⟶
        (F.etalePullbackMap (prod.fst : V i ⨯ V j ⟶ V i)).obj (L i))
    (W : F.EtaleSite)
    (s : ∀ i : I, (tupleChartSheaf F (V i) (L i)).val.obj (op W)) (i j : I) :
    (tupleOverlapSheaf F (V i) (V j) (L i)).val.obj (op W) :=
  (a i j).val.app (op ((Over.star (V i ⨯ V j)).obj W))
    ((L j).val.map (tupleRestriction F (prod.snd : V i ⨯ V j ⟶ V j) W).op (s j))

/-- The literal set of compatible tuples at `W`, with no sheafification.
Source: Stacks, Sites, Tag 04TR, compatible-tuples formula
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def moduleTupleSections {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (a : ∀ i j : I,
      (F.etalePullbackMap (prod.snd : V i ⨯ V j ⟶ V j)).obj (L j) ⟶
        (F.etalePullbackMap (prod.fst : V i ⨯ V j ⟶ V i)).obj (L i))
    (W : F.EtaleSite) :=
  {s : ∀ i : I, (tupleChartSheaf F (V i) (L i)).val.obj (op W) //
    ∀ i j : I, tupleLeftSection F V L W s i j = tupleRightSection F V L a W s i j}

/-- The usual forgetful functor to sheaves of sets on this site, retaining section sets.
Source: Stacks, Sites, Section 00YR, property (alpha)
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleUnderlyingSets {S : Scheme.{u}} (F : AlgebraicSpace S) :
    ringedSiteModules.{max (u + 1) v} F.structureSheaf ⥤
      Sheaf F.etaleTopology (Type (max (u + 1) v)) :=
  SheafOfModules.toSheaf F.structureSheaf ⋙
    sheafCompose F.etaleTopology (forget AddCommGrpCat)

/-- Evaluation of the canonical chart-product projections as a literal tuple.
Source: Stacks, Sites, Tag 00W2, sectionwise products
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleProductCoordinates {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i : I) :
    (tupleChartSheaf F (V i) (L i)).val.obj (op W) :=
  (Pi.π (fun k : I ↦ tupleChartSheaf F (V k) (L k)) i).val.app (op W) s

/-- Evaluation of the overlap-product projections as an ordered-pair-indexed tuple.
Source: Stacks, Sites, Tag 00W2, sectionwise products
(blueprint: lem-trf-space-etale-module-tuple-sheaf). -/
noncomputable def tupleOverlapCoordinates {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (W : F.EtaleSite) (s : (tupleOverlapProduct F V L).val.obj (op W)) (ij : I × I) :
    (tupleOverlapSheaf F (V ij.1) (V ij.2) (L ij.1)).val.obj (op W) :=
  (Pi.π (fun kl : I × I ↦ tupleOverlapSheaf F (V kl.1) (V kl.2) (L kl.1)) ij).val.app
    (op W) s

private theorem module_product_coordinates_bijective
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {I : Type v}
    (H : I → SheafOfModules.{max (u + 1) v} R) (W : Cᵒᵖ) :
    Function.Bijective (fun (s : (∏ᶜ H).val.obj W) (i : I) ↦
      (Pi.π H i).val.app W s) := by
  let E := SheafOfModules.evaluation R W ⋙ forget _
  let h := isLimitOfHasProductOfPreservesLimit E H
  exact (h.conePointUniqueUpToIso
    (Types.productLimitCone (fun i ↦ E.obj (H i))).isLimit).toEquiv.bijective

private theorem tupleRestriction_snd {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T U : F.EtaleSite} (p : U ⟶ T) (W : F.EtaleSite) :
    (tupleRestriction F p W).left ≫ (prod.snd : T ⨯ W ⟶ W) = prod.snd := by
  have h := ((Over.forgetAdjStar T).homEquiv
    ((Over.map p).obj ((Over.star U).obj W)) W).symm_apply_apply
      (prod.snd : U ⨯ W ⟶ W)
  simpa only [tupleRestriction, Adjunction.homEquiv_counit, Over.forget_map,
    Over.forgetAdjStar_counit_app] using h

private theorem tupleRestriction_naturality {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T U : F.EtaleSite} (p : U ⟶ T) {W W' : F.EtaleSite} (r : W' ⟶ W) :
    (Over.map p).map ((Over.star U).map r) ≫ tupleRestriction F p W =
      tupleRestriction F p W' ≫ (Over.star T).map r := by
  apply ((Over.forgetAdjStar T).homEquiv
    ((Over.map p).obj ((Over.star U).obj W')) W).symm.injective
  simp only [Adjunction.homEquiv_counit, Over.forget_map,
    Over.forgetAdjStar_counit_app, Over.comp_left, Category.assoc,
    tupleRestriction_snd, Over.map_map_left, Over.star_map_left,
    prod.map_snd]
  rw [← Category.assoc, tupleRestriction_snd]

-- Keep the ring sheaf abstract while proving linearity of the restriction maps.
private noncomputable def moduleChartRestriction
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {T U : C} (p : U ⟶ T) (L : SheafOfModules.{max (u + 1) v} (R.over T))
    (ρ : ∀ W : C, (Over.map p).obj ((Over.star U).obj W) ⟶ (Over.star T).obj W)
    (hρ : ∀ {W W' : C} (r : W' ⟶ W),
      (Over.map p).map ((Over.star U).map r) ≫ ρ W = ρ W' ≫ (Over.star T).map r)
    (hsnd : ∀ W : C, (ρ W).left ≫ (prod.snd : T ⨯ W ⟶ W) = prod.snd) :
    (SheafOfModules.pushforward (SheafOfModules.pushforwardOver T)).obj L ⟶
      (SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj
        ((SheafOfModules.overMap R p).obj L) := by
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro W
    refine ModuleCat.ofHom
      (X := ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver T)).obj L).val.obj W)
      (Y := ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj
        ((SheafOfModules.overMap R p).obj L)).val.obj W)
      { toFun := fun s ↦ L.val.map (ρ W.unop).op s
        map_add' := fun s t ↦ (L.val.map (ρ W.unop).op).hom.map_add s t
        map_smul' := ?_ }
    intro b s
    have hb : R.obj.map (ρ W.unop).left.op
        (R.obj.map (prod.snd : T ⨯ W.unop ⟶ W.unop).op b) =
        R.obj.map (prod.snd : U ⨯ W.unop ⟶ W.unop).op b := by
      exact ConcreteCategory.congr_hom
        (show R.obj.map (prod.snd : T ⨯ W.unop ⟶ W.unop).op ≫
            R.obj.map (ρ W.unop).left.op =
              R.obj.map (prod.snd : U ⨯ W.unop ⟶ W.unop).op by
          rw [← Functor.map_comp, ← op_comp, hsnd]) b
    refine (L.val.map_smul (ρ W.unop).op
      (R.obj.map (prod.snd : T ⨯ W.unop ⟶ W.unop).op b) s).trans ?_
    exact congrArg (fun c ↦ c • L.val.map (ρ W.unop).op s) hb
  · intro W W' r
    ext s
    change L.val.map (ρ W'.unop).op
      (L.val.map ((Over.star T).map r.unop).op s) =
      L.val.map ((Over.map p).map ((Over.star U).map r.unop)).op
        (L.val.map (ρ W.unop).op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
      ← op_comp, ← op_comp, hρ]

private noncomputable def tupleChartRestriction {S : Scheme.{u}} (F : AlgebraicSpace S)
    {T U : F.EtaleSite} (p : U ⟶ T)
    (L : ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over T)) :
    tupleChartSheaf F T L ⟶ tupleChartSheaf F U ((F.etalePullbackMap p).obj L) :=
  moduleChartRestriction F.structureSheaf p L (tupleRestriction F p)
    (tupleRestriction_naturality F p) (tupleRestriction_snd F p)

-- Keep the source module abstract while proving the section formulas.
private theorem tuple_equiv_operations {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (a : ∀ i j : I,
      (F.etalePullbackMap (prod.snd : V i ⨯ V j ⟶ V j)).obj (L j) ⟶
        (F.etalePullbackMap (prod.fst : V i ⨯ V j ⟶ V i)).obj (L i))
    (M : ringedSiteModules.{max (u + 1) v} F.structureSheaf)
    (h : M ⟶ tupleProduct F V L)
    (e : ∀ W : F.EtaleSite,
      M.val.obj (op W) ≃ moduleTupleSections F V L a W)
    (he : ∀ (W : F.EtaleSite) (s : M.val.obj (op W)),
      (e W s).val = tupleProductCoordinates F V L W
        (h.val.app (op W) s)) :
    (∀ W : F.EtaleSite, (e W 0).val = 0) ∧
    (∀ (W : F.EtaleSite) (s t : M.val.obj (op W)),
      (e W (s + t)).val = (e W s).val + (e W t).val) ∧
    (∀ (W : F.EtaleSite) (s : M.val.obj (op W)),
      (e W (-s)).val = -(e W s).val) ∧
    (∀ (W : F.EtaleSite) (b : F.structurePresheaf.obj (op W))
        (s : M.val.obj (op W)),
      (e W (b • s)).val = fun i : I ↦
        @SMul.smul (F.structurePresheaf.obj (op (V i ⨯ W)))
          ((L i).val.obj (op ((Over.star (V i)).obj W))) inferInstance
          (F.structurePresheaf.map (prod.snd : V i ⨯ W ⟶ W).op b) ((e W s).val i)) ∧
    (∀ (W W' : F.EtaleSite) (r : W' ⟶ W)
        (s : M.val.obj (op W)),
      (e W' (M.val.map r.op s)).val = fun i : I ↦
        (tupleChartSheaf F (V i) (L i)).val.map r.op ((e W s).val i)) ∧
    (∀ (W W' : F.EtaleSite) (r : W' ⟶ W) (b : F.structurePresheaf.obj (op W))
        (s : M.val.obj (op W)),
      M.val.map r.op (b • s) =
        F.structurePresheaf.map r.op b • M.val.map r.op s) := by
  let H := fun k : I ↦ tupleChartSheaf F (V k) (L k)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W
    simp only [he]
    funext i
    exact (congrArg ((Pi.π H i).val.app (op W))
      (h.val.app (op W)).hom.map_zero).trans ((Pi.π H i).val.app (op W)).hom.map_zero
  · intro W s t
    simp only [he]
    funext i
    exact (congrArg ((Pi.π H i).val.app (op W))
      ((h.val.app (op W)).hom.map_add s t)).trans
        (((Pi.π H i).val.app (op W)).hom.map_add _ _)
  · intro W s
    simp only [he]
    funext i
    exact (congrArg ((Pi.π H i).val.app (op W))
      ((h.val.app (op W)).hom.map_neg s)).trans
        (((Pi.π H i).val.app (op W)).hom.map_neg _)
  · intro W b s
    simp only [he]
    funext i
    exact (congrArg ((Pi.π H i).val.app (op W))
      ((h.val.app (op W)).hom.map_smul b s)).trans
        (((Pi.π H i).val.app (op W)).hom.map_smul b _)
  · intro W W' r s
    simp only [he]
    funext i
    exact (congrArg ((Pi.π H i).val.app (op W'))
      (PresheafOfModules.naturality_apply h.val r.op s)).trans
        (PresheafOfModules.naturality_apply (Pi.π H i).val r.op _)
  · intro W W' r b s
    exact M.val.map_smul r.op b s

/-- Compatible tuples form the sectionwise equalizer module sheaf, with the displayed
operations and restrictions. No covering, invertibility, identity or cocycle is assumed.
The section equivalence is fixed by the equalizer inclusion and the product projections;
it does not replace the specified tuples by their sheafification.
Source: Stacks, Sites, Tag 04TR (lemma-glue-sheaves), omitted sheaf verification;
Tag 00W2 (lemma-limit-sheaf); Modules on Sites, Tags 03CT and 03CW
(blueprint: lem-trf-space-etale-module-tuple-sheaf).

Proof:
1. The representable diagonal and étale scheme-test lemma give the binary products
   used above. Base-changing coverings gives coverings by
   lem-trf-space-fibre-products-etale-covers. The functors `Over.star T` preserve the
   relevant fibre products, by their universal properties.
2. Apply lem-weil-pbc-site-continuous-pushforward-sheaf to these functors and to
   `Over.map` for the first overlap projection. This gives exactly `tupleChartSheaf`
   and `tupleOverlapSheaf`, with their indicated section restrictions.
3. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise the two products have their
   literal product section sets, expressed by the bijective coordinate maps below.
   Restriction functoriality makes the left coordinates natural. Naturality of each
   `a i j` makes the right coordinates natural. Hence these coordinates define the
   two morphisms `f` and `g` of sheaves, without any cocycle assumption.
4. The same sectionwise-limit lemma identifies their equalizer with precisely the
   subtype `moduleTupleSections`. The equivalence `e` is the tuple of projections
   of its equalizer inclusion, so also identifies the restrictions coordinatewise.
5. Zero, sums and negatives satisfy the equations by additivity of restrictions
   and transitions. For a scalar on W, its two pullbacks to an overlap agree;
   linearity of the transition proves that scalar multiples satisfy the equations.
   The module axioms therefore hold coordinatewise.
6. Semilinearity of each local restriction proves the last two formulas below.
   By lem-weil-pbc-algebraic-sheaf-iff-underlying-sets this module presheaf is a sheaf.
   Its underlying set cone is the equalizer cone, as asserted explicitly. For an
   empty family its section subtype is a singleton and the module sheaf is zero. -/
theorem exists_etale_module_tuple_sheaf {S : Scheme.{u}} (F : AlgebraicSpace S)
    {I : Type v} (V : I → F.EtaleSite)
    (L : ∀ i : I, ringedSiteModules.{max (u + 1) v} (F.structureSheaf.over (V i)))
    (a : ∀ i j : I,
      (F.etalePullbackMap (prod.snd : V i ⨯ V j ⟶ V j)).obj (L j) ⟶
        (F.etalePullbackMap (prod.fst : V i ⨯ V j ⟶ V i)).obj (L i)) :
    (∀ W : F.EtaleSite, Function.Bijective (tupleProductCoordinates F V L W) ∧
      Function.Bijective (tupleOverlapCoordinates F V L W)) ∧
    ∃ f g : tupleProduct F V L ⟶ tupleOverlapProduct F V L,
      (∀ (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i j : I),
        tupleOverlapCoordinates F V L W (f.val.app (op W) s) (i, j) =
          tupleLeftSection F V L W (tupleProductCoordinates F V L W s) i j) ∧
      (∀ (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i j : I),
        tupleOverlapCoordinates F V L W (g.val.app (op W) s) (i, j) =
          tupleRightSection F V L a W (tupleProductCoordinates F V L W s) i j) ∧
      Nonempty (IsLimit ((tupleUnderlyingSets F).mapCone
        (limit.cone (parallelPair f g)))) ∧
      ∃ e : ∀ W : F.EtaleSite,
          (equalizer f g).val.obj (op W) ≃ moduleTupleSections F V L a W,
        (∀ (W : F.EtaleSite) (s : (equalizer f g).val.obj (op W)),
          (e W s).val = tupleProductCoordinates F V L W
            ((equalizer.ι f g).val.app (op W) s)) ∧
        (∀ W : F.EtaleSite, (e W 0).val = 0) ∧
        (∀ (W : F.EtaleSite) (s t : (equalizer f g).val.obj (op W)),
          (e W (s + t)).val = (e W s).val + (e W t).val) ∧
        (∀ (W : F.EtaleSite) (s : (equalizer f g).val.obj (op W)),
          (e W (-s)).val = -(e W s).val) ∧
        (∀ (W : F.EtaleSite) (b : F.structurePresheaf.obj (op W))
            (s : (equalizer f g).val.obj (op W)),
          (e W (b • s)).val = fun i : I ↦
            @SMul.smul (F.structurePresheaf.obj (op (V i ⨯ W)))
              ((L i).val.obj (op ((Over.star (V i)).obj W))) inferInstance
              (F.structurePresheaf.map (prod.snd : V i ⨯ W ⟶ W).op b) ((e W s).val i)) ∧
        (∀ (W W' : F.EtaleSite) (r : W' ⟶ W)
            (s : (equalizer f g).val.obj (op W)),
          (e W' ((equalizer f g).val.map r.op s)).val = fun i : I ↦
            (tupleChartSheaf F (V i) (L i)).val.map r.op ((e W s).val i)) ∧
        (∀ (W W' : F.EtaleSite) (r : W' ⟶ W) (b : F.structurePresheaf.obj (op W))
            (s : (equalizer f g).val.obj (op W)),
          (equalizer f g).val.map r.op (b • s) =
            F.structurePresheaf.map r.op b • (equalizer f g).val.map r.op s) := by
  classical
  have hb (W : F.EtaleSite) :
      Function.Bijective (tupleProductCoordinates F V L W) ∧
        Function.Bijective (tupleOverlapCoordinates F V L W) := by
    exact ⟨module_product_coordinates_bijective F.structureSheaf _ (op W),
      module_product_coordinates_bijective F.structureSheaf _ (op W)⟩
  let left (ij : I × I) :
      tupleProduct F V L ⟶ tupleOverlapSheaf F (V ij.1) (V ij.2) (L ij.1) :=
    Pi.π _ ij.1 ≫ tupleChartRestriction F prod.fst (L ij.1)
  let right (ij : I × I) :
      tupleProduct F V L ⟶ tupleOverlapSheaf F (V ij.1) (V ij.2) (L ij.1) :=
    Pi.π _ ij.2 ≫ tupleChartRestriction F prod.snd (L ij.2) ≫
      (SheafOfModules.pushforward
        (SheafOfModules.pushforwardOver (V ij.1 ⨯ V ij.2))).map (a ij.1 ij.2)
  let f : tupleProduct F V L ⟶ tupleOverlapProduct F V L := Pi.lift left
  let g : tupleProduct F V L ⟶ tupleOverlapProduct F V L := Pi.lift right
  have hf (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i j : I) :
      tupleOverlapCoordinates F V L W (f.val.app (op W) s) (i, j) =
        tupleLeftSection F V L W (tupleProductCoordinates F V L W s) i j := by
    change (f ≫ Pi.π _ (i, j)).val.app (op W) s = _
    rw [Pi.lift_π]
    rfl
  have hg (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) (i j : I) :
      tupleOverlapCoordinates F V L W (g.val.app (op W) s) (i, j) =
        tupleRightSection F V L a W (tupleProductCoordinates F V L W s) i j := by
    change (g ≫ Pi.π _ (i, j)).val.app (op W) s = _
    rw [Pi.lift_π]
    rfl
  refine ⟨hb, f, g, hf, hg, ?_, ?_⟩
  · refine ⟨isLimitOfReflects (sheafToPresheaf _ _) ?_⟩
    change IsLimit (((SheafOfModules.toSheaf F.structureSheaf ⋙
      sheafToPresheaf _ AddCommGrpCat) ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat)).mapCone
          (limit.cone (parallelPair f g)))
    exact isLimitOfPreserves _ (limit.isLimit _)
  · let E (W : F.EtaleSite) := SheafOfModules.evaluation F.structureSheaf (op W) ⋙ forget _
    let e0 (W : F.EtaleSite) :=
      ((isLimitOfHasEqualizerOfPreservesLimit (E W) f g).conePointUniqueUpToIso
        (Types.equalizerLimit (g := (E W).map f) (h := (E W).map g)).isLimit).toEquiv
    have hc (W : F.EtaleSite) (s : (tupleProduct F V L).val.obj (op W)) :
        (E W).map f s = (E W).map g s ↔
          ∀ i j : I, tupleLeftSection F V L W (tupleProductCoordinates F V L W s) i j =
            tupleRightSection F V L a W (tupleProductCoordinates F V L W s) i j := by
      constructor
      · intro h i j
        rw [← hf, ← hg]
        exact congrArg (fun t ↦ tupleOverlapCoordinates F V L W t (i, j)) h
      · intro h
        apply (hb W).2.1
        funext ij
        exact (hf W s ij.1 ij.2).trans ((h ij.1 ij.2).trans (hg W s ij.1 ij.2).symm)
    let e (W : F.EtaleSite) :
        (equalizer f g).val.obj (op W) ≃ moduleTupleSections F V L a W :=
      (e0 W).trans ((Equiv.ofBijective _ (hb W).1).subtypeEquiv (hc W))
    have he (W : F.EtaleSite) (s : (equalizer f g).val.obj (op W)) :
        (e W s).val = tupleProductCoordinates F V L W
          ((equalizer.ι f g).val.app (op W) s) := rfl
    exact ⟨e, he, tuple_equiv_operations F V L a (equalizer f g) (equalizer.ι f g) e he⟩

end AlgebraicGeometry.AlgebraicSpace
