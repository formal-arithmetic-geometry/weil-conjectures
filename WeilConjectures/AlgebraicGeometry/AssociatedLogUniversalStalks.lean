/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.AlgebraicGeometry.AssociatedLogPresentation
import WeilConjectures.AlgebraicGeometry.PrelogPushoutLogAxiom
import WeilConjectures.AlgebraicGeometry.PrelogPushoutHomExtension
import WeilConjectures.AlgebraicGeometry.EtaleLogPresentationComparison

import WeilConjectures.AlgebraicGeometry.AssociatedLogStalkComparison
import WeilConjectures.AlgebraicGeometry.LogGlobalChartIsomorphism

/-!
# The associated-log construction and its comparisons

Source: ILO VI 1.1, printed p.69; Stacks Tags 00YR, 03PQ, 03PT, 03PU.
(blueprint: lem-trf-associated-log-universal-stalks).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def constantChartMonoid (X : Scheme.{max u v}) (R : Type v)
    [CommMonoid R] : X.Etaleᵒᵖ ⥤ CommMonCat.{max u v} :=
  (Functor.const X.Etaleᵒᵖ).obj (CommMonCat.of (ULift.{u, v} R))

private noncomputable def constantChartGamma {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (β : R →* Γ(X, ⊤)) :
    constantChartMonoid X R ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat where
  app W := CommMonCat.ofHom (associatedLogBetaLift.{u, v} β W.unop)
  naturality W V f := by
    ext r
    change V.unop.hom.appTop.hom (β r.down) =
      f.unop.left.appTop.hom (W.unop.hom.appTop.hom (β r.down))
    have hw : f.unop.left ≫ W.unop.hom = V.unop.hom := f.unop.w
    rw [← hw, Scheme.Hom.comp_appTop]
    rfl

private noncomputable def constantChartMap {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (K : EtaleLogStructure.{max u v} X)
    (c : ULift.{u, v} R →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    constantChartMonoid X R ⟶ K.monoidSheaf.obj where
  app W := CommMonCat.ofHom c ≫ K.monoidSheaf.obj.map
    (MorphismProperty.Over.homMk W.unop.hom (Category.comp_id W.unop.hom) :
      W.unop ⟶ Scheme.Etale.mk (𝟙 X)).op
  naturality := by
    intro W V f
    change CommMonCat.ofHom c ≫ K.monoidSheaf.obj.map _ =
      (CommMonCat.ofHom c ≫ K.monoidSheaf.obj.map _) ≫ K.monoidSheaf.obj.map f
    rw [Category.assoc, ← Functor.map_comp]
    congr 2
    apply Quiver.Hom.unop_inj
    ext
    exact f.unop.w.symm

private theorem constantChartMap_global {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (K : EtaleLogStructure.{max u v} X)
    (c : ULift.{u, v} R →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    ((constantChartMap K c).app (op (Scheme.Etale.mk (𝟙 X)))).hom = c := by
  have ht : (MorphismProperty.Over.homMk (𝟙 X) (Category.comp_id (𝟙 X)) :
      Scheme.Etale.mk (𝟙 X) ⟶ Scheme.Etale.mk (𝟙 X)) = 𝟙 _ := by ext; rfl
  change (CommMonCat.ofHom c ≫ K.monoidSheaf.obj.map
    (MorphismProperty.Over.homMk (𝟙 X) (Category.comp_id (𝟙 X)) :
      Scheme.Etale.mk (𝟙 X) ⟶ Scheme.Etale.mk (𝟙 X)).op).hom = c
  rw [ht, op_id, K.monoidSheaf.obj.map_id]
  rfl

private theorem constantChartMap_ext {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] {H : X.Etaleᵒᵖ ⥤ CommMonCat.{max u v}}
    {f g : constantChartMonoid X R ⟶ H}
    (h : f.app (op (Scheme.Etale.mk (𝟙 X))) = g.app (op (Scheme.Etale.mk (𝟙 X)))) :
    f = g := by
  ext W r
  let t : W.unop ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk W.unop.hom (Category.comp_id W.unop.hom)
  have hf := congrArg (fun z ↦ z r) (f.naturality t.op)
  have hg := congrArg (fun z ↦ z r) (g.naturality t.op)
  change f.app W r = H.map t.op (f.app _ r) at hf
  change g.app W r = H.map t.op (g.app _ r) at hg
  rw [hf, hg, h]

private theorem constantChartMap_compatible {X : Scheme.{max u v}} {R : Type v}
    [CommMonoid R] (β : R →* Γ(X, ⊤)) (K : EtaleLogStructure.{max u v} X)
    (c : ULift.{u, v} R →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hc : (K.alpha.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp c =
      associatedLogDownChart β) :
    constantChartMap K c ≫ K.alpha = constantChartGamma β := by
  ext W r
  let t : W.unop ⟶ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.homMk W.unop.hom (Category.comp_id W.unop.hom)
  have hn := congrArg (fun z ↦ z (c r)) (K.alpha.naturality t.op)
  change K.alpha.app W (K.monoidSheaf.obj.map t.op (c r)) = _
  change K.alpha.app W (K.monoidSheaf.obj.map t.op (c r)) =
    W.unop.hom.appTop.hom (K.alpha.app _ (c r)) at hn
  rw [hn]
  rw [show K.alpha.app _ (c r) = β r.down from congrArg (fun z ↦ z r) hc]
  rfl

private theorem associatedLog_exists_presentation (X : Scheme.{max u v})
    [IsLocallyNoetherian X] (R : Type v) [CommMonoid R] (β : R →* Γ(X, ⊤)) :
    ∃ (L : EtaleLogStructure.{max u v} X) (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj),
      IsAssociatedLogPresentation β L η := by
  obtain ⟨P, q, a, hq, hn, _hu, ha, ⟨H, η, hη⟩, hlog⟩ :=
    prelog_pushout_log_axiom.{max u v, max u v} X (constantChartMonoid X R) (constantChartGamma β)
  let k : associatedLogPresheaf β ⟶ P :=
    { app := fun W ↦ CommMonCat.ofHom
        ((divisorialChartCongruence (associatedLogBetaLift.{u, v} β W.unop).mrangeRestrict).lift
          (q W) (by
            have hh : Con.ker (q W) = divisorialChartCongruence
                (associatedLogBetaLift.{u, v} β W.unop).mrangeRestrict := (hq W).2
            exact hh.ge))
      naturality := by
        intro W V f
        ext z
        induction z using Con.induction_on with
        | H p =>
          rcases p with ⟨r, b⟩
          exact (hn W V f r b).symm }
  have hk (W : X.Etaleᵒᵖ) : Function.Bijective (k.app W) := by
    constructor
    · intro x y h
      induction x using Con.induction_on with
      | H x =>
        induction y using Con.induction_on with
        | H y =>
          apply (Con.eq _).mpr
          have hh : Con.ker (q W) = divisorialChartCongruence
              (associatedLogBetaLift.{u, v} β W.unop).mrangeRestrict := (hq W).2
          exact hh ▸ h
    · intro y
      obtain ⟨p, hp⟩ := (hq W).1 y
      exact ⟨(divisorialChartCongruence
        (associatedLogBetaLift.{u, v} β W.unop).mrangeRestrict).mk' p, hp⟩
  have (W : X.Etaleᵒᵖ) : IsIso (k.app W) :=
    (MulEquiv.ofBijective (k.app W).hom (hk W)).toCommMonCatIso.isIso_hom
  have : IsIso k := NatIso.isIso_of_isIso_app k
  obtain ⟨α, i, j, hα, ⟨L, hL⟩, _⟩ := hlog H η hη
  let Λ : EtaleLogStructure X :=
    { toEtalePrelogStructure := { monoidSheaf := H, alpha := α }
      reflectsUnits := hL ▸ L.reflectsUnits
      unitsBijective := hL ▸ L.unitsBijective }
  refine ⟨Λ, k ≫ η, ?_, ?_⟩
  · intro T
    constructor
    · intro f g h
      apply (hη T).1
      apply (cancel_epi k).mp
      simpa only [Category.assoc] using h
    · intro w
      obtain ⟨f, hf⟩ := (hη T).2 (inv k ≫ w)
      refine ⟨f, ?_⟩
      simp only [Category.assoc, hf, IsIso.hom_inv_id_assoc]
  · intro W r b
    have hh := congrArg (fun z ↦ z.app (op W)
      ((divisorialChartCongruence (associatedLogBetaLift.{u, v} β W).mrangeRestrict).mk'
        (ULift.up r, b))) (congrArg (fun z ↦ k ≫ z) hα)
    change α.app (op W) (η.app (op W) (q (op W) (ULift.up r, b))) = _
    change α.app (op W) (η.app (op W) (q (op W) (ULift.up r, b))) = _ at hh
    rw [hh]
    exact ha (op W) (ULift.up r) b

private theorem associatedLog_universal {X : Scheme.{max u v}} [IsLocallyNoetherian X]
    {R : Type v} [CommMonoid R] (β : R →* Γ(X, ⊤))
    (L : EtaleLogStructure.{max u v} X) (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj)
    (hη : IsAssociatedLogPresentation β L η) (K : EtaleLogStructure.{max u v} X) :
    Function.Injective
      (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (K := K)) ∧
    Set.range (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (K := K)) =
      associatedLogCompatibleRange K β := by
  let i := prelogPresentationIota (constantChartGamma β) L.monoidSheaf η
  have hiα : i ≫ L.alpha = constantChartGamma β := by
    ext W r
    change L.alpha.app W (η.app W
      ((divisorialChartCongruence (P := ULift.{u, v} R)
        (associatedLogBetaLift β W.unop).mrangeRestrict).mk' (r, 1))) =
      associatedLogBetaLift β W.unop r
    cases W
    cases r
    simpa only [Units.val_one, mul_one] using hη.2 _ _ 1
  obtain ⟨jK, _hjK, hu, _hpair, _hunits⟩ := prelog_pushout_hom_extension X
    (constantChartMonoid X R) (constantChartGamma β) L
    (fun W ↦ (η.app W).hom)
    (by
      intro U V f m a
      exact (congrArg (fun z ↦ z ((divisorialChartCongruence
        (associatedLogBetaLift.{u, v} β U.unop).mrangeRestrict).mk' (m, a)))
          (η.naturality f)).symm)
    (by intro U m a; exact hη.2 U.unop m.down a)
    (by
      intro H w hw
      let w' : associatedLogPresheaf β ⟶ H.obj :=
        { app := fun U ↦ CommMonCat.ofHom (w U)
          naturality := by
            intro U V f
            ext z
            induction z using Con.induction_on with
            | H p =>
              rcases p with ⟨m, a⟩
              exact (hw U V f m a).symm }
      obtain ⟨f, hf⟩ := (hη.1 H).2 w'
      refine ⟨f, ?_, ?_⟩
      · intro U z
        exact congrArg (fun k ↦ k.app U z) hf
      · intro g hg
        apply (hη.1 H).1
        apply NatTrans.ext
        funext U
        ext z
        exact (hg U z).trans (congrArg (fun k ↦ k.app U z) hf).symm)
    i (by intro U m; rfl) K
  have hcomp (f : {f : L.monoidSheaf ⟶ K.monoidSheaf // f.hom ≫ K.alpha = L.alpha}) :
      (i ≫ f.val.hom) ≫ K.alpha = constantChartGamma β := by
    rw [Category.assoc, f.property, hiα]
  have hglobal (f : {f : L.monoidSheaf ⟶ K.monoidSheaf // f.hom ≫ K.alpha = L.alpha}) :
      EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) f ∈
        associatedLogCompatibleRange K β := by
    change (K.alpha.app _).hom.comp
      (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) f) = _
    ext r
    have h := congrArg (fun z ↦ z.app (op (Scheme.Etale.mk (𝟙 X))) r) (hcomp f)
    change K.alpha.app _ (f.val.hom.app _ (associatedLogIota β L η r)) =
      associatedLogBetaLift.{u, v} β (Scheme.Etale.mk (𝟙 X)) r at h
    change K.alpha.app _ (f.val.hom.app _ (associatedLogIota β L η r)) = β r.down
    rw [h]
    change (𝟙 X : X ⟶ X).appTop.hom (β r.down) = β r.down
    simp
  constructor
  · intro f g h
    apply Subtype.ext
    have hfg : i ≫ f.val.hom = i ≫ g.val.hom := by
      apply constantChartMap_ext
      exact CommMonCat.hom_ext h
    obtain ⟨z, hz, huniq⟩ := hu (i ≫ f.val.hom) (hcomp f)
    exact (huniq f.val ⟨f.property, rfl⟩).trans
      (huniq g.val ⟨g.property, hfg.symm⟩).symm
  · apply Set.ext
    intro c
    constructor
    · rintro ⟨f, rfl⟩
      exact hglobal f
    · intro hc
      obtain ⟨f, hf, _⟩ := hu (constantChartMap K c)
        (constantChartMap_compatible β K c hc)
      refine ⟨⟨f, hf.1⟩, ?_⟩
      have h := congrArg (fun z ↦ (z.app (op (Scheme.Etale.mk (𝟙 X)))).hom) hf.2
      exact h.trans (constantChartMap_global K c)

set_option maxHeartbeats 600000 in
-- Elaborating the generic quotient presentation against the constant chart uses
-- many definitional equalities of site functors; the file still compiles within 60 seconds.
private theorem associatedLog_etale_restriction {X : Scheme.{max u v}}
    [IsLocallyNoetherian X] {R : Type v} [CommMonoid R] (β : R →* Γ(X, ⊤))
    (L : EtaleLogStructure.{max u v} X) (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj)
    (hη : IsAssociatedLogPresentation β L η) (U : X.Etale) :
    ∃ (LU : EtaleLogStructure.{max u v} U.left)
      (ηU : associatedLogPresheaf (X := U.left) (associatedLogBeta β U) ⟶ LU.monoidSheaf.obj),
      IsAssociatedLogPresentation (associatedLogBeta β U) LU ηU ∧
      ∃ e : LU.monoidSheaf.obj ≅
          (MorphismProperty.Over.map ⊤ U.prop).op ⋙ L.monoidSheaf.obj,
        (∀ (W : U.left.Etale) (r : R) (a : Γ(W.left, ⊤)ˣ),
          e.hom.app (op W) (ηU.app (op W) ((divisorialChartCongruence (P := ULift.{u, v} R)
            (associatedLogBetaLift β
              ((MorphismProperty.Over.map ⊤ U.prop).obj W)).mrangeRestrict).mk'
              (ULift.up r, a))) =
            η.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj W))
              ((divisorialChartCongruence (P := ULift.{u, v} R)
                (associatedLogBetaLift β
                  ((MorphismProperty.Over.map ⊤ U.prop).obj W)).mrangeRestrict).mk'
                    (ULift.up r, a))) ∧
        ∀ (W : U.left.Etale) (s : LU.monoidSheaf.obj.obj (op W)),
          L.alpha.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj W))
            (e.hom.app (op W) s) = LU.alpha.app (op W) s := by
  have h := etaleLogPresentation_restriction X (constantChartMonoid X R)
    (constantChartGamma β) L η hη.1 (by
      intro W m a
      exact hη.2 W m.down a) U
  have : IsLocallyNoetherian U.left := h.1
  have hp : ∃ (LU : EtaleLogStructure.{max u v} U.left)
      (ηU : associatedLogPresheaf.{u, v} (associatedLogBeta β U) ⟶ LU.monoidSheaf.obj),
      IsAssociatedLogPresentation.{u, v} (associatedLogBeta β U) LU ηU :=
    associatedLog_exists_presentation.{u, v} U.left R (associatedLogBeta β U)
  obtain ⟨LU, ηU, hU⟩ := hp
  obtain ⟨_hlog, e, he, _huniq⟩ := h.2.2.2 LU.toEtalePrelogStructure ηU hU.1
    (by
      intro W m a
      exact hU.2 W m.down a)
  refine ⟨LU, ηU, hU, e, ?_, ?_⟩
  · intro W r a
    exact he.1 W (ULift.up r) a
  · exact he.2.1

set_option maxHeartbeats 600000 in
-- The existential witnesses and the five comparisons elaborate large site-functor
-- types; this allowance concerns heartbeats, while the file retains the 60-second limit.
/-- The associated log structure exists with its universal property, geometric
pushout stalks, étale restriction comparison and chart consequence.

Source: ILO VI 1.1, printed p. 69, referring to Kato (1988), §1. The explicit
argument is the ten-step proof of this node; generic sheaf results are from Stacks.
Proof:
1. Form the quotient of pairs by the pushout congruence; its restriction maps and
   structural formula are well defined on generators (`def-trf-fs-log-blowup`).
2. Sheafify in commutative monoids, with the same underlying set sheafification
   (`lem-trf-commutative-monoid-sheafification`), and extend the structural map.
3. By local representatives (`lem-weil-pbc-site-sheafification-sections-local`),
   a pair with unit image has its chart element mapping to a unit. The pushout
   relation identifies it with that unit. This proves the log axiom.
4. Given a compatible chart into `K`, send `[r,a]` to the restricted chart value
   times the canonical unit in `K`. The log axiom makes this respect the relations;
   monoid sheafification extends it uniquely.
5. Conversely compose with `ι`. Compatibility forces every log map to fix units,
   so the pair formula determines it. These operations are mutually inverse.
6. Cofiltered pointed étale neighbourhoods realize finitely many germs and
   equations on one refinement (`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`).
   In particular each stalk unit has a unit representative, and an element of
   `R` mapping to a stalk unit already maps to a unit on some neighbourhood.
7. The quotient of stalk pairs and the stalk of quotient pairs are inverse by
   these representatives; the maps preserve multiplication, `R` and units.
8. Set sheafification preserves geometric stalks
   (`lem-weil-pbc-sets-sheafification-geometric-stalk`); compose with Step 7.
9. For an étale `U`, its site is the slice over `U`
   (`lem-weil-pbc-etale-composition-cancellation`, `def-weil-pbc-etale-site`). The
   pair presheaves agree there. Local representatives and the local-bijection
   criterion (`lem-cbc-set-presheaf-sheafification-local-bijection`) identify their
   sheafifications, with the same structure and chart maps. `U` is locally
   Noetherian because it is locally of finite type over `X` (`pqf-def-locnoeth`).
10. A chart makes the canonical map into `K` an isomorphism on geometric stalks
    by Step 8 and `EtaleLogStructure.IsChart`. Algebraic closures of residue fields
    give a covering family of geometric points (`def-weil-algebraic-closure`).
    Conservativity (`lem-weil-pbc-sets-etale-iso-on-geometric-stalks`) makes this an
    isomorphism of sheaves. Transfer Step 5 along it.
(blueprint: lem-trf-associated-log-universal-stalks). -/
theorem associatedLog_universal_stalks (X : Scheme.{max u v}) [IsLocallyNoetherian X]
    (R : Type v) [CommMonoid R] (β : R →* Γ(X, ⊤)) :
    ∃ (L : EtaleLogStructure.{max u v} X) (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj),
      IsAssociatedLogPresentation β L η ∧
      (∀ K : EtaleLogStructure.{max u v} X,
        Function.Injective
          (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (K := K)) ∧
        Set.range
          (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (K := K)) =
            {v | (K.alpha.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp v =
              associatedLogDownChart β}) ∧
      (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ X),
        ∃ e : divisorialChartPushout (P := ULift.{u, v} R)
          (associatedLogStalkBeta β t).mrangeRestrict ≅
            L.toEtalePrelogStructure.stalk t,
          ∀ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
            (r : R) (a : Γ(W.left, ⊤)ˣ),
            e.hom ((divisorialChartCongruence (P := ULift.{u, v} R)
              (associatedLogStalkBeta β t).mrangeRestrict).mk'
                (ULift.up r, Units.map (strictLocalGerm X t W w).hom.toMonoidHom a)) =
              L.toEtalePrelogStructure.germ t W w
                (η.app (op W) ((divisorialChartCongruence (P := ULift.{u, v} R)
                  (associatedLogBetaLift β W).mrangeRestrict).mk' (ULift.up r, a)))) ∧
      (∀ U : X.Etale,
        ∃ (LU : EtaleLogStructure.{max u v} U.left)
          (ηU : associatedLogPresheaf (X := U.left) (associatedLogBeta β U) ⟶ LU.monoidSheaf.obj),
          IsAssociatedLogPresentation (associatedLogBeta β U) LU ηU ∧
          ∃ e : LU.monoidSheaf.obj ≅
              (MorphismProperty.Over.map ⊤ U.prop).op ⋙ L.monoidSheaf.obj,
            (∀ (W : U.left.Etale) (r : R) (a : Γ(W.left, ⊤)ˣ),
              e.hom.app (op W) (ηU.app (op W) ((divisorialChartCongruence (P := ULift.{u, v} R)
                (associatedLogBetaLift β
                  ((MorphismProperty.Over.map ⊤ U.prop).obj W)).mrangeRestrict).mk'
                  (ULift.up r, a))) =
                η.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj W))
                  ((divisorialChartCongruence (P := ULift.{u, v} R)
                    (associatedLogBetaLift β
                      ((MorphismProperty.Over.map ⊤ U.prop).obj W)).mrangeRestrict).mk'
                        (ULift.up r, a))) ∧
            ∀ (W : U.left.Etale) (s : LU.monoidSheaf.obj.obj (op W)),
              L.alpha.app (op ((MorphismProperty.Over.map ⊤ U.prop).obj W))
                (e.hom.app (op W) s) = LU.alpha.app (op W) s) ∧
      (∀ (K : EtaleLogStructure.{max u v} X)
        (c : ULift.{u, v} R →* K.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 X)))),
        (K.alpha.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp c =
          associatedLogDownChart β →
        K.IsChart (Scheme.Etale.mk (𝟙 X)) c →
          (∃ e : L.monoidSheaf ≅ K.monoidSheaf,
            e.hom.hom ≫ K.alpha = L.alpha ∧
            (e.hom.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp
              (associatedLogIota β L η) = c) ∧
          ∀ N : EtaleLogStructure.{max u v} X,
            Function.Injective (EtaleLogStructure.composeGlobalChart c (K := N)) ∧
            Set.range (EtaleLogStructure.composeGlobalChart c (K := N)) =
              associatedLogCompatibleRange N β) := by
  have hp : ∃ (L : EtaleLogStructure.{max u v} X)
      (η : associatedLogPresheaf.{u, v} β ⟶ L.monoidSheaf.obj),
      IsAssociatedLogPresentation.{u, v} β L η :=
    associatedLog_exists_presentation.{u, v} X R β
  obtain ⟨L, η, hη⟩ := hp
  have hu := associatedLog_universal.{u, v} β L η hη
  obtain ⟨hs, hchart⟩ := associatedLog_presentation_stalk_comparison.{u, v} β L η hη
  refine ⟨L, η, hη, hu, hs, associatedLog_etale_restriction.{u, v} β L η hη, ?_⟩
  intro K c hc hK
  obtain ⟨f, hfc⟩ := (show c ∈ Set.range
      (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (K := K)) by
    rw [(hu K).2]
    exact hc)
  have : IsIso f.val := EtaleLogStructure.isIso_of_globalChart L K
    (associatedLogIota β L η) c hchart hK f.val f.property hfc
  let e := asIso f.val
  have he : e.hom.hom ≫ K.alpha = L.alpha := f.property
  have hec : (e.hom.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp
      (associatedLogIota β L η) = c := hfc
  have hei : e.inv.hom ≫ L.alpha = K.alpha := by
    have hh : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg (fun z ↦ z.hom) e.inv_hom_id
    rw [← he, ← Category.assoc, hh, Category.id_comp]
  have heic : (e.inv.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp c =
      associatedLogIota β L η := by
    rw [← hec, ← MonoidHom.comp_assoc]
    have hh := congrArg
      (fun z ↦ (z.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom) e.hom_inv_id
    change (e.inv.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom.comp
      (e.hom.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom = MonoidHom.id _ at hh
    rw [hh]
    rfl
  refine ⟨⟨e, he, hec⟩, ?_⟩
  intro N
  let pre (g : {g : K.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = K.alpha}) :
      {g : L.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = L.alpha} :=
    ⟨e.hom ≫ g.val, by
      change (e.hom.hom ≫ g.val.hom) ≫ N.alpha = _
      rw [Category.assoc, g.property, he]⟩
  have hpre (g : {g : K.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = K.alpha}) :
      EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (pre g) =
        EtaleLogStructure.composeGlobalChart c g := by
    change ((g.val.hom.app _).hom.comp (e.hom.hom.app _).hom).comp _ = _
    rw [MonoidHom.comp_assoc, hec]
    rfl
  constructor
  · intro g h hgh
    have hp : pre g = pre h := (hu N).1 (by rw [hpre, hpre, hgh])
    apply Subtype.ext
    exact (cancel_epi e.hom).mp (congrArg Subtype.val hp)
  · apply Set.ext
    intro d
    constructor
    · rintro ⟨g, rfl⟩
      have hh : EtaleLogStructure.composeGlobalChart
          (associatedLogIota β L η) (pre g) ∈ associatedLogCompatibleRange N β := by
        rw [← (hu N).2]
        exact ⟨pre g, rfl⟩
      rwa [hpre] at hh
    · intro hd
      obtain ⟨g, hg⟩ := (show d ∈ Set.range
          (EtaleLogStructure.composeGlobalChart (associatedLogIota β L η) (K := N)) by
        rw [(hu N).2]
        exact hd)
      let g' : {g : K.monoidSheaf ⟶ N.monoidSheaf // g.hom ≫ N.alpha = K.alpha} :=
        ⟨e.inv ≫ g.val, by
          change (e.inv.hom ≫ g.val.hom) ≫ N.alpha = _
          rw [Category.assoc, g.property, hei]⟩
      refine ⟨g', ?_⟩
      change ((g.val.hom.app _).hom.comp (e.inv.hom.app _).hom).comp c = d
      rw [MonoidHom.comp_assoc, heic]
      exact hg

end AlgebraicGeometry
