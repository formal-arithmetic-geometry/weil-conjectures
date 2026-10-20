/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.PbcQbarCategory
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.PbcCommonStageCones
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PbcVerdierAxioms

/-!
# Descent of scalar-compatible exact functors

Source: Weil conjectures blueprint main-20261015, proper base change, order 1312
(blueprint: prop-weil-pbc-descent-functors).

The stage-system morphism records the finite-stage functors and their comparison
isomorphisms.  Its induced pair-category functor is the coefficient-category
functor of the proposition; the displayed map formula is included explicitly.

## Main definitions

* `CategoryTheory.StageSystem.CoherentExactMorphism`: the exact coherent stage family.
* `CategoryTheory.StageSystem.Morphism.DescentSpec`: the explicit general conclusion.
* `CategoryTheory.StageSystem.Morphism.ExactDescent`: the exactness clause.
* `AlgebraicGeometry.Scheme.pbcDescentDirectImage`: the actual rationalized direct image.
* `AlgebraicGeometry.Scheme.pbcDescentPullback`: the actual rationalized completed pullback.
* `AlgebraicGeometry.Scheme.PbcDirectImageBetaSpec`: canonical direct-image β components.
* `AlgebraicGeometry.Scheme.PbcPullbackBetaSpec`: canonical inverse pullback β components.

## Main statements

* `AlgebraicGeometry.Scheme.pbcDescentFunctors`: descent and general compatible equations.
* `AlgebraicGeometry.Scheme.pbcDescentOperations`: the four-operation exchange application.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe w u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.StageSystem

/-- A family of exact finite-stage functors with scalar-extension comparisons.
The `base` field contains the stage functors `Φ_E`, comparisons `β_{F/E}`, and
their associator coherence.  The remaining fields record additivity,
compatibility with shifts of the stage functors and comparisons, and
preservation of distinguished triangles at every stage. On the normalized PBC
stage systems, the unit equation follows from associator coherence at repeated
stages: the resulting idempotent isomorphism component is the identity.
Source: blueprint main-20261015, order 1312
(blueprint: prop-weil-pbc-descent-functors). -/
structure CoherentExactMorphism {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    (S : StageSystem C) (S' : StageSystem D)
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (C i)] [∀ i, HasZeroObject (D i)]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
    [∀ i, ∀ n : ℤ, (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (C i)] [∀ i, Pretriangulated (D i)]
    [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ (i j : I) (h : i ≤ j), (S'.T h).CommShift ℤ] where
  base : StageSystem.Morphism S S'
  additive : ∀ i, (base.Φ i).Additive
  [commShift : ∀ i, (base.Φ i).CommShift ℤ]
  betaCommShift : ∀ {i j : I} (h : i ≤ j),
    NatTrans.CommShift (base.β h).hom ℤ
  triangulated : ∀ i, (base.Φ i).IsTriangulated

namespace Morphism

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    {S : StageSystem C} {S' : StageSystem D}
    [Preadditive S.PairCategory] [Preadditive S'.PairCategory]
    [HasZeroObject S.PairCategory] [HasZeroObject S'.PairCategory]
    [HasShift S.PairCategory ℤ] [HasShift S'.PairCategory ℤ]
    [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
    [∀ n : ℤ, (shiftFunctor S'.PairCategory n).Additive]
    [Pretriangulated S.PairCategory] [Pretriangulated S'.PairCategory]

/-- The exactness clause for the induced functor, with its shift structure existentially
quantified. This packages the existing Additive, CommShift and IsTriangulated predicates;
all category structures are the supplied canonical ones.
Source: blueprint main-20261015, order 1312, exactness clause
(blueprint: prop-weil-pbc-descent-functors). -/
def ExactDescent (F : StageSystem.Morphism S S') : Prop :=
    F.functor.Additive ∧
      (∃ s : F.functor.CommShift ℤ,
        (fun [_hs : F.functor.CommShift ℤ] ↦ F.functor.IsTriangulated) (_hs := s))

/-- The full general descent conclusion, including every representative and every equation
between compatible transformation families. This predicate packages the displayed formulas
without choosing replacement categories, shifts, arrows or functors.
Source: blueprint main-20261015, order 1312, general descent paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def DescentSpec (F : StageSystem.Morphism S S') : Prop :=
    ExactDescent F ∧
      (∀ (K L : S.PairCategory) (M : I)
        (hK : K.stage ≤ M) (hL : L.stage ≤ M) (u : K.toStage hK ⟶ L.toStage hL),
        F.functor.map (StageSystem.PairCategory.mkHom M hK hL u) =
          StageSystem.PairCategory.mkHom
            (X := F.functor.obj K) (Y := F.functor.obj L) M hK hL
            ((F.β hK).hom.app K.obj ≫ (F.Φ M).map u ≫
              (F.β hL).inv.app L.obj)) ∧
      (∀ (G H : StageSystem.Morphism S S')
        (τ : StageSystem.Morphism.Hom G H) (K : S.PairCategory),
        (StageSystem.Morphism.descNatTrans τ).app K =
          (S'.ι K.stage).map ((τ.τ K.stage).app K.obj)) ∧
      (∀ (G H : StageSystem.Morphism S S')
        (τ τ' : StageSystem.Morphism.Hom G H),
        (∀ (E : I) (K : C E), (τ.τ E).app K = (τ'.τ E).app K) →
            StageSystem.Morphism.descNatTrans τ = StageSystem.Morphism.descNatTrans τ') ∧
      (∀ G : StageSystem.Morphism S S',
        StageSystem.Morphism.descNatTrans (StageSystem.Morphism.Hom.id G) = 𝟙 _) ∧
      (∀ (G H J : StageSystem.Morphism S S')
        (τ : StageSystem.Morphism.Hom G H) (τ' : StageSystem.Morphism.Hom H J),
        StageSystem.Morphism.descNatTrans (τ.comp τ') =
          StageSystem.Morphism.descNatTrans τ ≫ StageSystem.Morphism.descNatTrans τ')

omit [HasZeroObject S.PairCategory] [HasZeroObject S'.PairCategory]
  [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
  [∀ n : ℤ, (shiftFunctor S'.PairCategory n).Additive]
  [Pretriangulated S.PairCategory] [Pretriangulated S'.PairCategory]
  [HasShift S.PairCategory ℤ] [HasShift S'.PairCategory ℤ] in
set_option backward.isDefEq.respectTransparency false in
private theorem additive_of_stage
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    (F : StageSystem.Morphism S S') (hΦ : ∀ i, (F.Φ i).Additive)
    (hS : S.PairPreadditiveNormalized (inferInstance : Preadditive S.PairCategory))
    (hS' : S'.PairPreadditiveNormalized (inferInstance : Preadditive S'.PairCategory)) :
    F.functor.Additive := by
  constructor
  intro K L f g
  obtain ⟨M, _, hK, hL, hK', hL', u, v, rfl, rfl⟩ :=
    PairCategory.exists_common_stage f g K.stage
  rw [← (hS K L M hK hL u v).1]
  rw [F.functor_map_mkHom, F.functor_map_mkHom, F.functor_map_mkHom]
  have := hΦ M
  calc
    _ = PairCategory.mkHom (X := F.functor.obj K) (Y := F.functor.obj L)
        M hK hL (F.mapAt u + F.mapAt v) := by
      apply congrArg (PairCategory.mkHom (X := F.functor.obj K)
        (Y := F.functor.obj L) M hK hL)
      simp only [mapAt, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
    _ = _ := (hS' _ _ M hK hL _ _).1

section StageShift
variable [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S'.assoc h h').hom ℤ]
  (F : StageSystem.Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]
  (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)

private def shiftHom (n : ℤ) : Hom
    ((pbcStageShift S n).comp F) (F.comp (pbcStageShift S' n)) where
  τ i := ((F.Φ i).commShiftIso n).hom
  comm {i j} h K := by
    have := hβ h
    simpa [Morphism.comp, pbcStageShift, Functor.commShiftIso_comp_hom_app,
      Category.assoc] using (NatTrans.shift_app_comm (F.β h).hom n K)

private def shiftIso (n : ℤ) :
    (pbcPairShift S n) ⋙ F.functor ≅ F.functor ⋙ (pbcPairShift S' n) :=
  (functorCompIso (pbcStageShift S n) F).symm ≪≫
    NatIso.ofComponents
      (F := ((pbcStageShift S n).comp F).functor)
      (G := (F.comp (pbcStageShift S' n)).functor)
      (fun K ↦ (S'.ι K.stage).mapIso (((F.Φ K.stage).commShiftIso n).app K.obj))
      (fun f ↦ (descNatTrans (shiftHom F hβ n)).naturality f) ≪≫
    functorCompIso F (pbcStageShift S' n)

end StageShift

end Morphism

section ExactShift
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {S' : StageSystem D}
  [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S.assoc h h').hom ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
    NatTrans.CommShift (S'.assoc h h').hom ℤ]
  (F : StageSystem.Morphism S S') [∀ i, (F.Φ i).CommShift ℤ]
  (hβ : ∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (F.β h).hom ℤ)

set_option backward.isDefEq.respectTransparency false in
private theorem shiftIso_hom_app (n : ℤ) (K : S.PairCategory) :
    (Morphism.shiftIso F hβ n).hom.app K =
      (S'.ι K.stage).map (((F.Φ K.stage).commShiftIso n).hom.app K.obj) := by
  simp only [Morphism.shiftIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Morphism.functorCompIso_inv_app, Morphism.functorCompIso_hom_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom,
    Category.comp_id]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible] private def descendedCommShift : F.functor.CommShift ℤ where
  commShiftIso := Morphism.shiftIso F hβ
  commShiftIso_zero := by
    ext K
    simp only [shiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    change (S'.ι K.stage).map (((F.Φ K.stage).commShiftIso (0 : ℤ)).hom.app K.obj) =
      F.functor.map ((S.ι K.stage).map
        ((shiftFunctorZero (C K.stage) ℤ).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        ((shiftFunctorZero (D K.stage) ℤ).inv.app ((F.Φ K.stage).obj K.obj))
    erw [Morphism.functor_map_ι]
    simpa only [Functor.CommShift.isoZero_hom_app, Functor.map_comp] using
      congrArg ((S'.ι K.stage).map)
      (congr_app (congrArg Iso.hom ((F.Φ K.stage).commShiftIso_zero ℤ)) K.obj)
  commShiftIso_add n m := by
    ext K
    simp only [Functor.CommShift.isoAdd_hom_app, shiftIso_hom_app]
    change (S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso (n + m)).hom.app K.obj) =
      F.functor.map ((S.ι K.stage).map
        ((shiftFunctorAdd (C K.stage) n m).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso m).hom.app ((shiftFunctor (C K.stage) n).obj K.obj)) ≫
      (pbcPairShift S' m).map ((S'.ι K.stage).map
        (((F.Φ K.stage).commShiftIso n).hom.app K.obj)) ≫
      (S'.ι K.stage).map
        ((shiftFunctorAdd (D K.stage) n m).inv.app ((F.Φ K.stage).obj K.obj))
    erw [Morphism.functor_map_ι]
    erw [(pbcStageShift S' m).functor_map_ι]
    simpa only [Functor.CommShift.isoAdd_hom_app, Functor.map_comp, pbcStageShift] using
      congrArg ((S'.ι K.stage).map)
      (congr_app (congrArg Iso.hom ((F.Φ K.stage).commShiftIso_add n m)) K.obj)

set_option backward.isDefEq.respectTransparency false in
private theorem inclusionComp_commShift (i : I) :
    letI := descendedCommShift F hβ
    NatTrans.CommShift (F.ιCompFunctorIso i).hom ℤ := by
  let _ := descendedCommShift F hβ
  constructor
  intro n
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  change F.functor.map (𝟙 _) ≫ (Morphism.shiftIso F hβ n).hom.app ((S.ι i).obj K) ≫
      (shiftFunctor S'.PairCategory n).map (𝟙 _) =
    𝟙 _ ≫ ((S'.ι i).map (((F.Φ i).commShiftIso n).hom.app K) ≫ 𝟙 _)
  simp only [shiftIso_hom_app, Functor.map_id, Category.id_comp]
  erw [Category.comp_id]


variable [Nonempty I]
  [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
  [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S'.T h).Additive]
  [∀ i, HasZeroObject (C i)] [∀ i, HasZeroObject (D i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
  [∀ i, ∀ n : ℤ, (shiftFunctor (D i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ i, Pretriangulated (D i)]
  [Pretriangulated S.PairCategory] [Pretriangulated S'.PairCategory]

set_option backward.isDefEq.respectTransparency false in
private theorem triangulated_of_stage
    (hΦ : ∀ i, (F.Φ i).IsTriangulated)
    (hι : ∀ i, (S'.ι i).IsTriangulated)
    (hdist : ∀ U : Pretriangulated.Triangle S.PairCategory,
      U ∈ distTriang S.PairCategory → CommonStageDistinguished S U) :
    letI := descendedCommShift F hβ
    F.functor.IsTriangulated := by
  let _ := descendedCommShift F hβ
  constructor
  intro U hU
  obtain ⟨i, V, hV, ⟨e⟩⟩ := hdist U hU
  have := hΦ i
  have := hι i
  have := inclusionComp_commShift F hβ i
  have : (S.ι i ⋙ F.functor).IsTriangulated :=
    Functor.isTriangulated_of_iso (F.ιCompFunctorIso i).symm
  exact Pretriangulated.isomorphic_distinguished _
    ((S.ι i ⋙ F.functor).map_distinguished V hV) _
    (F.functor.mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso (S.ι i) F.functor).symm.app V)


set_option backward.isDefEq.respectTransparency false in
private theorem canonicalDescent
    (A : CoherentExactMorphism S S')
    (hS : S.PairPreadditiveNormalized (inferInstance : Preadditive S.PairCategory))
    (hS' : S'.PairPreadditiveNormalized (inferInstance : Preadditive S'.PairCategory))
    (hι : ∀ i, (S'.ι i).IsTriangulated)
    (hdist : ∀ U : Pretriangulated.Triangle S.PairCategory,
      U ∈ distTriang S.PairCategory → CommonStageDistinguished S U) :
    Morphism.DescentSpec A.base := by
  let _ := A.commShift
  refine ⟨⟨Morphism.additive_of_stage A.base A.additive hS hS',
    ⟨descendedCommShift A.base (fun {_ _} h ↦ A.betaCommShift h), ?_⟩⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact triangulated_of_stage A.base (fun {_ _} h ↦ A.betaCommShift h)
      A.triangulated hι hdist
  · intro K L M hK hL u
    exact A.base.functor_map_mkHom hK hL u
  · intro G H τ K
    exact Morphism.descNatTrans_app τ K
  · intro G H τ τ' h
    ext K
    exact congrArg ((S'.ι K.stage).map) (h K.stage K.obj)
  · exact Morphism.descNatTrans_id
  · intro G H J τ τ'
    exact Morphism.descNatTrans_comp τ τ'


end ExactShift

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T S : Scheme.{u}) [IsNoetherian T] [IsNoetherian S]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))]
  [iS : Fact (∀ t : S, IsUnit (l : S.presheaf.stalk t))]

/-- Exact descent on the actual Qbar coefficient categories, with the prescribed
representative formula and all compatible transformation equations.
Source: blueprint main-20261015, proper base change, order 1312
(blueprint: prop-weil-pbc-descent-functors).

Proof: use the canonical stage-system functor, with objects (E, Φ_E K) and
representative map β.hom.app K ≫ Φ_M.map u ≫ β.inv.app L. Associator coherence
and naturality identify the transport of this composite at any larger stage,
proving representative independence. Inverse β components cancel to give
identities and composition. Additivity follows at a common stage. Descend the
finite-stage shift comparisons componentwise; betaCommShift gives their
naturality. Applying the exact Φ_M to a distinguished stage triangle and using
β to identify its first two vertices proves preservation of the common-stage
triangles. These are exactly the distinguished triangles in pbcQbarCategory.
For compatible transformations use the components j_E(τ_E K); Hom.comm proves
naturality at every representative. Identities and vertical composites descend
componentwise. Every equation between compatible transformations holds at each
(E,K), hence holds after descent by natural-transformation extensionality.
This applies to compatible transformation families formed by whiskering and
horizontal composition as well. The concrete operation application below uses
four distinct systems and their composite exchange. -/
theorem pbcDescentFunctors
    (F : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω T dT.out iT.out) (pbcScalarSystem l Ω S dS.out iS.out)) :
    StageSystem.Morphism.DescentSpec F.base := by
  exact StageSystem.canonicalDescent F
    (commonStageCalculus l Ω T dT.out iT.out).operations
    (commonStageCalculus l Ω S dS.out iS.out).operations
    (pbcVerdierAxioms l Ω S).2.1
    (fun U hU ↦ ((StageSystem.commonStage_verdier_existsUnique
      (pbcScalarSystem l Ω T dT.out iT.out)).exists.choose_spec.1 U).1 hU)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The rational finite-stage direct image is the restriction of the actual ringed
pro-etale derived direct image followed by the recorded raw scalar localization.
Source: blueprint main-20261015, order 1312, final paragraph, using
prop-weil-pbc-rational-transport (blueprint: prop-weil-pbc-descent-functors). -/
def pbcDescentDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X E ⥤ pbcStageCategory l Ω Y E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (h E) (pbcStageUniformizer.{u} l Ω E)

/-- The rational finite-stage pullback is the restriction of the actual completed
ringed pro-etale pullback followed by the recorded raw scalar localization.
Source: blueprint main-20261015, order 1312, final paragraph, using
prop-weil-pbc-rational-transport (blueprint: prop-weil-pbc-descent-functors). -/
def pbcDescentPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (h E)
    (pbcStageUniformizer.{u} l Ω E)

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

section CanonicalBeta
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- Direct-image β is the localized canonical scalar mate, conjugated by the
integral/scalar comparisons, including equal coefficient stages. The right-hand
side is the unique comparison characterized by the localized ambient mate in
`pbcScalarDirectImage_rational`, at the canonical small coefficient fields.
The endpoint equalities are already concluded separately for every stage;
quantification over their proofs does not impose an additional assumption.
Source: blueprint main-20261015, descent proposition, final paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def PbcDirectImageBetaSpec (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Rf.Φ E = pbcDescentDirectImage l Ω f pres E)
    (eF : Rf.Φ F = pbcDescentDirectImage l Ω f pres F)
    (K : pbcIntegralStage l Ω X E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Rf.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).obj K) ≫
        β.hom.app (ScalarLocalization.mk K) ≫
        (pbcDescentDirectImage l Ω f pres F).map
          ((pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app K))
      (((pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) f
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))

/-- Pullback β inverse is the localized canonical completed scalar comparison,
conjugated by the integral/scalar comparisons, including equal stages. The
right-hand side is the unique comparison characterized by the localized
completed tensor comparison in `pbcScalarCompletedPull_rational`, at the small
coefficient fields. Its orientation is opposite to `Morphism.β`. Endpoint
identifications are concluded separately, so this predicate fixes every β.
Source: blueprint main-20261015, descent proposition, final paragraph
(blueprint: prop-weil-pbc-descent-functors). -/
def PbcPullbackBetaSpec (g : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Lg.Φ E = pbcDescentPullback l Ω g pres E)
    (eF : Lg.Φ F = pbcDescentPullback l Ω g pres F)
    (K : pbcIntegralStage l Ω Y E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Lg.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcDescentPullback l Ω g pres F).map
          ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app K) ≫
        β.inv.app (ScalarLocalization.mk K) ≫
        (pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (pres E)).obj K))
      (((pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) g
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))
end CanonicalBeta

/-- The actual direct-image and completed-pullback families supplied by rational
transport admit coherent stage-system structures and their canonical exchange descends.
The four stage functors are identified with `pbcDescentDirectImage` and
`pbcDescentPullback`. All four scalar-comparison families are characterized by
`PbcDirectImageBetaSpec` and `PbcPullbackBetaSpec`; their exchange is identified
with the localization of `pbcActualCompletedExchange`.

Source: Weil conjectures blueprint main-20261015, proper base change, order 1312
(blueprint: prop-weil-pbc-descent-functors).

Proof: restrict the actual derived operations using the four preservation hypotheses
and rationalize by pbcConditionalRational. Use pbcScalarDirectImage_rational and
pbcScalarCompletedPull_rational for the comparison isomorphisms, transporting their
normalizations to the small finite-coefficient stage presentation. The two completed
coefficient inclusions agree by their unique finite-quotient specifications. Conjugate
by pbcScalarIntegralComparison at both endpoints to normalize the scalar transitions;
for pullback use the inverse comparison. This proves the four BetaSpec clauses, on
every integral object and therefore every rational object, including repeated stages.
The operation coherence in PbcScalarExtension gives their unit, associator and shift equations;
pbcScalarCompletedExchange gives compatibility of the canonical exchange. Apply
pbcDescentFunctors to each of the four coherent families to obtain exactness. The
localized pbcActualCompletedExchange therefore defines a compatible transformation
between the composite families. Descend it componentwise and conjugate by
functorCompIso to obtain the transformation between the descended composites. -/
theorem pbcDescentOperations
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    ∃ (Rf : StageSystem.CoherentExactMorphism
        (pbcScalarSystem l Ω X dX.out iX.out)
        (pbcScalarSystem l Ω Y dY.out iY.out))
      (Rf' : StageSystem.CoherentExactMorphism
        (pbcScalarSystem l Ω X' dX'.out iX'.out)
        (pbcScalarSystem l Ω Y' dY'.out iY'.out))
      (Lg : StageSystem.CoherentExactMorphism
        (pbcScalarSystem l Ω Y dY.out iY.out)
        (pbcScalarSystem l Ω Y' dY'.out iY'.out))
      (Lg' : StageSystem.CoherentExactMorphism
        (pbcScalarSystem l Ω X dX.out iX.out)
        (pbcScalarSystem l Ω X' dX'.out iX'.out)),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        Rf.base.Φ E = pbcDescentDirectImage l Ω f presRf E) ∧
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        Rf'.base.Φ E = pbcDescentDirectImage l Ω f' presRf' E) ∧
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        Lg.base.Φ E = pbcDescentPullback l Ω g presLg E) ∧
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        Lg'.base.Φ E = pbcDescentPullback l Ω g' presLg' E) ∧
      PbcDirectImageBetaSpec l Ω f presRf Rf.base ∧
      PbcDirectImageBetaSpec l Ω f' presRf' Rf'.base ∧
      PbcPullbackBetaSpec l Ω g presLg Lg.base ∧
      PbcPullbackBetaSpec l Ω g' presLg' Lg'.base ∧
      StageSystem.Morphism.ExactDescent Rf.base ∧
      StageSystem.Morphism.ExactDescent Rf'.base ∧
      StageSystem.Morphism.ExactDescent Lg.base ∧
      StageSystem.Morphism.ExactDescent Lg'.base ∧
      ∃ Ex : StageSystem.Morphism.Hom (Rf.base.comp Lg.base)
          (Lg'.base.comp Rf'.base),
        (∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((Ex.τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app K.obj)))) ∧
        ∃ ExQ : Rf.base.functor ⋙ Lg.base.functor ⟶
            Lg'.base.functor ⋙ Rf'.base.functor,
          ExQ = (StageSystem.Morphism.functorCompIso Rf.base Lg.base).inv ≫
            StageSystem.Morphism.descNatTrans Ex ≫
              (StageSystem.Morphism.functorCompIso Lg'.base Rf'.base).hom ∧
          ∀ K : pbcQbarCategory l Ω X,
            ExQ.app K = ((pbcScalarSystem l Ω Y' dY'.out iY'.out).ι K.stage).map
              ((Ex.τ K.stage).app K.obj) := sorry

end AlgebraicGeometry.Scheme
