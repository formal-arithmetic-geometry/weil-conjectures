/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.WeilGeometricFiberProperties
public import Sheaf.Paper.CompactSupportCoefficientAction
import all Sheaf.Paper.WeilIndSheafCategory
import all Sheaf.Paper.CommonStageOpenHeartAdjunction

/-! # Realization of open extension on represented Weil ind-sheaves

Source: SGA 4, XVII, §5.1; Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7.
(blueprint: lem-zl-ind-open-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open CategoryTheory.Endofunctor
attribute [local irreducible] Scheme.residueField
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section CommonStageModel
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
open CommonOpenHeartProof CategoryTheory.Functor
attribute [local instance] stageCategory
attribute [local implicit_reducible] catToReflQuiver StageHom
set_option allowUnsafeReducibility true in
attribute [local reducible] Stage stageCategory
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
set_option allowUnsafeReducibility true in
attribute [local irreducible] stageSystem commonStageDerivedPullback
  sfCompactSupportFiniteFunctor rationalDerivedPullback

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  SheafOfModules.localizedSystemExtensionAdditive
  SheafOfModules.localizedSystemExtensionLimits
  SheafOfModules.localizedSystemExtensionColimits
  SheafOfModules.localizedSystemRestrictionAdditive
  SheafOfModules.localizedSystemRestrictionLimits
  SheafOfModules.localizedSystemRestrictionColimits in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Retain the object formula in the constructive proof of the common-stage open
adjunction. Only this formula is needed to compare with an arbitrary normalized
coefficient action: its finite functors have the same literal object values.
Source: SGA 4, XVII, §5; the common-stage descent construction of
`commonStageOpenHeartAdjunction`. -/
private theorem zlOpenRealization_commonModel
    {U T : Scheme.{u}} [U.Over (Spec (.of D.k))] [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (j : U ⟶ T) [IsOpenImmersion j] [j.IsOver (Spec (.of D.k))] [QuasiCompact j]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ y : T, Invertible (l : T.residueField y)]
    (S : SfCompactSupportCoefficientAction l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) Ω (.ofIsOpenImmersion j)) :
    ∃ J : generalAlgebraicallyClosedConstructibleCategory l Ω U ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω T,
      Nonempty (J ⊣ commonStageDerivedPullback l Ω j) ∧
      (∀ (b : Bool) (n : ℤ)
        (K : generalAlgebraicallyClosedConstructibleCategory l Ω U),
        sfCommonStageStandardClass l U Ω b n K →
        sfCommonStageStandardClass l T Ω b n (J.obj K)) ∧
      ∀ K, J.obj K = S.system.functor.obj K := by
  let : ∀ E : Index l Ω, Category (Stage l Ω U E) :=
    fun E ↦ stageCategory l Ω U E
  let : ∀ E : Index l Ω, Category (Stage l Ω T E) :=
    fun E ↦ stageCategory l Ω T E
  obtain ⟨⟨Φ, β, coh⟩, hR, _⟩ := sfRationalDirectImageCoefficientCompatibility l Ω j
  obtain ⟨hΦ, hβ, _⟩ := hR
  dsimp only at hΦ hβ
  subst Φ
  let R : (stageSystem l Ω T).Morphism (stageSystem l Ω U) :=
    ⟨(fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) j), β, coh⟩
  let L : ∀ E : Index l Ω, Stage l Ω U E ⥤ Stage l Ω T E :=
    fun E ↦ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) (Compactification.ofIsOpenImmersion j)
        (Coefficient.{u} l Ω E)
  let a : ∀ E, L E ⊣ R.Φ E := fun E ↦
    (rationalAdjunction D l hl j (Coefficient.{u} l Ω E)).1
  let hf (E : Index l Ω) : (L E).FullyFaithful :=
    (rationalAdjunction D l hl j (Coefficient.{u} l Ω E)).2
  have hu (E : Index l Ω) : IsIso (a E).unit := by
    let : (L E).Full := (hf E).full
    let : (L E).Faithful := (hf E).faithful
    exact (a E).unit_isIso_of_L_fully_faithful
  let e : ∀ {E F : Index l Ω} (h : E ≤ F),
      L E ⋙ (stageSystem l Ω T).T h ≅ (stageSystem l Ω U).T h ⋙ L F :=
    fun {E F} h ↦
      let hβ := sfCompactSupportNormalizedScalarIsomorphisms l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl)
        (Compactification.ofIsOpenImmersion j) Ω E F h
      let β := hβ.choose_spec.2.2.choose
      isoWhiskerLeft _ (operationStageTransitionIso l Ω T E F h) ≪≫ β ≪≫
        isoWhiskerRight (operationStageTransitionIso l Ω U E F h).symm _
  let d := fun {E F : Index l Ω} (h : E ≤ F) ↦
    ((mateEquiv (a E) (a F)).symm (TwoSquare.mk _ _ _ _ (R.β h).hom)).natTrans
  have hd {E F : Index l Ω} (h : E ≤ F) : IsIso (d h) := by
    let := hu E
    let := hu F
    exact leftMate_isIso (a E) (a F) _ _ (R.β h) (e h)
  let b := fun {E F : Index l Ω} (h : E ≤ F) ↦ (@asIso _ _ _ _ (d h) (hd h)).symm
  have hb {E F : Index l Ω} (h : E ≤ F) (K : Stage l Ω U E) :
      ((stageSystem l Ω U).T h).map ((a E).unit.app K) ≫
        (R.β h).hom.app ((L E).obj K) =
      (a F).unit.app (((stageSystem l Ω U).T h).obj K) ≫
        (R.Φ F).map ((b h).inv.app K) :=
    unit_mateEquiv_symm (a E) (a F) (TwoSquare.mk _ _ _ _ (R.β h).hom) K
  have hc {E F : Index l Ω} (h : E ≤ F) (K : Stage l Ω T E) :
      (L F).map ((R.β h).hom.app K) ≫
        (a F).counit.app (((stageSystem l Ω T).T h).obj K) =
      (b h).inv.app ((R.Φ E).obj K) ≫
        ((stageSystem l Ω T).T h).map ((a E).counit.app K) :=
    mateEquiv_counit_symm (a E) (a F) (TwoSquare.mk _ _ _ _ (R.β h).hom) K
  let J := StageLeftAdjunction.family R L a b hb
  let adj := descendStageAdjunction J R a
    (StageLeftAdjunction.familyUnit R L a b hb)
    (StageLeftAdjunction.familyCounit R L a b hb hc) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hReq : R.functor = commonStageDerivedPullback l Ω j := by
    unfold commonStageDerivedPullback
    apply (commonStageDerivedPullback_existsUnique l Ω j).unique
      (y₁ := R.functor)
    · constructor
      · intro K; rfl
      · intro K N M hK hN f
        apply heq_of_eq
        rw [StageSystem.Morphism.functor_map_mkHom]
        dsimp only [StageSystem.Morphism.mapAt, R]
        have hp := congrArg Iso.hom (eq_of_heq (hβ K.stage M hK K.obj))
        have hq := congrArg Iso.inv (eq_of_heq (hβ N.stage M hN N.obj))
        dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
        erw [hp, hq]
        rfl
    · exact (commonStageDerivedPullback_existsUnique l Ω j).exists.choose_spec
  refine ⟨J.functor, ⟨adj.ofNatIsoRight (eqToIso hReq)⟩, ?_, ?_⟩
  · intro q n K hK
    obtain ⟨E, M, hM, ⟨α⟩⟩ := hK
    refine ⟨E, (L E).obj M, rational_standard D l hl j
      (Coefficient.{u} l Ω E) q n M hM, ?_⟩
    exact ⟨J.functor.mapIso α ≪≫ (J.ιCompFunctorIso E).symm.app M⟩
  · intro K
    change (⟨K.stage, (L K.stage).obj K.obj⟩ : Pair l Ω T) =
      ⟨K.stage, (S.system.Φ K.stage).obj K.obj⟩
    rw [S.finite_eq K.stage]

end CommonStageModel

/-- A represented open ind-extension realizes the normalized open compact-support
operation on its underlying common-stage object. No proper image is involved.
Source: SGA 4, XVII, 5.1; Bhatt--Scholze, 6.7.6--6.7.7
(blueprint: lem-zl-ind-open-realization).

Proof: integral extension by zero is exact and left adjoint to restriction. The
identity-proper compactification computes this exact extension at every positive
coefficient quotient. The normalized completed realization consequently identifies
its Roos-limit value with integral extension by zero. Rationalization and finite
coefficient extension preserve this adjunction, its units, and the standard heart.
It descends to an exact left adjoint on common-stage hearts, with the prescribed
Frobenius comparison given by the inverse open-adjunction mate. Transport through
AsSmall and extend by filtered colimits; the Yoneda Kan unit identifies this
extension on represented objects with the original heart functor. The fixed-pair
adjunction has the same unit normalization as zlIndWeilOpenShriek, so uniqueness
of left adjoints identifies the two. Full faithfulness of the Weil embedding then
identifies the arbitrary representative G with this heart extension. Applying the
heart inclusion gives the displayed comparison. Finite-type schemes over a field
are noetherian, so their open immersions are quasi-compact; no separated structure
map is required. Empty opens, the identity open and zero objects are included. -/
theorem zlIndWeilOpenShriek_realization
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    (S : SfCompactSupportCoefficientAction l D.k (zlRealizationPrimeUnit D l hl) Ω
      (.ofIsOpenImmersion (zlFiberMap D j₀)))
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (G : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (e : (zlWeilIndEmbedding D l hl Ω Y₀).obj G ≅
      (zlIndWeilOpenShriek D l hl Ω j₀).obj
        ((zlWeilIndEmbedding D l hl Ω X₀).obj F)) :
    Nonempty (G.obj.carrier ≅ S.system.functor.obj F.obj.carrier) := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  obtain ⟨H, ⟨aH⟩, hH, hobj⟩ :=
    zlOpenRealization_commonModel D l hl Ω (zlFiberMap D j₀) S
  let PX := sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
  let PY := sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω
  have hheart (K : sfCommonStageHeart l (D.geometricFiber X₀).left Ω) :
      PY (H.obj K.obj) :=
    ⟨hH true 0 K.obj K.property.1, hH false 0 K.obj K.property.2⟩
  -- Restrict to hearts, then transport and extend the adjunction.
  let J := PY.lift (PX.ι ⋙ H) hheart
  let a : J ⊣ zlHeartPull D l hl Ω j₀ :=
    aH.restrictFullyFaithful PX.fullyFaithfulι PY.fullyFaithfulι
      (Iso.refl _) (Iso.refl _)
  let eX : sfCommonStageHeart l (D.geometricFiber X₀).left Ω ≌
      zlSmallHeart D l Ω hl X₀ := AsSmall.equiv
  let eY : sfCommonStageHeart l (D.geometricFiber Y₀).left Ω ≌
      zlSmallHeart D l Ω hl Y₀ := AsSmall.equiv
  let L := eX.inverse ⋙ J ⋙ eY.functor
  let aL : L ⊣ zlSmallPull D l hl Ω j₀ :=
    eX.symm.toAdjunction.comp (a.comp eY.toAdjunction)
  let aI := zlIndMap_adjunction aL
  let := (zlIndFrobenius_exact D l hl Ω X₀).2.2.2
  let := (zlIndFrobenius_exact D l hl Ω Y₀).2.2.2
  -- The inverse mate lifts the ind-adjunction to the specified Frobenius pairs.
  let eR := zlIndSquare (zlSmallPull D l hl Ω j₀)
    (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
    (zlSmallSquare D l hl Ω j₀)
  let m := ((mateEquiv aI aI).symm (TwoSquare.mk _ _ _ _ eR.hom)).natTrans
  let : IsIso m := isIso_inverseMate_of_equivalences aI aI eR
  let eL := (asIso m).symm
  have hm : (mateEquiv aI aI (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom :=
    congrArg TwoSquare.natTrans ((mateEquiv aI aI).apply_symm_apply
      (TwoSquare.mk _ _ _ _ eR.hom))
  let aW := IsoAlgebra.mapOfNatIsoAdjunction aI eL eR hm
  let := zlIndWeilPull_isRightAdjoint D l hl Ω j₀
  let t : zlIndWeilOpenShriek D l hl Ω j₀ ≅ IsoAlgebra.mapOfNatIso eL :=
    Adjunction.leftAdjointUniq (Adjunction.ofIsRightAdjoint _) aW
  -- Forget Frobenius and reflect the represented isomorphism through Yoneda.
  let A := ((zlWeilSmallPairs D l hl Ω X₀).obj F).carrier
  let B := ((zlWeilSmallPairs D l hl Ω Y₀).obj G).carrier
  let UY := IsoAlgebra.forget (zlIndMap (zlSmallFrobenius D l hl Ω Y₀))
  let i : Ind.yoneda.obj B ≅ (zlIndMap L).obj (Ind.yoneda.obj A) :=
    UY.mapIso (e ≪≫ t.app ((zlWeilIndEmbedding D l hl Ω X₀).obj F))
  let b : B ≅ L.obj A := Ind.yoneda.fullyFaithful.preimageIso
    (i ≪≫ (zlIndMapIso L).app A)
  let d := (PY.ι).mapIso (AsSmall.down.mapIso b)
  have hA : A = eX.functor.obj ⟨F.obj.carrier, F.property⟩ :=
    (zlWeilSmallPairs_existsUnique D l hl Ω X₀).exists.choose_spec.1 F
  have hB : B = eY.functor.obj ⟨G.obj.carrier, G.property⟩ :=
    (zlWeilSmallPairs_existsUnique D l hl Ω Y₀).exists.choose_spec.1 G
  dsimp only [L, Functor.comp_obj] at d
  rw [hA, hB] at d
  have d' : G.obj.carrier ≅ H.obj F.obj.carrier := d
  exact ⟨d' ≪≫ eqToIso (hobj F.obj.carrier)⟩

end WeilConjectures
