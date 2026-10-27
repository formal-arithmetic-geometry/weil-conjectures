/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.OpenWeilCoefficientFibres
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import Sheaf.Paper.CommonStageOpenHeartAdjunction
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Sheaf.Paper.IsomorphismFieldTransport
import Sheaf.Paper.OpenWeilCarrierRealization
import Sheaf.Paper.OpenWeilGeometricFibres
import Sheaf.Paper.OpenWeilFiniteStageFrobenius
import Sheaf.Paper.OpenWeilPunctualSpectrum

/-! # Exact extension by zero and punctual weights

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-quasifinite/lem-zl-quasi-finite.proof.md, parts (1) and (2)
(blueprint: lem-zl-extension-by-zero-punctual).

The canonical open extension is the left adjoint of the recorded Weil pullback.
The theorem identifies its underlying object with the actual completed-tower compact
support value and supplies the natural coefficient-fibre and local-Frobenius formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [hUsep : IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]


/-- Put the heart condition on the carrier before adding its invertible structure. -/
private def zlHeartPairsModel {C : Type*} [Category C] (G : C ⥤ C)
    (P : ObjectProperty C) (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj)) :
    (P.inverseImage (CategoryTheory.Endofunctor.IsoAlgebra.forget G)).FullSubcategory ⥤
      CategoryTheory.Endofunctor.IsoAlgebra (P.lift (P.ι ⋙ G) hG) where
  obj K := CategoryTheory.Endofunctor.IsoAlgebra.mk ⟨K.obj.carrier, K.property⟩
    (P.isoMk K.obj.str)
  map a := ObjectProperty.homMk
    { f := ObjectProperty.homMk a.hom.hom.f
      h := ObjectProperty.hom_ext _ a.hom.hom.h }
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply CategoryTheory.Endofunctor.Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply CategoryTheory.Endofunctor.Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    rfl

/-- Moving the heart condition across the invertible-algebra construction is an equivalence. -/
private def zlHeartPairsEquivalence {C : Type*} [Category C] (G : C ⥤ C)
    (P : ObjectProperty C) (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj)) :
    (P.inverseImage (CategoryTheory.Endofunctor.IsoAlgebra.forget G)).FullSubcategory ≌
      CategoryTheory.Endofunctor.IsoAlgebra (P.lift (P.ι ⋙ G) hG) := by
  let F := zlHeartPairsModel G P hG
  let ff : F.FullyFaithful :=
    { preimage := fun a ↦ ObjectProperty.homMk (ObjectProperty.homMk
        { f := a.hom.f.hom
          h := congrArg (fun f ↦ f.hom) a.hom.h })
      map_preimage := fun _ ↦ by
        apply ObjectProperty.hom_ext
        apply CategoryTheory.Endofunctor.Algebra.Hom.ext
        apply ObjectProperty.hom_ext
        rfl
      preimage_map := fun _ ↦ by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply CategoryTheory.Endofunctor.Algebra.Hom.ext
        rfl }
  let := ff.full
  let := ff.faithful
  let : F.EssSurj := ⟨fun K ↦ by
    let a : (P.inverseImage
        (CategoryTheory.Endofunctor.IsoAlgebra.forget G)).FullSubcategory :=
      ⟨CategoryTheory.Endofunctor.IsoAlgebra.mk K.carrier.obj
        { hom := K.str.hom.hom
          inv := K.str.inv.hom
          hom_inv_id := congrArg (fun f ↦ f.hom) K.str.hom_inv_id
          inv_hom_id := congrArg (fun f ↦ f.hom) K.str.inv_hom_id }, K.carrier.property⟩
    refine ⟨a, ⟨?_⟩⟩
    exact (CategoryTheory.Endofunctor.Algebra.IsIsoStr _).isoMk
      (CategoryTheory.Endofunctor.Algebra.isoMk (Iso.refl _) (by
        apply ObjectProperty.hom_ext
        change G.map (𝟙 K.carrier.obj) ≫ K.str.hom.hom =
          K.str.hom.hom ≫ 𝟙 K.carrier.obj
        rw [G.map_id, Category.id_comp, Category.comp_id]))⟩
  let : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The two heart presentations give the same pullback for normalized exchange squares. -/
private def zlHeartPairsPullComparison
    {C E : Type*} [Category C] [Category E] (G : C ⥤ C) (H : E ⥤ E)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj))
    (hH : ∀ K : Q.FullSubcategory, Q (H.obj K.obj))
    (R : C ⥤ E) (hR : ∀ K : P.FullSubcategory, Q (R.obj K.obj))
    (e : R ⋙ H ≅ G ⋙ R)
    (he : ∀ K : (P.inverseImage
        (CategoryTheory.Endofunctor.IsoAlgebra.forget G)).FullSubcategory,
      (Q.inverseImage (CategoryTheory.Endofunctor.IsoAlgebra.forget H))
        ((CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso e).obj K.obj))
    (a : Q.lift (P.ι ⋙ R) hR ⋙ Q.lift (Q.ι ⋙ H) hH ≅
      P.lift (P.ι ⋙ G) hG ⋙ Q.lift (P.ι ⋙ R) hR)
    (ha : ∀ K, (a.hom.app K).hom = e.hom.app K.obj) :
    zlHeartPairsModel G P hG ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso a ≅
      (Q.inverseImage (CategoryTheory.Endofunctor.IsoAlgebra.forget H)).lift
        ((P.inverseImage (CategoryTheory.Endofunctor.IsoAlgebra.forget G)).ι ⋙
          CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso e) he ⋙
        zlHeartPairsModel H Q hH := by
  refine NatIso.ofComponents (fun K ↦ ?_) ?_
  · refine (CategoryTheory.Endofunctor.Algebra.IsIsoStr _).isoMk ?_
    refine CategoryTheory.Endofunctor.Algebra.isoMk (Iso.refl _) ?_
    apply ObjectProperty.hom_ext
    change H.map (𝟙 _) ≫ (e.hom.app K.obj.carrier ≫ R.map K.obj.str.hom) =
      ((a.hom.app ⟨K.obj.carrier, K.property⟩).hom ≫ R.map K.obj.str.hom) ≫ 𝟙 _
    rw [H.map_id, Category.id_comp, Category.comp_id, ha]
  · intro K M f
    apply ObjectProperty.hom_ext
    apply CategoryTheory.Endofunctor.Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    change R.map f.hom.hom.f ≫ 𝟙 _ = 𝟙 _ ≫ R.map f.hom.hom.f
    exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem zlHeartPairsEquivalence_functor {C : Type*} [Category C] (G : C ⥤ C)
    (P : ObjectProperty C) (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj)) :
    (zlHeartPairsEquivalence G P hG).functor = zlHeartPairsModel G P hG := rfl

attribute [local irreducible] zlHeartPairsEquivalence
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback

private theorem zlHeartFrobeniusEquivalence (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    (zlHeartFrobenius D l hl Qbar Y₀).IsEquivalence := by
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let g := (D.geometricFrobenius Y₀).hom
  let I := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  let := I
  obtain ⟨iX, iY, hc⟩ := isomorphismFieldTransport D l hl Qbar g
  have hiX : iX = I := Subsingleton.elim _ _
  have hiY : iY = I := Subsingleton.elim _ _
  subst iX
  subst iY
  obtain ⟨hX, hY, _, _, S, R, _, ⟨c⟩, ⟨d⟩⟩ := hc
  let F := sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar
  let : F.IsEquivalence := c.equivalence
  have hcH := (constructible_pullback_t_exact D l hl Qbar (Classical.arbitrary _)
    (W := (D.geometricFiber Y₀).left) (X := (D.geometricFiber Y₀).left) (inv g)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hcH
  have hI : constructiblePullbackResidueUnits D l hl (D.geometricFiber Y₀).left = I :=
    Subsingleton.elim _ _
  rw [hI] at hcH
  obtain ⟨H⟩ := hcH
  let P := sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Qbar
  let e : commonStageDerivedPullback l Qbar (inv g) ⋙ F ≅ 𝟭 _ := by
    have de := d.epsilon
    change commonStageDerivedPullback l Qbar (inv g) ⋙
      commonStageDerivedPullback l Qbar (inv (inv g)) ≅ 𝟭 _ at de
    rw [CategoryTheory.IsIso.inv_inv] at de
    exact de
  let : (zlHeartFrobenius D l hl Qbar Y₀).Full := by
    change (P.lift (P.ι ⋙ F) _).Full
    infer_instance
  let : (zlHeartFrobenius D l hl Qbar Y₀).Faithful := by
    change (P.lift (P.ι ⋙ F) _).Faithful
    infer_instance
  let : (zlHeartFrobenius D l hl Qbar Y₀).EssSurj := ⟨fun K ↦ by
    refine ⟨H.heart.obj K, ⟨P.isoMk ?_⟩⟩
    exact F.mapIso ((eqToIso H.heart_fac).app K) ≪≫ e.app K.obj⟩
  exact {}

include hUsep hXsep


omit hUsep hXsep in
private theorem zlFixedPair_exact
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    (G : C ⥤ C) (H : E ⥤ E) [G.IsEquivalence] [H.IsEquivalence]
    (J : C ⥤ E) [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (b : J ⋙ H ≅ G ⋙ J) :
    PreservesFiniteLimits (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso b) ∧
      PreservesFiniteColimits (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso b) := by
  let : G.Additive := Functor.additive_of_preserves_binary_products _
  let : H.Additive := Functor.additive_of_preserves_binary_products _
  exact ⟨CategoryTheory.Endofunctor.IsoAlgebra.preservesFiniteLimits_mapOfNatIso b,
    CategoryTheory.Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso b⟩

private theorem zlOpenWeil_exactAdjunction :
    ∃ J : sfCommonStageWeilSheaf D l hl U₀ Qbar ⥤
        sfCommonStageWeilSheaf D l hl X₀ Qbar,
      PreservesFiniteLimits J ∧ PreservesFiniteColimits J ∧
        Nonempty (J ⊣ zlWeilPull D l hl Qbar j₀) := by
  let := sfWeilPrimeInvertible D l hl U₀
  let := sfWeilPrimeInvertible D l hl X₀
  let : (zlFiberMap D j₀).IsOver (Spec (.of D.k)) := ⟨by
    exact ((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).w⟩
  let : LocallyOfFiniteType (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left ↘
        Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left ↘
        Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : LocallyOfFiniteType (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left ↘
        Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact (((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left ↘
        Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  obtain ⟨J, hlim, hcolim, ⟨a⟩⟩ := commonStageOpenHeartAdjunction D l hl Qbar
    (zlFiberMap D j₀) (zlHeartPull D l hl Qbar j₀) rfl
  let := zlHeartFrobeniusEquivalence D l hl Qbar U₀
  let := zlHeartFrobeniusEquivalence D l hl Qbar X₀
  let := hlim
  let := hcolim
  let hAU : Abelian (sfCommonStageHeart l (D.geometricFiber U₀).left Qbar) :=
    (sfCommonStageHeart_properties l (D.geometricFiber U₀).left Qbar D hl).2.2.some
  let hAX : Abelian (sfCommonStageHeart l (D.geometricFiber X₀).left Qbar) :=
    (sfCommonStageHeart_properties l (D.geometricFiber X₀).left Qbar D hl).2.2.some
  let : Abelian (sfCommonStageHeart l
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left)
        Qbar) := hAU
  let : Abelian (sfCommonStageHeart l
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left)
        Qbar) := hAX
  let alpha := zlHeartSquare D l hl Qbar j₀
  let m := ((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ alpha.hom)).natTrans
  let : IsIso m := isIso_inverseMate_of_equivalences a a alpha
  let beta := (asIso m).symm
  have hm : (mateEquiv a a (TwoSquare.mk _ _ _ _ beta.inv)).natTrans = alpha.hom :=
    congrArg TwoSquare.natTrans ((mateEquiv a a).apply_symm_apply
      (TwoSquare.mk _ _ _ _ alpha.hom))
  obtain ⟨hbLim, hbColim⟩ := zlFixedPair_exact
    (zlHeartFrobenius D l hl Qbar U₀) (zlHeartFrobenius D l hl Qbar X₀) J beta
  let := hbLim
  let := hbColim
  let adj := CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction a beta alpha hm
  let eU := zlHeartPairsEquivalence (sfCommonStageWeilFrobeniusPullback D l hl U₀ Qbar)
    (sfCommonStageHeartProperty l (D.geometricFiber U₀).left Qbar)
    (zlHeartFrobenius_mem D l hl Qbar U₀)
  let eX := zlHeartPairsEquivalence (sfCommonStageWeilFrobeniusPullback D l hl X₀ Qbar)
    (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Qbar)
    (zlHeartFrobenius_mem D l hl Qbar X₀)
  let adj' := eU.toAdjunction.comp (adj.comp eX.symm.toAdjunction)
  have er : eX.functor ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso alpha ≅
      zlWeilPull D l hl Qbar j₀ ⋙ eU.functor := by
    have h := zlHeartPairsPullComparison
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Qbar)
      (sfCommonStageWeilFrobeniusPullback D l hl U₀ Qbar)
      (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Qbar)
      (sfCommonStageHeartProperty l (D.geometricFiber U₀).left Qbar)
      (zlHeartFrobenius_mem D l hl Qbar X₀)
      (zlHeartFrobenius_mem D l hl Qbar U₀)
      (zlPull D l hl Qbar j₀) (zlPull_mem D l hl Qbar j₀)
      (zlFrobeniusSquare D l hl Qbar j₀) (zlWeilPull_mem D l hl Qbar j₀)
      alpha ((zlHeartSquare_existsUnique D l hl Qbar j₀).exists.choose_spec)
    exact isoWhiskerRight (eqToIso (zlHeartPairsEquivalence_functor _ _ _)) _ ≪≫
      h ≪≫ isoWhiskerLeft _ (eqToIso (zlHeartPairsEquivalence_functor _ _ _).symm)
  let er' : (eX.functor ⋙ CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso alpha) ⋙
      eU.inverse ≅ zlWeilPull D l hl Qbar j₀ :=
    isoWhiskerRight er eU.inverse ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ eU.unitIso.symm ≪≫ Functor.rightUnitor _
  exact ⟨_, inferInstance, inferInstance, ⟨adj'.ofNatIsoRight er'⟩⟩



/-- Open extension preserves constructibility, so the Weil-heart pullback has its
canonical left adjoint within the constructible heart.
Source: blueprint proof (1); Stacks 03DJ and 03S5
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: use the exact common-stage open-heart adjunction for the prescribed pullback.
Geometric Frobenius acts by an autoequivalence on both hearts, using its normalized
isomorphism transport and t-exactness of inverse pullback. The inverse mate of the
canonical Frobenius square is therefore invertible. Lift this adjunction to
invertible Frobenius algebras, identify these with the recorded Weil hearts, and
use the normalization equation of the heart square to recover exactly zlWeilPull. -/
theorem zlOpenWeilPull_isRightAdjoint :
    (zlWeilPull D l hl Qbar j₀).IsRightAdjoint := by
  obtain ⟨_, _, _, ⟨a⟩⟩ := zlOpenWeil_exactAdjunction D l hl Qbar j₀
  exact a.isRightAdjoint


/-- The canonical extension by zero, characterized by the open restriction adjunction.
Choosing an adjoint determines the functor up to its unique adjunction isomorphism.
Source: blueprint proof (1) (blueprint: lem-zl-extension-by-zero-punctual). -/
def zlOpenWeilShriek :
    sfCommonStageWeilSheaf D l hl U₀ Qbar ⥤ sfCommonStageWeilSheaf D l hl X₀ Qbar :=
  letI := zlOpenWeilPull_isRightAdjoint D l hl Qbar j₀
  (zlWeilPull D l hl Qbar j₀).leftAdjoint

/-- The chosen open Weil extension inherits exactness from the underlying heart extension.
Source: blueprint proof (1), exact extension by zero
(blueprint: lem-zl-extension-by-zero-punctual).
Proof: lift the exact heart adjunction through the Frobenius square and transport
it across the heart-pair equivalences. Uniqueness of left adjoints identifies this
exact functor with the chosen extension. Finite products imply additivity. -/
theorem zlOpenWeilShriek_exact :
    (zlOpenWeilShriek D l hl Qbar j₀).Additive ∧
      PreservesFiniteLimits (zlOpenWeilShriek D l hl Qbar j₀) ∧
      PreservesFiniteColimits (zlOpenWeilShriek D l hl Qbar j₀) := by
  obtain ⟨J, hlim, hcolim, ⟨a⟩⟩ := zlOpenWeil_exactAdjunction D l hl Qbar j₀
  let := hlim
  let := hcolim
  let := zlOpenWeilPull_isRightAdjoint D l hl Qbar j₀
  let e : J ≅ zlOpenWeilShriek D l hl Qbar j₀ :=
    Adjunction.leftAdjointUniq a (Adjunction.ofIsRightAdjoint _)
  let : PreservesFiniteLimits (zlOpenWeilShriek D l hl Qbar j₀) :=
    preservesFiniteLimits_of_natIso e
  let : PreservesFiniteColimits (zlOpenWeilShriek D l hl Qbar j₀) :=
    preservesFiniteColimits_of_natIso e
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

include hUsep hXsep

/-- Extension by zero is exact on constructible common-stage Weil sheaves, is the
recorded compact-support functor, and has the natural adic fibre formula at every
geometric point. At closed points of the open, its natural finite-stage fibre
comparison intertwines the specified local geometric Frobenius. Consequently it
preserves punctual upper bounds and punctual purity, for every real weight.

Source: blueprint main-20261015, proof of lem-zl-quasi-finite, (1) and (2)
(blueprint: lem-zl-extension-by-zero-punctual).

Proof, in the order of the updated DAG node:
1. Retain finite limits and colimits of the common-stage heart extension in its
   adjunction. Lift the adjunction and exactness through the invertible Frobenius
   algebra construction, and transport across the heart-pair equivalences.
   Uniqueness of left adjoints gives exactness of the prescribed chosen extension;
   preservation of finite products gives additivity.
2. Apply openWeilCarrierRealization to this adjunction. Its coefficient comparison
   identifies every presented carrier with the actual compact-support value.
3. Apply openWeilGeometricFibres to the same adjunction. This supplies normalized
   natural fibres at all algebraically closed geometric fields, the inside-open
   comparison, and the outside-open zero formula.
4. Apply openWeilFiniteStageFrobenius for the finite coefficient extension, its
   common-stage comparison, and the intertwining of the recorded local operators.
5. For either weight clause, openWeilPunctualSpectrum transports an output
   eigenvalue to an input closed point with the same residue cardinality. Apply
   the assumed input inequality or equality and rewrite the cardinality. -/
theorem extensionByZero_punctual (iota : Qbar ≃+* ℂ) :
    (zlOpenWeilShriek D l hl Qbar j₀).Additive ∧
    PreservesFiniteLimits (zlOpenWeilShriek D l hl Qbar j₀) ∧
    PreservesFiniteColimits (zlOpenWeilShriek D l hl Qbar j₀) ∧
    (∀ (F : sfCommonStageWeilSheaf D l hl U₀ Qbar)
      (L : Padic.FiniteCoefficientFields l Qbar)
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber U₀).left),
      Nonempty (F.obj.carrier ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((sfRationalConstructibleLocalization l _ (D.geometricFiber U₀).left).obj K)) →
      Nonempty (((zlOpenWeilShriek D l hl Qbar j₀).obj F).obj.carrier ≅
        sfQbarCompactSupportValue l (X := (D.geometricFiber U₀).left)
          (Y := (D.geometricFiber X₀).left) (f := zlFiberMap D j₀)
          D.k (zlClosurePrimeUnit D l hl) Qbar
          (Compactification.ofIsOpenImmersion (zlFiberMap D j₀)) L K)) ∧
    (∃
      (FU : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        (Spec (.of Ω) ⟶ (D.geometricFiber U₀).left) →
          (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber U₀).left ⥤
            ModuleCat.{max (u + 1) v} Qbar))
      (FX : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        (Spec (.of Ω) ⟶ (D.geometricFiber X₀).left) →
          (generalAlgebraicallyClosedConstructibleCategory l Qbar (D.geometricFiber X₀).left ⥤
            ModuleCat.{max (u + 1) v} Qbar)),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left),
        SfAdicCommonFiberSpec l (D.geometricFiber U₀).left x Qbar (FU Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left),
        SfAdicCommonFiberSpec l (D.geometricFiber X₀).left x Qbar (FX Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left),
        Nonempty (zlOpenWeilShriek D l hl Qbar j₀ ⋙ zlWeilHeartCarrier D l hl Qbar X₀ ⋙
          FX Ω (x ≫ zlFiberMap D j₀) ≅ zlWeilHeartCarrier D l hl Qbar U₀ ⋙ FU Ω x)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left),
        Set.range x.base ⊆ (Set.range (zlFiberMap D j₀).base)ᶜ →
        ∀ F : sfCommonStageWeilSheaf D l hl U₀ Qbar,
          IsZero ((FX Ω x).obj (((zlOpenWeilShriek D l hl Qbar j₀).obj F).obj.carrier)))) ∧
    (∀ L : Padic.FiniteCoefficientFields l Qbar,
      ∃ J : sfWeilSheaf D l hl U₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⥤
          sfWeilSheaf D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L),
      Nonempty (J ⋙ zlFiniteWeilHeartCarrier D l hl _ X₀ ≅
        zlFiniteWeilHeartCarrier D l hl _ U₀ ⋙
          sfCompactSupportFiniteFunctor l (X := (D.geometricFiber U₀).left)
            (Y := (D.geometricFiber X₀).left) (f := zlFiberMap D j₀)
            D.k (zlClosurePrimeUnit D l hl)
            (Compactification.ofIsOpenImmersion (zlFiberMap D j₀))
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)) ∧
      Nonempty (zlWeilHeartStage D l hl Qbar U₀ L ⋙ zlOpenWeilShriek D l hl Qbar j₀ ≅
        J ⋙ zlWeilHeartStage D l hl Qbar X₀ L) ∧
      ∀ (u : {u : U₀.left // u ∈ closedPoints U₀.left})
        (x : {x : X₀.left // x ∈ closedPoints X₀.left})
        (ιU : U₀.left.residueField u.val →+* D.k)
        (hU : ιU.comp (U₀.hom.residueFieldAlgebraMap u.val) = algebraMap D.k₀ D.k)
        (ιX : X₀.left.residueField x.val →+* D.k)
        (hX : ιX.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
        j₀.left.base u.val = x.val →
        localClosedPoint D U₀ u ιU hU ≫ zlFiberMap D j₀ =
          localClosedPoint D X₀ x ιX hX →
        ∃ e : J ⋙ zlClosedCoefficientFiber D l hl _ X₀ x ιX hX ≅
            zlClosedCoefficientFiber D l hl _ U₀ u ιU hU,
          ∀ K : sfWeilSheaf D l hl U₀
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L),
            localClosedFrobeniusCohomology l _ D hl X₀ (J.obj K).obj x ιX hX 0 ≫
                e.hom.app K =
              e.hom.app K ≫ localClosedFrobeniusCohomology l _ D hl U₀ K.obj u ιU hU 0) ∧
    (∀ (w : ℝ) (F : sfCommonStageWeilSheaf D l hl U₀ Qbar),
      (ZlPunctualUpperBound D l hl Qbar U₀ iota F w →
        ZlPunctualUpperBound D l hl Qbar X₀ iota
          ((zlOpenWeilShriek D l hl Qbar j₀).obj F) w) ∧
      (SfIsPunctuallyPureOfWeight D l hl Qbar U₀ iota F w →
        SfIsPunctuallyPureOfWeight D l hl Qbar X₀ iota
          ((zlOpenWeilShriek D l hl Qbar j₀).obj F) w)) := by
  let a : zlOpenWeilShriek D l hl Qbar j₀ ⊣ zlWeilPull D l hl Qbar j₀ :=
    @Adjunction.ofIsRightAdjoint _ _ _ _ (zlWeilPull D l hl Qbar j₀)
      (zlOpenWeilPull_isRightAdjoint D l hl Qbar j₀)
  obtain ⟨hadd, hlim, hcolim⟩ := zlOpenWeilShriek_exact D l hl Qbar j₀
  refine ⟨hadd, hlim, hcolim,
    openWeilCarrierRealization D l hl Qbar j₀ _ a,
    openWeilGeometricFibres D l hl Qbar j₀ _ a,
    openWeilFiniteStageFrobenius D l hl Qbar j₀ _ a, ?_⟩
  intro w F
  constructor
  · intro h x α hα
    obtain ⟨z, hz, he⟩ := openWeilPunctualSpectrum D l hl Qbar j₀ _ a F x α hα
    simpa only [← hz] using h z α he
  · intro h x α hα
    obtain ⟨z, hz, he⟩ := openWeilPunctualSpectrum D l hl Qbar j₀ _ a F x α hα
    simpa only [← hz] using h z α he

end WeilConjectures
