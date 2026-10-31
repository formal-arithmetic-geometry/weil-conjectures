/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleRealization
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution
public import WeilConjectures.AlgebraicGeometry.Native.NativeWeilLocalizingBrownAdjoints
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.LocalizingHomTest

/-! # Constructible and localizing native exceptional adjoints

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, final
exceptional-adjunction sentence and common finite-field passage; Stacks Tags 0037 and 05QR.
(blueprint: lem-sf-native-geometric-brown-constructible-comparison)

The geometric schemes, compactification, locally finite coefficient sheaves and ordinary
derived categories are those of the native framework. The supplied common-stage adjunction
and scalar-extension comparison are the ones in the two realization dependencies.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false

attribute [local irreducible] HasDerivedCategory.standard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Transport

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  (eX : C ≌ C') (eY : D ≌ D') {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (Fc : C' ⥤ D') (α : F ⋙ eY.functor ≅ eX.functor ⋙ Fc)

private def transportLeftIso : (eX.inverse ⋙ F) ⋙ eY.functor ≅ Fc :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft eX.inverse α ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eX.counitIso Fc ≪≫
    Functor.leftUnitor Fc

private def transportAdj : Fc ⊣ eY.inverse ⋙ G ⋙ eX.functor :=
  ((eX.symm.toAdjunction.comp adj).comp eY.toAdjunction).ofNatIsoLeft
    (transportLeftIso eX eY Fc α)

private theorem transportAdj_counit (M : D') :
    (transportAdj eX eY adj Fc α).counit.app M =
      α.inv.app (G.obj (eY.inverse.obj M)) ≫
        eY.functor.map (adj.counit.app (eY.inverse.obj M)) ≫ eY.counitIso.hom.app M := by
  simp only [transportAdj, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, transportLeftIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id, Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit, Equivalence.symm_functor, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  have hn := α.inv.naturality (eX.unitInv.app (G.obj (eY.inverse.obj M)))
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← Fc.map_comp_assoc, ← eX.counit_app_functor]
  simp

private theorem transportAdj_hom (K : C) (M : D')
    (a : Fc.obj (eX.functor.obj K) ⟶ M) :
    (transportAdj eX eY adj Fc α).homEquiv _ _ a =
      eX.functor.map (adj.homEquiv _ _
        (eY.fullyFaithfulFunctor.preimage
          (α.hom.app K ≫ a ≫ eY.counitIso.inv.app M))) := by
  apply ((transportAdj eX eY adj Fc α).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, transportAdj_counit]
  symm
  change (eX.functor ⋙ Fc).map _ ≫ _ = _
  rw [α.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  let r := eY.fullyFaithfulFunctor.preimage
    (α.hom.app K ≫ a ≫ eY.counitIso.inv.app M)
  have hc : F.map (adj.homEquiv _ _ r) ≫ adj.counit.app (eY.inverse.obj M) = r :=
    (adj.homEquiv_counit (g := adj.homEquiv _ _ r)).symm.trans
      ((adj.homEquiv _ _).symm_apply_apply r)
  rw [← eY.functor.map_comp_assoc, hc, eY.fullyFaithfulFunctor.map_preimage]
  simp

end Transport

attribute [local irreducible] transportLeftIso transportAdj

namespace WeilConjectures.NativeGeometricBrown

open LocallyFiniteAdicRealization

variable (l : ℕ) [Fact l.Prime]

/-- Restrict the published realization to its exact bounded constructible image.
Source: Bhatt--Scholze, Proposition 6.8.14, realization dependency
(blueprint: lem-sf-native-geometric-brown-constructible-comparison). -/
def realizationFunctor {T : Scheme.{u}} (R : Realization l T) :=
  (ProEtale.DerivedCategory.boundedAdicConstructible l T).lift R.J
    (fun K ↦ (R.image _).2 ⟨K, ⟨Iso.refl _⟩⟩)

/-- The equivalence supplied by the realization, with no new choice of coefficient category.
Its inverse is a quasi-inverse of this fully faithful, essentially surjective functor.
Source: Bhatt--Scholze, Proposition 6.8.14, realization dependency
(blueprint: lem-sf-native-geometric-brown-constructible-comparison). -/
def realizationEquivalence {T : Scheme.{u}} (R : Realization l T) :
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T ≌
      (ProEtale.DerivedCategory.boundedAdicConstructible l T).FullSubcategory := by
  let J := realizationFunctor l R
  letI : J.Faithful := ⟨fun {A B} {a b} h ↦ (R.fully_faithful _ _).injective
    (congrArg (fun f : J.obj A ⟶ J.obj B ↦ f.hom) h)⟩
  letI : J.Full := ⟨fun f ↦ by
    obtain ⟨g, hg⟩ := (R.fully_faithful _ _).surjective f.hom
    exact ⟨g, InducedCategory.hom_ext hg⟩⟩
  letI : J.EssSurj := ⟨fun M ↦ by
    obtain ⟨K, ⟨e⟩⟩ := (R.image M.obj).1 M.property
    exact ⟨K, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  letI : J.IsEquivalence := {}
  exact J.asEquivalence

/-- The full inclusion of constructible objects into their existing localizing closure.
Source: the ordinary localizing closure convention
(blueprint: lem-sf-native-geometric-brown-constructible-comparison). -/
def inclusion (T : Scheme.{u}) :=
  ObjectProperty.ιOfLE
    (ProEtale.DerivedCategory.boundedAdicConstructible l T).le_localizingClosure

variable {l}

/-- The transported right functor is literally J_X G_stage J_Y inverse.
Source: common-field transport in the final exceptional-adjunction sentence
(blueprint: lem-sf-native-geometric-brown-constructible-comparison). -/
def constructibleRight {X Y : Scheme.{u}} (RX : Realization l X) (RY : Realization l Y)
    (Gs : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X) :=
  (realizationEquivalence l RY).inverse ⋙ Gs ⋙ (realizationEquivalence l RX).functor

/-- The inherited triangulation on native bounded constructible complexes.
Source: the framework's Serre constructible heart and bounded derived subcategory
(blueprint: lem-sf-native-geometric-brown-constructible-comparison). -/
instance constructibleTriangulated (T : Scheme.{u}) [IsLocallyNoetherian T] :
    (ProEtale.DerivedCategory.boundedAdicConstructible l T).IsTriangulated :=
  inferInstanceAs ((DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (ProEtale.adicConstructibleSheaf l T)).IsTriangulated)

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X₀ Y₀ : Scheme.{u}} [X₀.Over (Spec (.of k₀))] [Y₀.Over (Spec (.of k₀))]
  [LocallyOfFiniteType (X₀ ↘ Spec (.of k₀))] [QuasiCompact (X₀ ↘ Spec (.of k₀))]
  [LocallyOfFiniteType (Y₀ ↘ Spec (.of k₀))] [QuasiCompact (Y₀ ↘ Spec (.of k₀))]
  [QuasiSeparated (Y₀ ↘ Spec (.of k₀))]
  (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of k₀))]
  [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
  (RX : Realization l (X₀ ↘ Spec (.of k₀)).geometricFiber)
  (RY : Realization l (Y₀ ↘ Spec (.of k₀)).geometricFiber)
  (Fs : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (X₀ ↘ Spec (.of k₀)).geometricFiber ⥤
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Y₀ ↘ Spec (.of k₀)).geometricFiber)
  (Gs : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Y₀ ↘ Spec (.of k₀)).geometricFiber ⥤
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (X₀ ↘ Spec (.of k₀)).geometricFiber)
  (stageAdj : Fs ⊣ Gs)
  (alpha : Fs ⋙ RY.J ≅ RX.J ⋙ nativeWeilUnderlyingCompactSupport k₀ l f₀
    (nativeWeilChosenCompactification k₀ f₀))

include RX RY Fs alpha in
/-- The actual native compact support preserves the full constructible subcategory.
Source: compact-support realization, first sentence of proof step 1
(blueprint: lem-sf-native-geometric-brown-constructible-comparison).

Proof: write any constructible K as J_X A using RX.image. The comparison alpha identifies
F(J_X A) with J_Y(F_stage A), which is constructible by RY.image. Repleteness transfers
this property along F of the chosen isomorphism. No absolute separatedness is used. -/
theorem preserves_constructible :
    ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l
        (X₀ ↘ Spec (.of k₀)).geometricFiber K →
      ProEtale.DerivedCategory.boundedAdicConstructible l
        (Y₀ ↘ Spec (.of k₀)).geometricFiber
        ((nativeWeilUnderlyingCompactSupport k₀ l f₀
          (nativeWeilChosenCompactification k₀ f₀)).obj K) := by
  intro K hK
  obtain ⟨A, ⟨e⟩⟩ := (RX.image K).1 hK
  exact (RY.image _).2 ⟨Fs.obj A,
    ⟨alpha.app A ≪≫ (nativeWeilUnderlyingCompactSupport k₀ l f₀
      (nativeWeilChosenCompactification k₀ f₀)).mapIso e⟩⟩

/-- Restriction of the actual native compact-support functor, with its original arrows.
Source: compact-support realization and proof step 1
(blueprint: lem-sf-native-geometric-brown-constructible-comparison). -/
def constructibleLeft :=
  (ProEtale.DerivedCategory.boundedAdicConstructible l
    (X₀ ↘ Spec (.of k₀)).geometricFiber).liftFullSubcategory
      (ProEtale.DerivedCategory.boundedAdicConstructible l
        (Y₀ ↘ Spec (.of k₀)).geometricFiber)
      (nativeWeilUnderlyingCompactSupport k₀ l f₀ (nativeWeilChosenCompactification k₀ f₀))
      (preserves_constructible k₀ l f₀ RX RY Fs alpha)

/-- Constructible exceptional adjunction transported to the native coefficient sheaf,
and its counit-transpose comparison with every localizing right adjoint.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final sentence;
Stacks Tags 0037 and 05QR
(blueprint: lem-sf-native-geometric-brown-constructible-comparison).

Proof plan:
1. Transport Hom through J_Y inverse, the fully faithful J_Y, the stage adjunction,
and the fully faithful J_X. For an arbitrary constructible input A, first use the
counit J_X J_X inverse A to represent A in the image. Naturality gives the adjunction
by lem-weil-pbc-adjunction-of-natural-bijection. Its Hom formula below on every stage
input determines the transport on all objects, since J_X is an equivalence.
2. Apply the inverse Hom transport to the identity of G_c M. Full faithfulness gives
the identity of G_stage J_Y inverse M, then the stage counit. The last two inverse
transport steps are alpha inverse and the counit e_Y. This is the displayed formula.
3. For any ambient adjunction, transpose that counit. Naturality of both Hom bijections
makes the transposes a natural transformation t. Naturality in the source says that
postcomposition by t is the composite of the constructible inverse Hom bijection and
the ambient Hom bijection, including every integer shift of a constructible object.
4. Both endpoints belong to the localizing hull. Apply lem-sf-localizing-hom-test to
the constructible class: step 3 supplies bijections from all its integer shifts.
Thus every t_M is invertible and t is a natural isomorphism. Repleteness puts G M
back in the constructible subcategory, with no absolute separatedness hypothesis.
5. By lem-kun-distinguished-cone-zero every distinguished cone Q of t_M is zero.
Consequently every ordinary derived map B[n] to Q vanishes, for B in the hull and
any integer n. All categories below are full ordinary derived subcategories.
-/
theorem native_geometric_brown_constructible_comparison :
    ∃ adj : constructibleLeft k₀ l f₀ RX RY Fs alpha ⊣ constructibleRight RX RY Gs,
      (∀ (K : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
          (X₀ ↘ Spec (.of k₀)).geometricFiber)
        (M : (ProEtale.DerivedCategory.boundedAdicConstructible l
          (Y₀ ↘ Spec (.of k₀)).geometricFiber).FullSubcategory)
        (a : (constructibleLeft k₀ l f₀ RX RY Fs alpha).obj
            ((realizationEquivalence l RX).functor.obj K) ⟶ M),
        (adj.homEquiv _ _ a).hom = RX.J.map
          (stageAdj.homEquiv _ _
            ((Equiv.ofBijective RY.J.map (RY.fully_faithful _ _)).symm
              (alpha.hom.app K ≫ a.hom ≫
                ((realizationEquivalence l RY).counitIso.inv.app M).hom)))) ∧
      (∀ M, (adj.counit.app M).hom =
        alpha.inv.app (Gs.obj ((realizationEquivalence l RY).inverse.obj M)) ≫
          RY.J.map (stageAdj.counit.app ((realizationEquivalence l RY).inverse.obj M)) ≫
          ((realizationEquivalence l RY).counitIso.hom.app M).hom) ∧
      ∀ (hL : ∀ K, nativeWeilUnderlyingHull k₀ l X₀ K →
          nativeWeilUnderlyingHull k₀ l Y₀
            ((nativeWeilUnderlyingCompactSupport k₀ l f₀
              (nativeWeilChosenCompactification k₀ f₀)).obj K))
        (G : (nativeWeilUnderlyingHull k₀ l Y₀).FullSubcategory ⥤
          (nativeWeilUnderlyingHull k₀ l X₀).FullSubcategory)
        (ambientAdj : (nativeWeilUnderlyingHull k₀ l X₀).liftFullSubcategory
          (nativeWeilUnderlyingHull k₀ l Y₀)
          (nativeWeilUnderlyingCompactSupport k₀ l f₀
            (nativeWeilChosenCompactification k₀ f₀)) hL ⊣ G),
        ∃ t : constructibleRight RX RY Gs ⋙
            inclusion l (X₀ ↘ Spec (.of k₀)).geometricFiber ≅
          inclusion l (Y₀ ↘ Spec (.of k₀)).geometricFiber ⋙ G,
          (∀ M, t.hom.app M = ambientAdj.homEquiv
            ((constructibleRight RX RY Gs ⋙ inclusion l
              (X₀ ↘ Spec (.of k₀)).geometricFiber).obj M)
            ((inclusion l (Y₀ ↘ Spec (.of k₀)).geometricFiber).obj M)
            (ObjectProperty.homMk (adj.counit.app M).hom)) ∧
          (∀ M, ProEtale.DerivedCategory.boundedAdicConstructible l
            (X₀ ↘ Spec (.of k₀)).geometricFiber
            (G.obj ((inclusion l (Y₀ ↘ Spec (.of k₀)).geometricFiber).obj M)).obj) ∧
          (∀ (M : (ProEtale.DerivedCategory.boundedAdicConstructible l
              (Y₀ ↘ Spec (.of k₀)).geometricFiber).FullSubcategory)
            (A : (ProEtale.DerivedCategory.boundedAdicConstructible l
              (X₀ ↘ Spec (.of k₀)).geometricFiber).FullSubcategory)
            (n : ℤ) (a : A⟦n⟧ ⟶ (constructibleRight RX RY Gs).obj M),
            ((inclusion l (X₀ ↘ Spec (.of k₀)).geometricFiber).map a) ≫
                t.hom.app M =
              ambientAdj.homEquiv
                ((inclusion l (X₀ ↘ Spec (.of k₀)).geometricFiber).obj (A⟦n⟧))
                ((inclusion l (Y₀ ↘ Spec (.of k₀)).geometricFiber).obj M)
                (ObjectProperty.homMk ((adj.homEquiv _ _).symm a).hom)) ∧
          (∀ (M : (ProEtale.DerivedCategory.boundedAdicConstructible l
              (Y₀ ↘ Spec (.of k₀)).geometricFiber).FullSubcategory)
            (Q : (nativeWeilUnderlyingHull k₀ l X₀).FullSubcategory)
            (b : (G.obj ((inclusion l
              (Y₀ ↘ Spec (.of k₀)).geometricFiber).obj M)) ⟶ Q)
            (d : Q ⟶ ((constructibleRight RX RY Gs ⋙ inclusion l
              (X₀ ↘ Spec (.of k₀)).geometricFiber).obj M)⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk (t.hom.app M) b d ∈ distTriang _ →
              ∀ (B : (nativeWeilUnderlyingHull k₀ l X₀).FullSubcategory)
                (n : ℤ) (a : B⟦n⟧ ⟶ Q), a = 0) := by
  let eX := realizationEquivalence l RX
  let eY := realizationEquivalence l RY
  let Fc := constructibleLeft k₀ l f₀ RX RY Fs alpha
  let αc : Fs ⋙ eY.functor ≅ eX.functor ⋙ Fc :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (alpha.app K)) (by
      intro K L a
      apply InducedCategory.hom_ext
      exact alpha.hom.naturality a)
  let adj := transportAdj eX eY stageAdj Fc αc
  refine ⟨adj, ?_, ?_, ?_⟩
  · intro K M a
    have h := congrArg (fun f ↦ f.hom) (transportAdj_hom eX eY stageAdj Fc αc K M a)
    refine h.trans ?_
    apply congrArg RX.J.map
    apply congrArg (stageAdj.homEquiv _ _)
    apply (RY.fully_faithful _ _).injective
    change (eY.functor.map (eY.fullyFaithfulFunctor.preimage _)).hom = _
    rw [eY.fullyFaithfulFunctor.map_preimage]
    exact ((Equiv.ofBijective RY.J.map (RY.fully_faithful _ _)).apply_symm_apply _).symm
  · intro M
    exact congrArg (fun f ↦ f.hom) (transportAdj_counit eX eY stageAdj Fc αc M)
  · intro hL G ambientAdj
    let iX := inclusion l (X₀ ↘ Spec (.of k₀)).geometricFiber
    let iY := inclusion l (Y₀ ↘ Spec (.of k₀)).geometricFiber
    let Gc := eY.inverse ⋙ Gs ⋙ eX.functor
    let t : Gc ⋙ iX ⟶ iY ⋙ G :=
      { app := fun M ↦ ambientAdj.homEquiv _ _ (ObjectProperty.homMk (adj.counit.app M).hom)
        naturality := by
          intro M N v
          dsimp only [Functor.comp_map]
          rw [← ambientAdj.homEquiv_naturality_left,
            ← ambientAdj.homEquiv_naturality_right]
          congr 1
          apply InducedCategory.hom_ext
          exact congrArg (fun f ↦ f.hom) (adj.counit.naturality v) }
    have htranspose (A) (M) (a : A ⟶ Gc.obj M) :
        iX.map a ≫ t.app M = ambientAdj.homEquiv (iX.obj A) (iY.obj M)
          (ObjectProperty.homMk ((adj.homEquiv _ _).symm a).hom) := by
      change iX.map a ≫ ambientAdj.homEquiv _ _ _ = _
      rw [← ambientAdj.homEquiv_naturality_left]
      congr 1
    have hiso (M) : IsIso (t.app M).hom := by
      apply ObjectProperty.isIso_of_bijective_postcomp_shift_generators
        (ProEtale.DerivedCategory.boundedAdicConstructible l
          (X₀ ↘ Spec (.of k₀)).geometricFiber)
        (t.app M).hom ((iX.obj (Gc.obj M)).property) ((G.obj (iY.obj M)).property)
      intro A hA n
      let Ac : (ProEtale.DerivedCategory.boundedAdicConstructible l
          (X₀ ↘ Spec (.of k₀)).geometricFiber).FullSubcategory :=
        ⟨A⟦n⟧, ObjectProperty.le_shift _ n A hA⟩
      let e₁ : (A⟦n⟧ ⟶ (iX.obj (Gc.obj M)).obj) ≃ (Ac ⟶ Gc.obj M) :=
        { toFun := fun a ↦ (ObjectProperty.homMk a : Ac ⟶ Gc.obj M)
          invFun := fun a ↦ a.hom
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      let e₂ : ((iX.obj Ac) ⟶ G.obj (iY.obj M)) ≃
          (A⟦n⟧ ⟶ (G.obj (iY.obj M)).obj) :=
        { toFun := fun a ↦ a.hom
          invFun := fun a ↦
            (ObjectProperty.homMk a : iX.obj Ac ⟶ G.obj (iY.obj M))
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      let e₃ : (Fc.obj Ac ⟶ M) ≃
          ((((nativeWeilUnderlyingHull k₀ l X₀).liftFullSubcategory
            (nativeWeilUnderlyingHull k₀ l Y₀)
            (nativeWeilUnderlyingCompactSupport k₀ l f₀
              (nativeWeilChosenCompactification k₀ f₀)) hL).obj (iX.obj Ac)) ⟶ iY.obj M) :=
        { toFun := fun a ↦ ObjectProperty.homMk a.hom
          invFun := fun a ↦ ObjectProperty.homMk a.hom
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      convert (e₁.trans ((adj.homEquiv Ac M).symm.trans
        (e₃.trans ((ambientAdj.homEquiv _ _).trans e₂)))).bijective using 1 <;> try rfl
      all_goals
        funext a
        exact congrArg (fun f ↦ f.hom) (htranspose Ac M (e₁ a))
    have : ∀ M, IsIso (t.app M) := fun M ↦
      (ObjectProperty.isIso_hom_iff _).1 (hiso M)
    have : IsIso t := NatIso.isIso_of_isIso_app t
    refine ⟨asIso t, (fun _ ↦ rfl), ?_, ?_, ?_⟩
    · intro M
      obtain ⟨K, ⟨e⟩⟩ := (RX.image _).1 (Gc.obj M).property
      exact (RX.image _).2 ⟨K, ⟨e ≪≫ asIso (t.app M).hom⟩⟩
    · intro M A n a
      exact htranspose (A⟦n⟧) M a
    · intro M Q b d hT B n a
      have hQ := (Pretriangulated.Triangle.isZero₃_iff_isIso₁
        (Pretriangulated.Triangle.mk (t.app M) b d) hT).2 (inferInstance : IsIso (t.app M))
      exact hQ.eq_of_tgt a 0

end WeilConjectures.NativeGeometricBrown
