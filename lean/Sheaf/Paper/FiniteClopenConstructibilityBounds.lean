/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.ClopenStratificationModels
import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import all Sheaf.Paper.FiniteCtfTriangulated
import all Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Paper.ProEtaleCanonicalTensorPullback

/-! # Finite-clopen constructibility and fixed interval bounds

Source: main-20261015 blueprint, sec-six-functors-basics/sk-def-purity-conv,
def-pur-section-invariant, final invertibility assertion; Stacks Tags 005J and 09YD
(blueprint: lem-pur-clopen-finite-constructibility-bounds).

All restrictions are the published ordinary inverse images with their canonical
constant-section coefficient comparison. The derived functors descend exact termwise
restriction. Stratification comparisons retain the immersed subschemes, not just their images.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

-- Use the fixed pro-etale coefficient universe instead of the generic clopen universe.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ZeroObject

namespace WeilConjectures.PurityFiniteSetting

/-- The existing positive-level coefficient quotient is finite. This instance only
exposes its recorded finiteness proof for the constructibility predicates.
Source: blueprint def-pur-section-invariant, finite coefficient paragraph
(blueprint: lem-pur-clopen-finite-constructibility-bounds). -/
instance finiteClopenCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Uniqueness of left adjoints compares actual inverse image with site composition. -/
private theorem ordinaryClopenComparison {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    ∃ e : ProEt.FiniteClopenTensor.Modules.{u, u}
        ((ProEt.FiniteClopenTensor.rings.{u, u} j).obj (proEtaleConstantRing X A)) ≌
          proEtaleRingModules Y (proEtaleConstantRing Y A),
      Nonempty (proEtaleConstantRingPullback A j ≅
        ProEt.FiniteClopenTensor.restriction.{u, u} j (proEtaleConstantRing X A) ⋙ e.functor) := by
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing Y A
  let B := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
  let G : Y.ProEt ⥤ X.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let : G.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).IsContinuous
      (ProEt.topology X) (ProEt.topology Y) := ProEt.isContinuous_overPullback j
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology Y) (ProEt.topology X)
  let c₀ := ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).leftAdjointUniq b).app R
  let V := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let c : V.obj B ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) := V.mapIso c₀
  let ψ : ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      ((proEtaleBaseChange j).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology Y)).obj (V.obj B) :=
    ⟨Functor.whiskerRight
      ((proEtaleSheafAdjunction j CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj =
      ψ.hom ≫ (proEtaleBaseChange j).op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    have hc := Adjunction.unit_leftAdjointUniq_hom_app
      (proEtaleSheafAdjunction j CommRingCat.{u + 1}) b R
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app U)) hc.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) (V.obj B).obj = 𝟙 _ := by
    apply NatTrans.ext
    funext U
    apply (cancel_mono (c.hom.hom.app U)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app U.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun f ↦ f.app (G.op.obj U)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj U))
      (c.hom.hom.app ((proEtaleBaseChange j).op.obj (G.op.obj U)))
      (((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.map
          (G.map (a.unit.app U.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app U ≫ ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.map
        (𝟙 (G.op.obj U)) = c.hom.hom.app U
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id (c.hom.hom.app U)
  let d : SheafOfModules.pushforward.{u + 1} (F := G) c.hom ⊣
      SheafOfModules.pushforward.{u + 1} ψ :=
    SheafOfModules.pushforwardPushforwardAdj
      (F := G) (G := proEtaleBaseChange j) a c.hom ψ H₁ H₂
  let z : proEtaleModuleInverseImage j R ⊣ SheafOfModules.pushforward.{u + 1} ψ :=
    (proEtaleModuleInverseImageAdjunction j R).ofNatIsoRight
    (SheafOfModules.pushforwardCongr (by simp [ψ, proEtaleRingDirectImageMap]))
  let h := z.leftAdjointUniq d
  let E₀ := proEtaleScalarEquivalence Y c
  let E₁ := proEtaleScalarEquivalence Y (V.mapIso (proEtaleConstantRingComparison j A))
  let e := E₀.trans E₁.symm
  have p : proEtaleConstantRingPullback A j ≅
      proEtaleModuleInverseImage j R ⋙ E₁.inverse :=
    Functor.isoWhiskerLeft (proEtaleModuleInverseImage j R)
    ((proEtaleRingExtensionAdjunction j R S (proEtaleConstantRingComparison j A)).leftAdjointUniq
      E₁.symm.toAdjunction)
  have hE₀ : E₀.functor = SheafOfModules.pushforward.{u + 1}
      (F := 𝟭 Y.ProEt) c.hom := rfl
  have t : ProEt.FiniteClopenTensor.restriction.{u, u} j R ⋙ E₀.functor ≅
      SheafOfModules.pushforward.{u + 1} (F := G) c.hom := by
    rw [hE₀]
    refine NatIso.ofComponents (fun M ↦
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl))) ?_
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  have h' : proEtaleModuleInverseImage j R ≅
      ProEt.FiniteClopenTensor.restriction.{u, u} j R ⋙ E₀.functor := h ≪≫ t.symm
  exact ⟨e, ⟨p ≪≫ Functor.isoWhiskerRight h' E₁.inverse ≪≫
    Functor.associator _ _ _⟩⟩

private theorem ordinaryClopenEquivalence
    (X : Scheme.{u}) {I : Type w} [Finite I] (Xi : I → Scheme.{u})
    (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : (⋃ i, Set.range (j i)) = Set.univ) (A : Type u) [CommRing A] :
    ∃ E : proEtaleRingModules X (proEtaleConstantRing X A) ≌
        (∀ i, proEtaleRingModules (Xi i) (proEtaleConstantRing (Xi i) A)),
      E.functor = Functor.pi' (fun i ↦ proEtaleConstantRingPullback A (j i)) := by
  classical
  choose e he using fun i ↦ ordinaryClopenComparison (j i) A
  obtain ⟨E₀, hE₀⟩ := ProEt.FiniteClopenTensor.moduleGluing.{u, u, w}
    X I Xi j hd (fun x ↦ Set.mem_iUnion.mp (hc.symm ▸ Set.mem_univ x))
    (proEtaleConstantRing X A)
  let E := E₀.trans (CategoryTheory.Equivalence.pi e)
  have h : E.functor ≅ Functor.pi' (fun i ↦ proEtaleConstantRingPullback A (j i)) := by
    change E₀.functor ⋙ Functor.pi (fun i ↦ (e i).functor) ≅ _
    rw [hE₀]
    exact NatIso.pi' (fun i ↦ (he i).some.symm)
  exact ⟨E.changeFunctor h, rfl⟩

/-- Restrict a product equivalence while retaining its specified forward functor. -/
private theorem restrictProductEquivalence
    {C : Type*} [Category C] {J : Type*} {D : J → Type*} [∀ i, Category (D i)]
    (r : ∀ i, C ⥤ D i) (E : C ≌ ∀ i, D i)
    (hE : E.functor = Functor.pi' r) (P : ObjectProperty C)
    (Q : ∀ i, ObjectProperty (D i))
    (hP : ∀ K, P K ↔ ∀ i, Q i ((r i).obj K))
    (hQ : ∀ i {K L : D i}, (K ≅ L) → Q i K → Q i L) :
    ∃ e : P.FullSubcategory ≌ ∀ i, (Q i).FullSubcategory,
      Nonempty (e.functor ⋙ Functor.pi (fun i ↦ (Q i).ι) ≅
        P.ι ⋙ Functor.pi' r) := by
  let E := E.changeFunctor (eqToIso hE)
  let F : P.FullSubcategory ⥤ ∀ i, (Q i).FullSubcategory :=
    Functor.pi' (fun i ↦ (Q i).lift (P.ι ⋙ r i) (fun K ↦ (hP K.obj).mp K.property i))
  let G : (∀ i, (Q i).FullSubcategory) ⥤ P.FullSubcategory :=
    P.lift (Functor.pi (fun i ↦ (Q i).ι) ⋙ E.inverse) (fun K ↦ (hP _).mpr
      (fun i ↦ hQ i ((Pi.eval D i).mapIso
        (E.counitIso.app (fun i ↦ (K i).obj))).symm (K i).property))
  have η : 𝟭 _ ≅ F ⋙ G := by
    refine NatIso.ofComponents (fun K ↦ P.isoMk (E.unitIso.app K.obj)) ?_
    intro K L f
    apply ObjectProperty.hom_ext
    exact E.unitIso.hom.naturality f.hom
  have ε : G ⋙ F ≅ 𝟭 _ := by
    refine NatIso.ofComponents (fun K ↦ Pi.isoMk (fun i ↦
      (Q i).isoMk ((Pi.eval D i).mapIso (E.counitIso.app (fun i ↦ (K i).obj))))) ?_
    intro K L f
    funext i
    apply ObjectProperty.hom_ext
    exact congrFun (E.counitIso.hom.naturality (fun i ↦ (f i).hom)) i
  exact ⟨CategoryTheory.Equivalence.mk F G η ε, ⟨Iso.refl _⟩⟩

private noncomputable abbrev clopenTensor (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  @CategoryTheory.MonoidalCategory.tensor (proEtaleDerivedCategory X A) _
    (RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (ProEt.topology X) (proEtaleConstantRing X A))

private noncomputable def clopenTensorModel (X : Scheme.{u}) (A : Type u) [CommRing A] :
    ProEtaleTensorModel X (proEtaleConstantRing X A) where
  tensor := clopenTensor X A
  representative := NatIso.ofComponents (fun Z ↦
    RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2} (ProEt.topology X)
      (proEtaleConstantRing X A) Z.1.obj Z.2.obj (Or.inl Z.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality _ _ _ _ _ _ _ _ f.1.hom f.2.hom)

/-- Compare the published resolution tests with the native derived tensor. -/
private theorem clopenTorTest (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ) :
    HasProEtaleTorAmplitude X A K a b ↔ a ≤ b ∧
      ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (m : ℤ),
        m < a ∨ b < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj
          ((clopenTensor X A).obj (K, (DerivedCategory.singleFunctor _ 0).obj M))) := by
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} (ProEt.topology X) R
  have comp (L P : CochainComplex C ℤ) (e : DerivedCategory.Q.obj L ≅ K)
      (f : P ⟶ L) (hf : QuasiIso f) (hP : P.IsAcyclicTensorKFlat) (M : C) :
      derivedTensor X A L ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP ≅
        (clopenTensor X A).obj (K, (DerivedCategory.singleFunctor _ 0).obj M) := by
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C f).mpr hf
    exact RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2}
        (ProEt.topology X) R P ((HomologicalComplex.single C (.up ℤ) 0).obj M)
        (Or.inl hP) ≪≫
      (clopenTensor X A).mapIso (Iso.prod (asIso (DerivedCategory.Q.map f) ≪≫ e)
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M).symm)
  constructor
  · intro h
    refine ⟨h.1, fun M m hm ↦ ?_⟩
    let L := (DerivedCategory.Q (C := C)).objPreimage K
    let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
    obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
    exact (h.2 L P ⟨e⟩ f hf hP M m hm).of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso (comp L P e f hf hP M)).symm
  · rintro ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    rintro L P ⟨e⟩ f hf hP M m hm
    exact (h M m hm).of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso (comp L P e f hf hP M))

/-- Constructibility and the same prescribed cohomological and Tor intervals are
componentwise on a finite clopen partition. The last two equivalences are required
to induce the actual derived restriction after forgetting full-subcategory membership.
The strata comparisons identify immersions, hence retain the same locally constant
module models and their restricted trivializations.

Source: main-20261015 blueprint, def-pur-section-invariant, final invertibility assertion
(blueprint: lem-pur-clopen-finite-constructibility-bounds).

Proof:
1. A clopen component is retrocompact: its intersection with a quasi-compact open is
closed in that open. Restrict constructible strata by Stacks 005J and base change
open and closed immersions. Conversely compose their immersions with the clopen
inclusion and apply Stacks 09YD. The displayed isomorphisms preserve scheme structures.
2. Restrict a constructibility stratification and its trivializing covers by base change
on the small pro-etale site; the finite module models stay the same.
3. Conversely unite the finitely many component stratifications. Their disjointness
and covering properties give a stratification of X with the original finite models.
4. Use lem-pur-clopen-ringed-module-gluing and
lem-pur-finite-product-derived-tensor-calculus: exact restriction commutes with each
cohomology sheaf and jointly detects zero. Apply the sheaf criterion in every degree.
This detects unbounded constructible cohomology and any fixed cohomological interval.
5. For any degree-zero global module M, restrict K tensor M and use the component
Tor hypotheses and tensor comparison. Joint detection of zero gives global Tor bounds.
6. For the converse, insert an arbitrary degree-zero module from one component,
using zero insertion from lem-pur-clopen-ringed-module-gluing. Restrict its tensor
with K. The result is the component tensor, so every component test is covered.
7. Restrict the unbounded equivalence to bounded constructible and finite-Tor objects.
For finitely many different intervals take their minimum lower and maximum upper
endpoints. Any already common interval is preserved by the fixed-interval clauses.
8. Empty components have zero module and derived categories. An empty index type
forces X empty. Use the empty stratification, or one empty stratum for the positive
stratum convention. The zero module is finite and locally constant; all its cohomology
and all its derived tensors vanish, for every ordered interval. No minimum is needed.
-/
theorem finite_clopen_constructibility_bounds
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    {I : Type w} [Finite I] (Xi : I → Scheme.{u}) (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i)) (Set.range (j i')))
    (hcover : (⋃ i, Set.range (j i)) = Set.univ) :
    (∀ (S : Stratification X) (i : I),
      ∃ (T : Stratification (Xi i)) (e : Fin T.n ≃ Fin S.n),
        ∀ t : Fin T.n, ∃ d : T.domain t ≅ pullback (S.immersion (e t)) (j i),
          d.hom ≫ pullback.snd (S.immersion (e t)) (j i) = T.immersion t) ∧
    (∀ S : ∀ i, Stratification (Xi i),
      ∃ (T : Stratification X) (e : Fin T.n ≃ Σ i, Fin (S i).n),
        ∀ t : Fin T.n,
          ∃ d : T.domain t ≅ (S (e t).1).domain (e t).2,
            d.hom ≫ (S (e t).1).immersion (e t).2 ≫ j (e t).1 = T.immersion t) ∧
    (∀ F : proEtaleRingModules X (proEtaleConstantRing X P.Ring),
      IsConstructibleProEtaleModuleSheaf X P.Ring F ↔
        ∀ i, IsConstructibleProEtaleModuleSheaf (Xi i) P.Ring
          ((proEtaleConstantRingPullback P.Ring (j i)).obj F)) ∧
    (∀ K : proEtaleDerivedCategory X P.Ring,
      (∀ m : ℤ, IsConstructibleProEtaleModuleSheaf X P.Ring
        ((DerivedCategory.homologyFunctor _ m).obj K)) ↔
      ∀ (i : I) (m : ℤ), IsConstructibleProEtaleModuleSheaf (Xi i) P.Ring
        ((DerivedCategory.homologyFunctor _ m).obj
          ((proEtaleConstantRingDerivedPullback P.Ring (j i)).obj K))) ∧
    (∀ (K : proEtaleDerivedCategory X P.Ring) (a b : ℤ), a ≤ b →
      (proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, proEtaleCohomologicalSupport
          ((proEtaleConstantRingDerivedPullback P.Ring (j i)).obj K) ⊆ Set.Icc a b)) ∧
    (∀ (K : proEtaleDerivedCategory X P.Ring) (a b : ℤ), a ≤ b →
      (HasProEtaleTorAmplitude X P.Ring K a b ↔
        ∀ i, HasProEtaleTorAmplitude (Xi i) P.Ring
          ((proEtaleConstantRingDerivedPullback P.Ring (j i)).obj K) a b)) ∧
    (∃ e : (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X).FullSubcategory ≌
        (∀ i, (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
          P.level P.level_pos (Xi i)).FullSubcategory),
      Nonempty (e.functor ⋙ Functor.pi (fun i ↦
          (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
            P.level P.level_pos (Xi i)).ι) ≅
        (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension P.level P.level_pos X).ι ⋙
          Functor.pi' (fun i ↦ proEtaleConstantRingDerivedPullback P.Ring (j i)))) ∧
    (∃ e : (finiteTorConstructible P.coefficients.l P.extension P.level
        P.level_pos X).FullSubcategory ≌
        (∀ i, (finiteTorConstructible P.coefficients.l P.extension P.level
          P.level_pos (Xi i)).FullSubcategory),
      Nonempty (e.functor ⋙ Functor.pi (fun i ↦
          (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos (Xi i)).ι) ≅
        (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X).ι ⋙
          Functor.pi' (fun i ↦ proEtaleConstantRingDerivedPullback P.Ring (j i)))) ∧
    (∀ (K : proEtaleDerivedCategory X P.Ring), IsZero K →
      ∀ a b : ℤ, a ≤ b →
        proEtaleCohomologicalSupport K ⊆ Set.Icc a b ∧
        HasProEtaleTorAmplitude X P.Ring K a b) := by
  classical
  let := Fintype.ofFinite I
  have hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))) :=
    hdisjoint
  let toFinite {Y : Scheme.{u}} (S : Stratification Y) :
      FiniteLocallyClosedStratification Y :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  let r := fun i ↦ proEtaleConstantRingPullback P.Ring (j i)
  let rd := fun i ↦ proEtaleConstantRingDerivedPullback P.Ring (j i)
  obtain ⟨E, hE⟩ := ordinaryClopenEquivalence X Xi j hd hcover P.Ring
  have hz (M : proEtaleRingModules X (proEtaleConstantRing X P.Ring)) :
      IsZero M ↔ ∀ i, IsZero ((r i).obj M) := by
    constructor
    · intro h i
      exact (r i).map_isZero h
    · intro h
      apply IsZero.of_full_of_faithful_of_isZero E.functor M
      rw [hE]
      refine ⟨fun N ↦ ?_, fun N ↦ ?_⟩
      · exact ⟨⟨⟨fun i ↦ (h i).to_ (N i)⟩, fun f ↦ funext fun i ↦
          (h i).eq_of_src _ _⟩⟩
      · exact ⟨⟨⟨fun i ↦ (h i).from_ (N i)⟩, fun f ↦ funext fun i ↦
          (h i).eq_of_tgt _ _⟩⟩
  have hh (K : proEtaleDerivedCategory X P.Ring) (m : ℤ) :
      IsZero ((DerivedCategory.homologyFunctor _ m).obj K) ↔
        ∀ i, IsZero ((DerivedCategory.homologyFunctor _ m).obj ((rd i).obj K)) := by
    rw [hz]
    exact forall_congr' fun i ↦
      (((r i).mapDerivedCategoryHomologyFunctorIso m).app K).isZero_iff
  have hs (K : proEtaleDerivedCategory X P.Ring) :
      proEtaleCohomologicalSupport K =
        ⋃ i, proEtaleCohomologicalSupport ((rd i).obj K) := by
    ext m
    simp only [proEtaleCohomologicalSupport, Set.mem_ofPred_eq, Set.mem_iUnion,
      hh, not_forall]
  have hf (K : proEtaleDerivedCategory X P.Ring) :
      (proEtaleCohomologicalSupport K).Finite ↔
        ∀ i, (proEtaleCohomologicalSupport ((rd i).obj K)).Finite := by
    rw [hs]
    exact ⟨fun h i ↦ h.subset (Set.subset_iUnion
        (fun i ↦ proEtaleCohomologicalSupport ((rd i).obj K)) i), Set.finite_iUnion⟩
  have hr : JointlyReflectIsomorphisms r := by
    constructor
    intro M N f h
    have : IsIso (E.functor.map f) := by
      rw [hE]
      exact (isIso_pi_iff _).mpr h
    exact isIso_of_reflects_iso f E.functor
  let := ProEt.FiniteClopenTensor.piPreadditive
    (fun i ↦ proEtaleRingModules (Xi i) (proEtaleConstantRing (Xi i) P.Ring))
  have hA : E.functor.Additive := by
    constructor
    intro M N f g
    rw [hE]
    funext i
    exact (r i).map_add
  let := hA
  have hD := ProEt.FiniteClopenTensor.derivedPi_isEquivalence r E.inverse
    (fun M N ↦ E.inverse.map_zero M N)
    (by simpa only [hE] using E.unitIso)
    (by simpa only [hE] using E.counitIso) hr
  let := hD
  let ED := (Functor.pi' rd).asEquivalence
  have tensorComp (i : I) (K : proEtaleDerivedCategory X P.Ring)
      (M : proEtaleRingModules X (proEtaleConstantRing X P.Ring)) :
      (rd i).obj ((clopenTensor X P.Ring).obj
        (K, (DerivedCategory.singleFunctor _ 0).obj M)) ≅
      (clopenTensor (Xi i) P.Ring).obj
        ((rd i).obj K, (DerivedCategory.singleFunctor _ 0).obj ((r i).obj M)) :=
    (proEtaleCanonicalTensorPullback (j i) _ _ (proEtaleConstantRingComparison (j i) P.Ring)
      (clopenTensorModel X P.Ring) (clopenTensorModel (Xi i) P.Ring)).2.choose.app
        (K, (DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (clopenTensor (Xi i) P.Ring).mapIso
        (Iso.prod (Iso.refl _) (((r i).mapDerivedCategorySingleFunctor 0).app M))
  have ht (K : proEtaleDerivedCategory X P.Ring) (a b : ℤ) (hab : a ≤ b) :
      HasProEtaleTorAmplitude X P.Ring K a b ↔
        ∀ i, HasProEtaleTorAmplitude (Xi i) P.Ring ((rd i).obj K) a b := by
    constructor
    · intro h i
      refine (clopenTorTest _ _ _ _ _).mpr ⟨hab, fun N m hm ↦ ?_⟩
      let V := fun k ↦ @dite (proEtaleRingModules (Xi k)
        (proEtaleConstantRing (Xi k) P.Ring)) (i = k) (Classical.propDecidable _)
        (fun h ↦ h ▸ N) (fun _ ↦ 0)
      let M := E.inverse.obj V
      have e : (r i).obj M ≅ N := by
        have he := (Pi.eval _ i).mapIso (E.counitIso.app V)
        rw [hE] at he
        exact he ≪≫ eqToIso (by simp [V])
      have hM := ((clopenTorTest _ _ _ _ _).mp h).2 M m hm
      have hc := tensorComp i K M ≪≫ (clopenTensor (Xi i) P.Ring).mapIso
        (Iso.prod (Iso.refl _) ((DerivedCategory.singleFunctor _ 0).mapIso e))
      exact ((hh _ m).mp hM i).of_iso
        ((DerivedCategory.homologyFunctor _ m).mapIso hc).symm
    · intro h
      refine (clopenTorTest _ _ _ _ _).mpr ⟨hab, fun M m hm ↦ ?_⟩
      apply (hh _ m).mpr
      intro i
      exact (((clopenTorTest _ _ _ _ _).mp (h i)).2 ((r i).obj M) m hm).of_iso
        ((DerivedCategory.homologyFunctor _ m).mapIso (tensorComp i K M))
  have hc (K : proEtaleDerivedCategory X P.Ring) :
      (∀ m : ℤ, IsConstructibleProEtaleModuleSheaf X P.Ring
        ((DerivedCategory.homologyFunctor _ m).obj K)) ↔
      ∀ i m, IsConstructibleProEtaleModuleSheaf (Xi i) P.Ring
        ((DerivedCategory.homologyFunctor _ m).obj ((rd i).obj K)) := by
    have hcf (m : ℤ) := isConstructibleProEtaleModuleSheaf_iff_clopen X I Xi j hd hcover
      P.Ring ((DerivedCategory.homologyFunctor _ m).obj K)
    have he (i : I) (m : ℤ) := ((r i).mapDerivedCategoryHomologyFunctorIso m).app K
    constructor
    · intro h i m
      exact constructibleProEtale_of_iso _ _ (he i m) ((hcf m).mp (h m) i)
    · intro h m
      exact (hcf m).mpr (fun i ↦ constructibleProEtale_of_iso _ _ (he i m).symm (h i m))
  let B := fun Y ↦ intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
    P.level P.level_pos Y
  let T := fun Y ↦ finiteTorConstructible P.coefficients.l P.extension
    P.level P.level_pos Y
  have hB (K : proEtaleDerivedCategory X P.Ring) : B X K ↔ ∀ i, B (Xi i) ((rd i).obj K) := by
    change (proEtaleCohomologicalSupport K).Finite ∧ _ ↔ _
    constructor
    · intro h i
      exact ⟨(hf K).mp h.1 i, (hc K).mp h.2 i⟩
    · intro h
      exact ⟨(hf K).mpr (fun i ↦ (h i).1), (hc K).mpr (fun i ↦ (h i).2)⟩
  have hT (K : proEtaleDerivedCategory X P.Ring) : T X K ↔ ∀ i, T (Xi i) ((rd i).obj K) := by
    constructor
    · rintro ⟨hb, a, b, htor⟩ i
      exact ⟨(hB K).mp hb i, a, b, (ht K a b htor.1).mp htor i⟩
    · intro h
      refine ⟨(hB K).mpr (fun i ↦ (h i).1), ?_⟩
      choose ai bi hi using fun i ↦ (h i).2
      obtain ⟨a, ha⟩ := (Set.finite_range ai).bddBelow
      obtain ⟨b, hb⟩ := (Set.finite_range bi).bddAbove
      refine ⟨min a b, b, (ht K (min a b) b (min_le_right _ _)).mpr ?_⟩
      intro i
      exact amplitude_mono _ _ (hi i) ((min_le_left _ _).trans (ha ⟨i, rfl⟩)) (hb ⟨i, rfl⟩)
  have Biso (Y : Scheme.{u}) {K L : proEtaleDerivedCategory Y P.Ring}
      (e : K ≅ L) (h : B Y K) : B Y L := by
    constructor
    · have hsupp : proEtaleCohomologicalSupport L = proEtaleCohomologicalSupport K := by
        ext m
        exact not_congr ((DerivedCategory.homologyFunctor _ m).mapIso e).isZero_iff.symm
      change (proEtaleCohomologicalSupport L).Finite
      rw [hsupp]
      exact h.1
    · intro m
      exact constructibleProEtale_of_iso Y P.Ring
        ((DerivedCategory.homologyFunctor _ m).mapIso e) (h.2 m)
  have Tiso (Y : Scheme.{u}) {K L : proEtaleDerivedCategory Y P.Ring}
      (e : K ≅ L) (h : T Y K) : T Y L := by
    obtain ⟨hb, a, b, htor⟩ := h
    exact ⟨Biso Y e hb, a, b, amplitude_iso Y P.Ring e a b htor⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S i
    obtain ⟨hi, hl, hc, hp, hu⟩ := clopenStratification_pullback
      X I Xi j hd hcover (toFinite S) S.isConstructible_stratum i
    let T : Stratification (Xi i) :=
      { n := S.n
        stratum t := Set.range (pullback.snd (S.immersion t) (j i))
        isLocallyClosed_stratum := hl
        isConstructible_stratum := hc
        iUnion_stratum_eq_univ := hu
        pairwise_disjoint_stratum := hp
        domain t := pullback (S.immersion t) (j i)
        immersion t := pullback.snd (S.immersion t) (j i)
        isImmersion := hi
        range_immersion _ := rfl }
    exact ⟨T, Equiv.refl _, fun t ↦ ⟨Iso.refl _, Category.id_comp _⟩⟩
  · intro S
    obtain ⟨hi, hl, hc, hp, hu⟩ := clopenStratification_union
      X I Xi j hd hcover (fun i ↦ toFinite (S i)) (fun i ↦ (S i).isConstructible_stratum)
    let e := (Fintype.equivFin (Σ i, Fin (S i).n)).symm
    let T : Stratification X :=
      { n := Fintype.card (Σ i, Fin (S i).n)
        stratum t := Set.range ((S (e t).1).immersion (e t).2 ≫ j (e t).1)
        isLocallyClosed_stratum t := hl (e t)
        isConstructible_stratum t := hc (e t)
        iUnion_stratum_eq_univ := by
          ext x
          constructor
          · intro _
            trivial
          · intro _
            have hx : x ∈ ⋃ p : (Σ i, Fin (S i).n), Set.range ((S p.1).immersion p.2 ≫ j p.1) := by
              rw [show (⋃ p : (Σ i, Fin (S i).n),
                Set.range ((S p.1).immersion p.2 ≫ j p.1)) = Set.univ from hu]
              trivial
            obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
            obtain ⟨t, rfl⟩ := e.surjective p
            exact Set.mem_iUnion.mpr ⟨t, hp⟩
        pairwise_disjoint_stratum := fun t t' h ↦ hp (e.injective.ne h)
        domain t := (S (e t).1).domain (e t).2
        immersion t := (S (e t).1).immersion (e t).2 ≫ j (e t).1
        isImmersion t := hi (e t)
        range_immersion _ := rfl }
    exact ⟨T, e, fun t ↦ ⟨Iso.refl _, Category.id_comp _⟩⟩
  · intro F
    exact isConstructibleProEtaleModuleSheaf_iff_clopen X I Xi j hd hcover P.Ring F
  · exact hc
  · intro K a b _
    rw [hs]
    exact Set.iUnion_subset_iff
  · exact ht
  · exact restrictProductEquivalence rd ED rfl (B X) (fun i ↦ B (Xi i)) hB
      (fun i {_ _} e h ↦ Biso (Xi i) e h)
  · exact restrictProductEquivalence rd ED rfl (T X) (fun i ↦ T (Xi i)) hT
      (fun i {_ _} e h ↦ Tiso (Xi i) e h)
  · intro K hK a b hab
    constructor
    · intro m hm
      exact False.elim (hm ((DerivedCategory.homologyFunctor _ m).map_isZero hK))
    · refine ⟨hab, ?_⟩
      intro L Q e f hf hQ M m hm
      obtain ⟨F, _, _, hF⟩ := tensor_functor X P.Ring M
      obtain ⟨d⟩ := hF L Q f hf hQ
      have hz := F.map_isZero (hK.of_iso e.some)
      exact (DerivedCategory.homologyFunctor _ m).map_isZero (hz.of_iso d.symm)

end WeilConjectures.PurityFiniteSetting
