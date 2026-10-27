/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ConstructibleAlgClTopologyComparison
public import Sheaf.Paper.CoefficientHeartFiltration
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import Sheaf.Paper.CondensedOpenClosedRecollement

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Paper.SupportedCommonFieldScalarModels
import Sheaf.Paper.FiniteModelTopologyDerivedHom
import Sheaf.Paper.GlobalInternalHomDetection

/-!
# Supported finite-stage local systems and the scalar-unit topology defect

Source: blueprint main-20261015, six-functors direct-image stability proof,
paragraph (3), explicit agent coefficient-topology obligation
(blueprint: lem-sfb-supported-finite-stage-topology-defect).

C is the finite-subextension-valued condensed ring and B is the full norm-continuous
condensed ring. The existing inclusion and derived scalar adjunction are used unchanged.
The supported objects are constructed by exact termwise extension through their closures.
The proof uses common-field supported models and the finite-model global Hom comparison,
then detects the actual scalar unit and applies distinguished-triangle exactness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensorHomAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.internalScalarExtension
  AlgebraicGeometry.ProEtale.CondensedRing.internalScalarTensorIso
  AlgebraicGeometry.ProEtale.FiniteModelTopologyHom.sections
  AlgebraicGeometry.ProEtale.FiniteModelTopologyHom.restrictionSections
  AlgebraicGeometry.ProEtale.FiniteModelTopologyHom.globalize
  AlgebraicGeometry.ProEtale.FiniteModelTopologyHom.restrictionMate
  AlgebraicGeometry.ProEtale.FiniteModelTopologyHom.scalarAdjunction


universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale


private theorem bijective_of_equiv_square {A B C D : Type*}
    (e : A ≃ B) (d : C ≃ D) (f : A → C) (g : B → D)
    (h : ∀ a, d (f a) = g (e a)) (hg : Function.Bijective g) :
    Function.Bijective f := by
  constructor
  · intro a b hab
    apply e.injective
    apply hg.injective
    rw [← h, ← h, hab]
  · intro c
    obtain ⟨b, hb⟩ := hg.surjective (d c)
    refine ⟨e.symm b, d.injective ?_⟩
    rw [h, e.apply_symm_apply, hb]

private theorem triangle_hom_zero
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (G : C)
    (hs : Function.Surjective (fun f : G ⟶ T.obj₁ ↦ f ≫ T.mor₁))
    (hi : Function.Injective (fun f : G ⟶ T.obj₁⟦(1 : ℤ)⟧ ↦
      f ≫ T.mor₁⟦(1 : ℤ)⟧')) : Subsingleton (G ⟶ T.obj₃) := by
  have hz (q : G ⟶ T.obj₃) : q = 0 := by
    have hq : q ≫ T.mor₃ = 0 := by
      apply hi
      simp only [zero_comp]
      rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero]
    obtain ⟨f, hf⟩ := T.coyoneda_exact₃ hT q hq
    obtain ⟨g, hg⟩ := hs f
    rw [hf, ← hg, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

private theorem unitHom_transport
    {C : Type*} [Category C] [HasShift C ℤ] (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    {G H G' H' : C} (e : G ≅ G') (d : H ≅ H') (n : ℤ)
    (h : Function.Bijective (fun f : G' ⟶ H'⟦n⟧ ↦ f ≫ (η.app H')⟦n⟧')) :
    Function.Bijective (fun f : G ⟶ H⟦n⟧ ↦ f ≫ (η.app H)⟦n⟧') := by
  apply bijective_of_equiv_square
    (e.homCongr ((shiftFunctor C n).mapIso d))
    (e.homCongr ((shiftFunctor C n).mapIso (J.mapIso d))) _ _ _ h
  intro f
  simp only [Iso.homCongr_apply, Functor.mapIso_hom]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← η.naturality d.hom]
  rfl

private theorem triangle_shift_hom_zero
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (G : C)
    (h : ∀ n : ℤ, Function.Bijective (fun f : G ⟶ T.obj₁⟦n⟧ ↦
      f ≫ T.mor₁⟦n⟧')) (n : ℤ) : Subsingleton (G ⟶ T.obj₃⟦n⟧) := by
  have hb : Function.Bijective (fun f : G ⟶ T.obj₁⟦n⟧⟦(1 : ℤ)⟧ ↦
      f ≫ (T.mor₁⟦n⟧')⟦(1 : ℤ)⟧') := by
    apply bijective_of_equiv_square
      ((shiftFunctorAdd C n (1 : ℤ)).app T.obj₁).symm.homToEquiv
      ((shiftFunctorAdd C n (1 : ℤ)).app T.obj₂).symm.homToEquiv _ _ _ (h (n + 1))
    intro f
    change (f ≫ (T.mor₁⟦n⟧')⟦(1 : ℤ)⟧') ≫
        (shiftFunctorAdd C n (1 : ℤ)).inv.app T.obj₂ =
      (f ≫ (shiftFunctorAdd C n (1 : ℤ)).inv.app T.obj₁) ≫ T.mor₁⟦n + 1⟧'
    have hn := (shiftFunctorAdd C n (1 : ℤ)).inv.naturality T.mor₁
    simpa only [Functor.comp_map, Category.assoc] using congrArg (fun z ↦ f ≫ z) hn
  apply triangle_hom_zero ((shiftFunctor (Triangle C) n).obj T)
    (Triangle.shift_distinguished T hT n) G
  · change Function.Surjective (fun f : G ⟶ T.obj₁⟦n⟧ ↦
      f ≫ (n.negOnePow • T.mor₁⟦n⟧'))
    simpa only [Function.comp_def, Linear.comp_units_smul] using
      ((MulAction.bijective n.negOnePow).comp (h n)).surjective
  · change Function.Injective (fun f : G ⟶ T.obj₁⟦n⟧⟦(1 : ℤ)⟧ ↦
      f ≫ (n.negOnePow • T.mor₁⟦n⟧')⟦(1 : ℤ)⟧')
    simpa only [Function.comp_def, Functor.map_units_smul, Linear.comp_units_smul] using
      ((MulAction.bijective n.negOnePow).comp hb).injective

private theorem adjointGlobalize_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    (Γ : C ⥤ E) (Γ' : D ⥤ E) (δ : U ⋙ Γ ≅ Γ')
    (V : C) (W Z : D) (f : J.obj V ⟶ W) (g : W ⟶ Z) :
    Γ.map (a.homEquiv V Z (f ≫ g)) ≫ δ.hom.app Z =
      (Γ.map (a.homEquiv V W f) ≫ δ.hom.app W) ≫ Γ'.map g := by
  rw [a.homEquiv_naturality_right, Functor.map_comp]
  have hn := δ.hom.naturality g
  change Γ.map (U.map g) ≫ δ.hom.app Z = δ.hom.app W ≫ Γ'.map g at hn
  simp only [Category.assoc]
  rw [hn]

private theorem adjointGlobalize_isIso_of_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    (Γ : C ⥤ E) (Γ' : D ⥤ E) (δ : U ⋙ Γ ≅ Γ')
    (V : C) (W Z : D) (f : J.obj V ⟶ W) (g : W ⟶ Z) [IsIso g]
    (h : IsIso (Γ.map (a.homEquiv V Z (f ≫ g)) ≫ δ.hom.app Z)) :
    IsIso (Γ.map (a.homEquiv V W f) ≫ δ.hom.app W) := by
  have h' : IsIso ((Γ.map (a.homEquiv V W f) ≫ δ.hom.app W) ≫ Γ'.map g) := by
    rw [← adjointGlobalize_comp a Γ Γ' δ V W Z f g]
    exact h
  letI := h'
  exact IsIso.of_isIso_comp_right _ (Γ'.map g)

private theorem rightUniq_apply
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {U V : D ⥤ C} (a : F ⊣ U) (b : F ⊣ V)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    a.homEquiv X Y f ≫ (a.rightAdjointUniq b).hom.app Y = b.homEquiv X Y f := by
  rw [a.homEquiv_unit, Category.assoc,
    (a.rightAdjointUniq b).hom.naturality f, ← Category.assoc,
    Adjunction.unit_rightAdjointUniq_hom_app, ← b.homEquiv_unit]

private theorem scalarHom_normalization
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    {L R : C ⥤ C} (b : L ⊣ R) {L' R' : D ⥤ D} (b' : L' ⊣ R')
    (μ : L ⋙ J ≅ J ⋙ L') (N : C) :
    a.homEquiv _ _ (b'.homEquiv _ _
      (μ.inv.app (R.obj N) ≫ J.map (b.counit.app N))) ≫
      ((a.comp b').rightAdjointUniq ((b.comp a).ofNatIsoLeft μ)).hom.app (J.obj N) =
        R.map (a.unit.app N) := by
  have he := rightUniq_apply (a.comp b') ((b.comp a).ofNatIsoLeft μ)
    (μ.inv.app (R.obj N) ≫ J.map (b.counit.app N))
  rw [Adjunction.comp_homEquiv] at he
  change a.homEquiv _ _ (b'.homEquiv _ _
    (μ.inv.app (R.obj N) ≫ J.map (b.counit.app N))) ≫ _ = _ at he
  simp only [Functor.id_obj] at he ⊢
  rw [he, Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [Adjunction.comp_homEquiv]
  change b.homEquiv _ _ (a.homEquiv _ _ (J.map (b.counit.app N))) = _
  rw [a.homEquiv_unit]
  have hn := a.unit.naturality (b.counit.app N)
  change b.counit.app N ≫ a.unit.app N =
    a.unit.app (L.obj (R.obj N)) ≫ U.map (J.map (b.counit.app N)) at hn
  rw [← hn]
  change b.homEquiv _ _ (b.counit.app N ≫ a.unit.app N) = _
  rw [b.homEquiv_naturality_right, ← b.homEquiv_symm_id]
  simp only [Functor.id_obj, Equiv.apply_symm_apply, Category.id_comp]

private theorem scalarHom_sections_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    {J : C ⥤ D} {U : D ⥤ C} (a : J ⊣ U)
    {L R : C ⥤ C} (b : L ⊣ R) {L' R' : D ⥤ D} (b' : L' ⊣ R')
    (μ : L ⋙ J ≅ J ⋙ L') (Γ : C ⥤ E) (Γ' : D ⥤ E)
    (δ : U ⋙ Γ ≅ Γ') (N : C)
    (h : IsIso (Γ.map (a.homEquiv _ _ (b'.homEquiv _ _
      (μ.inv.app (R.obj N) ≫ J.map (b.counit.app N)))) ≫
        δ.hom.app (R'.obj (J.obj N)))) :
    IsIso (Γ.map (R.map (a.unit.app N))) := by
  simp only [Functor.id_obj] at h ⊢
  have hm : IsIso (Γ.map (a.homEquiv _ _ (b'.homEquiv _ _
      (μ.inv.app (R.obj N) ≫ J.map (b.counit.app N))))) := by
    apply (isIso_comp_right_iff _ (δ.hom.app _)).mp
    simpa only [Functor.id_obj] using h
  rw [← scalarHom_normalization a b b' μ N, Functor.map_comp]
  simp only [Functor.id_obj] at hm ⊢
  letI := hm
  apply (isIso_comp_right_iff _
    (Γ.map (((a.comp b').rightAdjointUniq ((b.comp a).ofNatIsoLeft μ)).hom.app
      (J.obj N)))).mpr
  exact hm

private theorem unitHom_bijective_of_globalHom_isIso
    (X : Scheme.{u})
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (c : Λ ⟶ Λ') [IsMonHom c]
    (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : IsIso (FiniteModelTopologyHom.globalize X c _ _
      (FiniteModelTopologyHom.homComparison X c K N))) (n : ℤ) :
    Function.Bijective (fun f : K ⟶ N⟦n⟧ ↦
      f ≫ ((FiniteModelTopologyHom.scalarAdjunction X c).unit.app N)⟦n⟧') := by
  let η := (FiniteModelTopologyHom.scalarAdjunction X c).unit.app N
  have hd : IsIso ((FiniteModelTopologyHom.sections X (condensedRingObj Λ X)).map
      (((CondensedRing.derivedHom Λ X).obj (op K)).map η)) := by
    apply scalarHom_sections_isIso (FiniteModelTopologyHom.scalarAdjunction X c)
      (CondensedRing.derivedTensorHomAdjunction Λ K)
      (CondensedRing.derivedTensorHomAdjunction Λ'
        ((CondensedRing.internalScalarExtension c X).obj K))
      ((CondensedRing.internalScalarTensorIso c X).app K)
      (FiniteModelTopologyHom.sections X (condensedRingObj Λ X))
      (FiniteModelTopologyHom.sections X (condensedRingObj Λ' X))
      (FiniteModelTopologyHom.restrictionSections X (coefficientMap c X)) N
    simpa only [FiniteModelTopologyHom.globalize, FiniteModelTopologyHom.restrictionMate,
      FiniteModelTopologyHom.homComparison, Functor.id_obj, Iso.app_inv] using h
  exact FiniteModelTopologyHom.shiftedHom_bijective_of_globalInternalHom_isIso X Λ K η hd n



private theorem unitHom_bijective_of_globalHom_comp_isIso
    (X : Scheme.{u})
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (c : Λ ⟶ Λ') [IsMonHom c]
    (K N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {Z : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))}
    (t : ((CondensedRing.derivedHom Λ' X).obj
      (op ((CondensedRing.internalScalarExtension c X).obj K))).obj
        ((CondensedRing.internalScalarExtension c X).obj N) ⟶ Z) [IsIso t]
    (h : IsIso (FiniteModelTopologyHom.globalize X c _ _
      (FiniteModelTopologyHom.homComparison X c K N ≫ t))) (n : ℤ) :
    Function.Bijective (fun f : K ⟶ N⟦n⟧ ↦
      f ≫ ((FiniteModelTopologyHom.scalarAdjunction X c).unit.app N)⟦n⟧') := by
  have hg : IsIso (FiniteModelTopologyHom.globalize X c _ _
      (FiniteModelTopologyHom.homComparison X c K N)) := by
    simp only [FiniteModelTopologyHom.globalize, FiniteModelTopologyHom.restrictionMate]
      at h ⊢
    exact adjointGlobalize_isIso_of_comp (FiniteModelTopologyHom.scalarAdjunction X c)
      (FiniteModelTopologyHom.sections X (condensedRingObj Λ X))
      (FiniteModelTopologyHom.sections X (condensedRingObj Λ' X))
      (FiniteModelTopologyHom.restrictionSections X (coefficientMap c X)) _ _ _ _ t h
  exact unitHom_bijective_of_globalHom_isIso X c K N hg n

set_option backward.isDefEq.respectTransparency false
attribute [local semireducible] CondensedRing.internalScalarExtension
  CondensedRing.internalScalarTensorIso FiniteModelTopologyHom.scalarAdjunction
attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction

/-- The specified object a_!(C_S tensor^L_{A_E,S} L[0]), using the canonical
scheme-theoretic closure factorization already defining
`coefficientHeartLocallyClosedExtension`. No lisse hypothesis is needed to construct it.
Source: blueprint direct-image stability proof (3), supported finite-stage
scalar-unit defect obligation, displayed definition of G (and independently H)
(blueprint: lem-sfb-supported-finite-stage-topology-defect).

Finite type over the field supplies the Noetherian structures by the recorded Mathlib
lemmas. Exactness of the closed factor is the proof-irrelevant witness in the recorded
recollement theorem. Only that property is selected, never a functor or an object.
The exact composite is localized termwise using `mapDerivedCategory`, after applying
the existing K-flat derived scalar extension to the degree-zero complex. -/
def supportedFiniteStageTopologyObject (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {S : Scheme.{u}} (a : S ⟶ X.left) (ha : IsImmersion a)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :=
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := ⟨⟩
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  letI : PreservesFiniteColimits
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι) :=
    (CondensedRing.condensed_open_closed_recollement (Profinite.padicAlgClRingObj ℓ)
      a.imageι (Scheme.openComplementOfIsClosedImmersion a.imageι).ι
      (Scheme.Opens.range_ι _)).choose
  letI : PreservesFiniteLimits
      (coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ) a ha) :=
    inferInstanceAs (PreservesFiniteLimits
      (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) a.toImage ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι))
  letI : PreservesFiniteColimits
      (coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ) a ha) :=
    inferInstanceAs (PreservesFiniteColimits
      (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) a.toImage ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι))
  letI : (coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ) a ha).Additive :=
    Functor.additive_of_preserves_binary_products _
  ((coefficientHeartLocallyClosedExtension (Profinite.padicAlgClRingObj ℓ)
    a ha).mapDerivedCategory).obj
      (((Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) S)
          ).leftDerivedFunctor).obj ((DerivedCategory.singleFunctor _ 0).obj L))

/-- Two independently supported finite-stage lisse modules are left orthogonal to
every shift of every cone of the specified derived scalar adjunction unit.
`Subsingleton` says precisely that the Hom group is zero: its existing zero morphism
supplies an element. The algebraic closure is the fixed model `PadicAlgCl` used by the
recorded coefficient definitions, with its extended ell-adic norm.

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
agent supported finite-stage scalar-unit defect obligation
(blueprint: lem-sfb-supported-finite-stage-topology-defect).

Proof:
1. Apply supported_common_field_scalar_models to the independent supports and finite
fields. It produces bounded constructible K,N over the finite compositum E F and
canonical isomorphisms from the two supported objects to their C-scalar extensions.
The termwise exact composite comparison identifies the displayed supported objects
with those used in that model theorem.
2. finiteModelTopologyDerivedHom makes the actual globalHomComparison invertible.
Its final reassociation acts on internal Hom by an isomorphism; naturality of
restrictionSections permits cancelling that isomorphism after globalization.
3. Uniqueness of right adjoints identifies the restriction mate of the scalar
Hom comparison, followed by the canonical scalar-Hom isomorphism, with internal
Hom applied to the actual unit. GlobalInternalHomDetection gives bijectivity of
postcomposition with every shifted unit. Naturality of the unit transports this
through the supported-object isomorphisms, without identifying their supports.
4. Shift the specified distinguished triangle. Its first arrow is the shifted unit
multiplied by the invertible sign (-1)^n. Surjectivity on Hom at this arrow and
injectivity at its shift by one force every map into the third object to vanish:
its boundary is zero by injectivity; exactness factors it through the second
arrow; surjectivity then factors it through the composite of the first two,
which is zero. This proves Subsingleton for the arbitrary given cone and n. -/
theorem supported_finiteStage_topology_defect
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (S T : Scheme.{u}) (a : S ⟶ X.left) (ha : IsImmersion a)
    (haCons : Topology.IsConstructible (Set.range a))
    (b : T ⟶ X.left) (hb : IsImmersion b)
    (hbCons : Topology.IsConstructible (Set.range b))
    (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) S))
    (hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj F) T))
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj F) M)
    (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (v : ((Mod.comap (coefficientMap (algClTopologyInclusion ℓ) X.left)).mapDerivedCategory).obj
          ((algClTopologyScalarExtension ℓ X.left).obj
            (supportedFiniteStageTopologyObject ℓ X b hb F M)) ⟶ Q)
    (w : Q ⟶ (supportedFiniteStageTopologyObject ℓ X b hb F M)⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (algClTopologyInclusion ℓ) X.left)).unit.app
          (supportedFiniteStageTopologyObject ℓ X b hb F M)) v w ∈ distTriang _)
    (n : ℤ) :
    Subsingleton (supportedFiniteStageTopologyObject ℓ X a ha E L ⟶ Q⟦n⟧) := by
  letI : IsImmersion a := ha
  letI : IsImmersion b := hb
  obtain ⟨hX, hmodels⟩ :=
    SupportedCommonField.supported_common_field_scalar_models ℓ p k hp hpℓ
      X S T a haCons b hbCons E F L hL M hM
  letI := hX
  obtain ⟨hS, hmodels⟩ := hmodels
  letI := hS
  obtain ⟨hT, hmodels⟩ := hmodels
  letI := hT
  have hLmodel := hmodels.2.2.2.2.2.1
  have hMmodel := hmodels.2.2.2.2.2.2
  obtain ⟨_, hK, hSingleL, dL, _, _, _, _, _, _⟩ := hLmodel
  obtain ⟨_, hN, hSingleM, dM, _, _, _, _, _, _⟩ := hMmodel
  letI := hSingleL
  letI := hSingleM
  let A := SupportedCommonField.commonField ℓ E F
  have hEA : E ≤ A := (show E.1 ≤ E.1 ⊔ F.1 from le_sup_left)
  have hFA : F ≤ A := (show F.1 ≤ E.1 ⊔ F.1 from le_sup_right)
  let K := SupportedCommonField.finiteModel ℓ hEA a L
  let N := SupportedCommonField.finiteModel ℓ hFA b M
  let eG : supportedFiniteStageTopologyObject ℓ X a ha E L ≅
      (FiniteModelTopologyHom.toUnion X.left ℓ A).obj K :=
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) a.toImage)
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) a.imageι)).app _ ≪≫
        SupportedCommonField.alpha ℓ hEA a L dL
  let eH : supportedFiniteStageTopologyObject ℓ X b hb F M ≅
      (FiniteModelTopologyHom.toUnion X.left ℓ A).obj N :=
    (Functor.mapDerivedCategoryCompIso
      (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) b.toImage)
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) b.imageι)).app _ ≪≫
        SupportedCommonField.alpha ℓ hFA b M dM
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (algClTopologyInclusion ℓ) X.left)
  have hu (m : ℤ) : Function.Bijective
      (fun f : supportedFiniteStageTopologyObject ℓ X a ha E L ⟶
          (supportedFiniteStageTopologyObject ℓ X b hb F M)⟦m⟧ ↦
        f ≫ (adj.unit.app (supportedFiniteStageTopologyObject ℓ X b hb F M))⟦m⟧') := by
    apply unitHom_transport _ adj.unit eG eH m
    haveI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k (Nat.ne_of_gt hp)⟩
    have hall := FiniteModelTopologyHom.finiteModelTopologyDerivedHom X.left ℓ A K N
      (k := k) p hpℓ X.hom hK hN
    have hg := hall.2.2.2.2.2.2.2.2
    let c := algClTopologyInclusion ℓ
    let G := (FiniteModelTopologyHom.toUnion X.left ℓ A).obj K
    let H := (FiniteModelTopologyHom.toUnion X.left ℓ A).obj N
    let t := FiniteModelTopologyHom.homArrow X.left
      (Profinite.continuousMapRingObj (PadicAlgCl ℓ))
      ((FiniteModelTopologyHom.reassociation X.left ℓ A).inv.app K)
      ((FiniteModelTopologyHom.reassociation X.left ℓ A).hom.app N)
    have ht : IsIso t := by
      dsimp only [t, FiniteModelTopologyHom.homArrow]
      infer_instance
    letI := ht
    exact unitHom_bijective_of_globalHom_comp_isIso X.left c G H t hg m
  exact triangle_shift_hom_zero _ htriangle _ hu n

end AlgebraicGeometry.ProEtale
